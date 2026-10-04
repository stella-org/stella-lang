-- | Guests written in Typed Core against `Stella.Elab`, and a machine to run them
-- | on with the answers a test gives.
-- |
-- | A guest is compiled as the trusted module is — declared, translated, and
-- | lowered — against the signature `Stella.Elab` declares. It runs on a store
-- | holding `Stella.Elab` installed as a session installs it, standing on the root
-- | boundary of `Kernel.command`; each command it asks is read back as a generic
-- | value, and each answer the test gives is brought into the machine as the
-- | session brings one.
module Test.Steam.Guest
  ( compileGuest
  , compileGuests
  , compileGuestsOver
  , Machine
  , machineWith
  , Ran(..)
  , runGuest
  , goalToken
  , token
  , handleT
  , elabT
  , elabRow
  , elab
  , global
  , construct
  , widened
  , call
  , text
  , unitValue
  , listOf
  , wire
  , wireList
  , wireText
  ) where

import Prelude

import Prim as P

import Data.Argonaut.Core (fromString)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl, foldr)
import Data.Maybe (Maybe(..), fromJust)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Effect.Ref as Ref
import Foreign.Object as Object
import Partial.Unsafe (unsafePartial)
import Run (runBaseEffect)
import Run.Except as Except
import Steam.CLI.Elaboration (install, prepare)
import Steam.CLI.Token as Token
import Steam.CLI.Wire (Unencodable(..), fromWire, toWire)
import Steam.Eval (Outcome(..), Slice, invoke, resumeWith)
import Steam.Foreign (emptyTable)
import Steam.Load (Store, emptyStore, globalNamed, load, namesOf, noIdentities, registryOf)
import Steam.Value (Root, Value(..))
import Stella.CLI.Session.Guest (Token)
import Stella.CLI.Session.Value (WireValue(..), renderPath)
import Stella.Compiler.Bytecode (Dmo, lower)
import Stella.Compiler.Elaborate.Protocol.Guest (elabModule, guestModule, handleTy, withGuest)
import Stella.Compiler.Elaborate.Protocol.Guest as Guest
import Stella.Compiler.Interface (importsOf, aritiesOf, noImports)
import Stella.Compiler.MiddleEnd (translate)
import Stella.Compiler.TypedCore (Expr(..), Ident(..), Literal(..), Module, Qualified(..), TyName(..), Type(..), declareAnnotated, primSignature)
import Stella.Compiler.TypedCore.Domain (scalarString)
import Stella.Compiler.TypedCore.Prim (unitCtor)
import Stella.Compiler.TypedCore.Signature (Signature)

-- Compiling --------------------------------------------------------------------------------

-- | A guest module compiled against `Stella.Elab`.
compileGuest :: Module Unit -> Either P.String Dmo
compileGuest m = compileGuests [ m ] >>= \dmos -> case Array.last dmos of
  Just dmo -> Right dmo
  Nothing -> Left "nothing was compiled"

-- | Modules compiled in order against `Stella.Elab`, each against what the ones
-- | before it declare.
compileGuests :: P.Array (Module Unit) -> Either P.String (P.Array Dmo)
compileGuests = compileGuestsOver identity

-- | `compileGuests`, the signature first given what the function adds to it: a
-- | type an ABI manifest supplies, which no declaration does.
compileGuestsOver :: (Signature -> Signature) -> P.Array (Module Unit) -> Either P.String (P.Array Dmo)
compileGuestsOver supplied modules = do
  elabDeclared <- declared (supplied (withGuest primSignature)) guestModule
  elabMid <- translated noImports guestModule elabDeclared
  compiled <- Array.foldM step
    { signature: elabDeclared.signature, interfaces: [ { name: elabMid.module.name, imports: elabMid.module.imports, arities: aritiesOf elabMid.module } ], dmos: [] }
    modules
  pure compiled.dmos
  where
  step acc m = do
    imports <- case importsOf acc.interfaces of
      Left err -> Left (show err)
      Right imports -> Right imports
    d <- declared acc.signature m
    mid <- translated imports m d
    out <- case lower mid of
      Left err -> Left (show m.name <> " does not lower: " <> show err)
      Right out -> Right out
    pure
      { signature: d.signature
      , interfaces: Array.snoc acc.interfaces ({ name: mid.module.name, imports: mid.module.imports, arities: aritiesOf mid.module })
      , dmos: Array.snoc acc.dmos out.dmo
      }

  declared signature m = case declareAnnotated signature m of
    Left err -> Left (show m.name <> " does not declare: " <> show err.error)
    Right d -> Right d

  translated imports m d = case translate imports m d of
    Left err -> Left (show m.name <> " does not translate: " <> show err)
    Right mid -> Right mid

-- Running ----------------------------------------------------------------------------------

-- | A store holding `Stella.Elab` and the guests given, and the root boundary.
type Machine = { store :: Store, root :: Root }

machineWith :: P.Array Dmo -> Aff Machine
machineWith guests = liftEffect case prepare of
  Left err -> throw ("Stella.Elab is not ready: " <> err)
  Right elaboration -> do
    store <- emptyStore emptyTable <$> Ref.new noIdentities
    runBaseEffect (install elaboration store) >>= case _ of
      Left err -> throw ("Stella.Elab did not install: " <> err)
      Right opened -> do
        loaded <- runBaseEffect (Except.runExcept (Array.foldM (\s dmo -> load s dmo) opened.store guests))
        case loaded of
          Left err -> throw ("a guest did not load: " <> show err)
          Right s -> pure { store: s, root: opened.root }

-- | How a run ended: the commands the guest asked, in order, and what it returned or
-- | why it stopped.
data Ran
  = Returned (P.Array WireValue) WireValue
  -- | The guest asked a command no answer was given for.
  | Unanswered (P.Array WireValue)
  | Stopped (P.Array WireValue) P.String

derive instance Eq Ran

instance Show Ran where
  show = case _ of
    Returned asked value -> "Returned " <> show asked <> " " <> show value
    Unanswered asked -> "Unanswered " <> show asked
    Stopped asked why -> "Stopped " <> show asked <> " " <> why

-- | Apply the global named to the tokens given, and answer the commands it asks with
-- | the answers given, in order.
runGuest :: Machine -> Qualified Ident -> P.Array Token -> P.Array WireValue -> Aff Ran
runGuest machine name arguments answers = liftEffect case globalNamed machine.store name of
  Nothing -> pure (Stopped [] ("no global " <> show name))
  Just slot -> Ref.read slot >>= case _ of
    Nothing -> pure (Stopped [] ("the global " <> show name <> " holds nothing"))
    Just callee -> do
      slice <- runBaseEffect (Except.runExcept (invoke (registryOf machine.store) machine.root budget callee (map (VOpaque <<< Token.wrap) arguments)))
      continue [] answers slice
  where
  budget = 1_000_000

  continue asked remaining = case _ of
    Left failure -> pure (Stopped asked (show failure))
    Right (slice :: Slice) -> case slice.outcome of
      Done value -> do
        names <- namesOf machine.store
        pure case toWire machine.store names value of
          Left why -> Stopped asked ("the result does not read: " <> unencodable why)
          Right result -> Returned asked result
      Paused _ -> pure (Stopped asked "the guest took more steps than the budget")
      Halted _ -> pure (Stopped asked "the guest performed an effect nothing answered")
      Asked argument suspension -> do
        names <- namesOf machine.store
        case toWire machine.store names argument of
          Left why -> pure (Stopped asked ("the command does not read: " <> unencodable why))
          Right command -> do
            let asked' = Array.snoc asked command
            case Array.uncons remaining of
              Nothing -> pure (Unanswered asked')
              Just { head, tail } -> fromWire machine.store head >>= case _ of
                Left problem -> pure (Stopped asked' ("the answer does not read at " <> renderPath problem.path <> ": " <> problem.problem))
                Right answer -> runBaseEffect (Except.runExcept (resumeWith budget suspension answer)) >>= continue asked' tail

-- | The token a guest is given as its goal.
goalToken :: Token
goalToken = token "goal"

token :: P.String -> Token
token t = Object.singleton "handle" (fromString t)

-- Writing guests -----------------------------------------------------------------------------

handleT :: Type
handleT = TCon handleTy []

elabT :: P.String -> Type
elabT n = TCon (Qualified elabModule (TyName n)) []

elabRow :: Type
elabRow = Guest.elabRow

elab :: P.String -> Qualified Ident
elab = Qualified elabModule <<< Ident

-- | A global of `Stella.Elab`, by its name.
global :: P.String -> Expr Unit
global n = Global unit (elab n) []

-- | A constructor of `Stella.Elab` at the type arguments given, applied to the
-- | arguments given where the ambient row is the one given, each arrow widened into
-- | it (D8).
construct :: Type -> P.String -> P.Array Type -> P.Array (Expr Unit) -> Expr Unit
construct row c tyArgs = foldl (\f x -> App unit (widened row f) x)
  (foldl (TyApp unit) (global c) tyArgs)

-- | A function of the facade's shape — every arrow pure but the last, which is at
-- | the facade's row — applied at that row to the arguments given.
call :: Expr Unit -> P.Array (Expr Unit) -> Expr Unit
call f arguments = case Array.unsnoc arguments of
  Nothing -> f
  Just { init, last } -> App unit (foldl (\g x -> App unit (OpenEff unit elabRow g) x) f init) last

text :: P.String -> Expr Unit
text s = Lit unit (LitString (unsafePartial (fromJust (scalarString s))))

unitValue :: Expr Unit
unitValue = Global unit unitCtor []

-- | A `List` of the type given, at the facade's row.
listOf :: Type -> P.Array (Expr Unit) -> Expr Unit
listOf t = foldr (\x rest -> construct elabRow "Cons" [ t ] [ x, rest ]) (TyApp unit (global "Nil") t)

-- | A constructor of `Stella.Elab` as a generic value.
wire :: P.String -> P.Array WireValue -> WireValue
wire c = WData (elab c)

wireList :: P.Array WireValue -> WireValue
wireList = foldr (\x rest -> wire "Cons" [ x, rest ]) (wire "Nil" [])

wireText :: P.String -> WireValue
wireText s = WString (unsafePartial (fromJust (scalarString s)))

unencodable :: Unencodable -> P.String
unencodable = case _ of
  NotEncodable class' -> "a value of the class " <> show class'
  Unaccounted why -> why

-- | A function widened into the row given, which a pure row leaves as it is.
widened :: Type -> Expr Unit -> Expr Unit
widened row f = case row of
  TRowEmpty -> f
  _ -> OpenEff unit row f
