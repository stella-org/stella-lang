-- | A machine to run guests on with the answers a test gives.
-- |
-- | A guest runs on a store holding `Stella.Elab` installed as a session installs
-- | it, standing on the root boundary of `Kernel.command`; each command it asks is
-- | read back as a generic value, and each answer the test gives is brought into the
-- | machine as the session brings one. The guests are built from source against the
-- | `Stella.Elab` the compiler carries; `machineWith` installs `Stella.Elab`, and is
-- | given the modules the guests reach but it.
module Test.E2E.Guest
  ( elabInterface
  , Machine
  , machineWith
  , Ran(..)
  , runGuest
  , goalToken
  , token
  , wire
  , wireList
  , wireText
  ) where

import Prelude

import Prim as P

import Data.Argonaut.Core (fromString)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldr)
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
import Stella.Compiler.Bytecode (Dmo)
import Stella.Compiler.Elaborate.Protocol.Guest (elabModule)
import Stella.Compiler.Interface.Module (ModuleInterface)
import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.TypedCore (Ident(..), Qualified(..))
import Stella.Compiler.TypedCore.Domain (scalarString)

-- The interface ------------------------------------------------------------------------------

-- | The interface of the `Stella.Elab` the compiler carries.
elabInterface :: Either P.String ModuleInterface
elabInterface = compiled >>= \c -> case Array.find (\i -> i.name == elabModule) c.moduleInterfaces of
  Just i -> Right i
  Nothing -> Left "the compiler carries no Stella.Elab"

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

-- Generic values ---------------------------------------------------------------------------

elab :: P.String -> Qualified Ident
elab = Qualified elabModule <<< Ident

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
