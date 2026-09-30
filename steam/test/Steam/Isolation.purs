-- | What a guest keeps between attempts, and what the host makes of it.
-- |
-- | **A retry is a new invocation**: it asks from its beginning, as the attempt
-- | that waited did, and holds nothing that attempt held on its stack. **A guest's
-- | heap is not rolled back**, though, so a guest can keep a value where an array a
-- | module created at load holds it — out of contract, and exactly what the host's
-- | checks are for. `Stash.caching` keeps the handle of its goal's type in such an
-- | array where it waits, and presents what the array holds when it is run where it
-- | does not wait: a handle a rollback took back is refused as stale, and one another
-- | compiler session issued as foreign.
module Test.Steam.Isolation (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff, Milliseconds(..))
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Node.Buffer as Buffer
import Node.FS.Aff as FS
import Node.FS.Perms as Perms
import Stella.CLI.Session.Broker (SessionHealth(..), newCancellation)
import Stella.CLI.Session.Broker.Attempter (Guests, runGuests, submitGuest, submitGuestSynthesis)
import Stella.CLI.Session.Client (Session)
import Stella.CLI.Session.Client as Client
import Stella.Compiler.Bytecode (encode)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), emptyXContext)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.CorePlus.Type (XType(..))
import Stella.Compiler.Elaborate.Driver.Attempt (Attempt(Committed, Registered))
import Stella.Compiler.Elaborate.Driver.Loop (RunResult(..), Submission(..))
import Stella.Compiler.Elaborate.Environment.Catalog (catalogOf)
import Stella.Compiler.Elaborate.Environment.Constructors (constructorsOf)
import Stella.Compiler.Elaborate.Environment.Effects (effectsOf)
import Stella.Compiler.Elaborate.Kernel.Elab (Outcome(..), SessionEnv, freshTypeMeta, initialState, runElabIn)
import Stella.Compiler.Elaborate.Mechanism.Kinding (kindingOf)
import Stella.Compiler.Elaborate.Mechanism.Pending (Job(..), Site)
import Stella.Compiler.Elaborate.Protocol.Guest (bundle, elabModule, kernelEffect)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..))
import Stella.Compiler.Elaborate.Vocabulary.Handle (HandleError(..), SessionId(..))
import Stella.Compiler.Elaborate.Vocabulary.Trace (TraceEvent(..), Tracing(..), canonicalCommands, commandsOf)
import Stella.Compiler.TypedCore (CanonicalClass(..), DecisionTree(..), Decl(..), Export(..), Expr(..), Ident(..), Kind(..), Literal(..), Module, ModuleName(..), Occurrence(..), Qualified(..), RowEntry(..), TyConInfo(..), TyName(..), TyVar(..), Type(..), monoScheme)
import Stella.Compiler.TypedCore.Prim (fn, intTy, primSignature, pureFn, unitTy)
import Stella.Compiler.TypedCore.Signature (Signature)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Steam.Command (dir, pathOf)
import Test.Steam.Guest (call, compileGuestsOver, construct, elab, elabRow, elabT, global, handleT, text, widened)
import Test.Steam.InProcess (openInProcess)
import Test.Steam.Session (close', hello, node)

-- `Base.Array` ----------------------------------------------------------------------------------

arrayModuleName :: ModuleName
arrayModuleName = ModuleName "Base.Array"

arrayTy :: Qualified TyName
arrayTy = Qualified arrayModuleName (TyName "Array")

arrayOf :: Type -> Type
arrayOf = TApp (TCon arrayTy [])

-- | What the ABI manifest supplies to `Base.Array`: the type constructor, opaque.
withArray :: Signature -> Signature
withArray sig = sig
  { types = Map.insert arrayTy (IntrinsicTyCon (monoScheme (KFun KType KType)) CanonicalOpaque) sig.types }

-- | `Base.Array`, the three entries a stash needs, which the interpreter carries out.
arrayModule :: Module Unit
arrayModule =
  { annotation: unit
  , name: arrayModuleName
  , imports: []
  , exports: map (ExportValue <<< Ident) [ "unsafeNew", "unsafeSet", "unsafeIndex" ]
  , decls:
      [ foreign' "unsafeNew" (pureFn int (arrayOf a))
      , foreign' "unsafeSet" (pureFn int (pureFn a (pureFn (arrayOf a) (TCon unitTy []))))
      , foreign' "unsafeIndex" (pureFn (arrayOf a) (pureFn int a))
      ]
  }
  where
  a = TVar (TyVar "a")
  int = TCon intTy []
  foreign' name body = DeclForeign unit { name: Ident name, scheme: monoScheme (TForall (TyVar "a") KType body), attributes: [] }

entry :: P.String -> Expr Unit
entry name = TyApp unit (Global unit (Qualified arrayModuleName (Ident name)) []) handleT

-- `Stash` -----------------------------------------------------------------------------------------

stashModuleName :: ModuleName
stashModuleName = ModuleName "Stash"

caching :: Qualified Ident
caching = Qualified stashModuleName (Ident "caching")

-- | `box`, an array of one handle, created where the module loads; and `caching`,
-- | which keeps its goal's type there where it waits, and presents what is there
-- | where it does not.
stashModule :: Module Unit
stashModule =
  { annotation: unit
  , name: stashModuleName
  , imports: [ elabModule, arrayModuleName ]
  , exports: []
  , decls:
      [ DeclNonRec unit
          { name: Ident "box"
          , scheme: monoScheme (arrayOf handleT)
          , value: App unit (entry "unsafeNew") (Lit unit (LitInt 1))
          , attributes: []
          }
      , DeclNonRec unit
          { name: Ident "caching"
          , scheme: monoScheme (fn handleT (TRowExtend (RowEffectEntry kernelEffect []) TRowEmpty) handleT)
          , value: App unit (global "synthesizer") (Lam unit (Ident "goal") handleT policy)
          , attributes: []
          }
      ]
  }
  where
  box = Global unit (Qualified stashModuleName (Ident "box")) []
  applied f = Array.foldl (\g x -> App unit (widened elabRow g) x) f
  var n = Var unit (Ident n)

  policy =
    Let unit (Ident "goalType") handleT (call (global "goalType") [ var "goal" ])
      $ Case unit [ call (global "viewType") [ var "goalType" ] ]
          ( SwitchCtor (OccScrutinee 0)
              [ { ctor: elab "MetaType"
                , tree: Bind (Ident "waited") (OccField (OccScrutinee 0) (elab "MetaType") 0) $ Leaf $
                    Let unit (Ident "kept") (TCon unitTy []) (applied (entry "unsafeSet") [ Lit unit (LitInt 0), var "goalType", box ])
                      (call (TyApp unit (global "postpone") handleT) [ listOfHandles [ var "waited" ] ])
                }
              ]
              ( Just $ Leaf
                  $ Let unit (Ident "presented") handleT (applied (entry "unsafeIndex") [ box, Lit unit (LitInt 0) ])
                  $ Let unit (Ident "seen") (elabT "TypeView") (call (global "viewType") [ var "presented" ])
                  $ call (TyApp unit (global "throw") handleT)
                      [ listOfParts [ construct elabRow "TextPart" [] [ text "the kept handle was taken" ] ] ]
              )
          )

  listOfHandles xs = Array.foldr (\x rest -> construct elabRow "Cons" [ handleT ] [ x, rest ]) (TyApp unit (global "Nil") handleT) xs
  listOfParts xs = Array.foldr (\x rest -> construct elabRow "Cons" [ elabT "MessagePart" ] [ x, rest ]) (TyApp unit (global "Nil") (elabT "MessagePart")) xs

-- The compiler's side ---------------------------------------------------------------------------

env :: SessionEnv
env =
  { catalog: catalogOf []
  , kinding: kindingOf primSignature
  , constructors: constructorsOf primSignature
  , effects: effectsOf primSignature
  , tracing: TraceEnabled
  }

site :: Site
site = { context: emptyXContext, origin: InDeclaration (Qualified (ModuleName "Main") (Ident "answer")) }

xInt :: XType
xInt = XCon intTy []

-- | What runs a compilation's goals on the session, the attempt numbers drawn from
-- | the session's one supply.
guestsOn :: Session -> Ref P.Int -> Aff Guests
guestsOn session attempts = case bundle of
  Left err -> liftEffect (throw ("no bundle: " <> err))
  Right trusted -> liftEffect do
    cancellation <- newCancellation (Milliseconds 1000.0)
    health <- Ref.new Reusable
    pure { session, descriptor: trusted.descriptor, env, budget: 1_000_000, cancellation, attempts, health }

-- | A session served in this process that has loaded `Base.Array` and `Stash`.
withStash :: (Session -> Aff Unit) -> Aff Unit
withStash k = case compileGuestsOver withArray [ arrayModule, stashModule ] of
  Left err -> fail ("the stash did not compile: " <> err)
  Right [ array, stash ] -> do
    FS.mkdir' dir { recursive: true, mode: Perms.mkPerms Perms.all Perms.all Perms.all }
    write "BaseArrayStash" array
    write "Stash" stash
    openInProcess 10_000 (hello { offers = [ "modules", "invoke", "kernel" ] }) >>= case _ of
      Left failure -> fail ("the session did not open: " <> show failure)
      Right session -> do
        node (Client.load session (pathOf "BaseArrayStash")) >>= shouldEqual (Right (Right "Base.Array"))
        node (Client.load session (pathOf "Stash")) >>= shouldEqual (Right (Right "Stash"))
        k session
        close' session >>= shouldEqual (Right unit)
  Right other -> fail ("expected two modules, got " <> show (Array.length other))
  where
  write name dmo = case encode dmo of
    Left err -> fail ("could not encode " <> name <> ": " <> show err)
    Right bytes -> liftEffect (Buffer.fromArray bytes) >>= FS.writeFile (pathOf name)

-- The cases ---------------------------------------------------------------------------------------

spec :: Spec Unit
spec = describe "what a guest keeps between attempts" do
  it "retries as a new invocation from its beginning, and a handle it kept from the attempt that waited is stale" do
    withStash \session -> do
      attempts <- liftEffect (Ref.new 0)
      guests <- guestsOn session attempts
      case runElabIn env (initialState (SessionId 0) 10) (freshTypeMeta emptyXContext XKType) of
        Tuple (Done a@(XMeta _)) s0 -> node (submitGuestSynthesis guests site a caching Nothing s0) >>= case _ of
          Right (Tuple { submission: Continue { attempt: Registered _ } } s1) ->
            node (submitGuest guests site (JobUnify { kind: XKType, left: a, right: xInt }) s1) >>= case _ of
              Right (Tuple (Continue { attempt: Committed }) s2) -> node (runGuests guests s2) >>= case _ of
                Right (Tuple report s3) -> do
                  case report.result of
                    Halted (InvalidHandle _ StaleHandle) -> pure unit
                    other -> fail ("the kept handle was not refused as stale: " <> show other)
                  liftEffect (Ref.read attempts) >>= shouldEqual 2
                  -- the retry asked what the attempt that waited asked, from the start,
                  -- until the goal's type showed what the host had since learned
                  case conversationsIn s3.retained.trace of
                    [ waited, retried ] -> do
                      let
                        first = canonicalCommands (commandsOf waited s3.retained.trace)
                        second = canonicalCommands (commandsOf retried s3.retained.trace)
                      Array.take 2 second `shouldEqual` Array.take 2 first
                      Array.length second `shouldEqual` 3
                    other -> fail ("expected two conversations: " <> show other)
                Left _ -> fail "the run was called off"
              _ -> fail "the equation did not commit"
          _ -> fail "the goal did not wait"
        _ -> fail "no metavariable"

  it "refuses a handle kept from another compiler session as foreign, the attempt numbers going on" do
    withStash \session -> do
      attempts <- liftEffect (Ref.new 0)
      earlier <- guestsOn session attempts
      -- a compilation whose goal waits, which leaves its goal's type in the array
      case runElabIn env (initialState (SessionId 0) 10) (freshTypeMeta emptyXContext XKType) of
        Tuple (Done a) s0 -> node (submitGuestSynthesis earlier site a caching Nothing s0) >>= case _ of
          Right (Tuple { submission: Continue { attempt: Registered _ } } _) -> pure unit
          _ -> fail "the goal did not wait"
        _ -> fail "no metavariable"
      -- another, of another session of the compiler, on the same Steam session
      later <- guestsOn session attempts
      node (submitGuestSynthesis later site xInt caching Nothing (initialState (SessionId 1) 10)) >>= case _ of
        Right (Tuple { submission: Stop report } _) -> case report.result of
          Halted (InvalidHandle _ ForeignHandle) -> pure unit
          other -> fail ("the kept handle was not refused as foreign: " <> show other)
        _ -> fail "the submission did not stop"
      liftEffect (Ref.read attempts) >>= shouldEqual 2
  where
  conversationsIn = Array.mapMaybe case _ of
    AttemptOpened e -> Just e.conversation
    _ -> Nothing
