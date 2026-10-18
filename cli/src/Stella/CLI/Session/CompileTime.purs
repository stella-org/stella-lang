-- | What a build's compile-time execution shares: the session its macros'
-- | parsers and its synthesizers run on, the modules of the build loaded into
-- | it, and how that execution fails.
-- |
-- | **A module of the build runs from the bytecode the build wrote.** Before a
-- | parser or a synthesizer it declares is run, the module is loaded into the
-- | session, after each module of the build it reaches through its imports,
-- | and each only once; a module from outside the build is the session's own.
-- |
-- | **What keeps the session from answering is a failure of compile-time
-- | execution, and no error of the module compiled.** It stops the compiling,
-- | and is returned beside it. A synthesizer that faults or uses up its budget
-- | is one too: it says nothing of whether the goal has a solution, so it is
-- | reported against the synthesizer, where the goal stands, and not as the
-- | program's error.
module Stella.CLI.Session.CompileTime
  ( CompileTimeError(..)
  , Loading
  , opened
  , ensureLoaded
  , reached
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl, for_)
import Data.Generic.Rep (class Generic)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Run (AFF, EFFECT, Run, liftEffect)
import Run.Except (EXCEPT, throw)
import Stella.CLI.Effect.Process (PROCESS)
import Stella.CLI.Session.Client (Launch, OpenFailure, RequestFailure, Session)
import Stella.CLI.Session.Client as Client
import Stella.CLI.Session.Guest (LoadFailure)
import Stella.Compiler.Build (BuiltModules)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin)
import Stella.Compiler.TypedCore.Name (Ident, ModuleName, Qualified)
import Type.Row (type (+))

data CompileTimeError
  -- | The session could not be opened.
  = SessionNotOpened OpenFailure
  -- | The session refused a request, or was lost.
  | RequestFailed RequestFailure
  -- | A parser's input could not be written as a value of the wire.
  | InputUnencodable String
  -- | An answer is not what a parser returns.
  | AnswerUnreadable String
  -- | A module of the build whose bytecode is not where the build was to
  -- | write it.
  | ModuleUnavailable ModuleName
  -- | A module of the build the session did not load.
  | ModuleNotLoaded { module :: ModuleName, failure :: LoadFailure }
  -- | A synthesizer that faulted, with the goal it was solving and what the
  -- | fault said.
  | SynthesizerFaulted { synthesizer :: Qualified Ident, goal :: Origin, detail :: String }
  -- | A synthesizer that took every step its budget allows, with the goal it was
  -- | solving.
  | SynthesizerBudgetExhausted { synthesizer :: Qualified Ident, goal :: Origin, budget :: Int }
  -- | The session lost, or the interpreter's own defect, while a synthesizer
  -- | ran.
  | SessionBroke String

derive instance Generic CompileTimeError _

instance Show CompileTimeError where
  show = genericShow

-- | What loading the modules of a build takes: the modules the session has
-- | loaded, and where the build wrote a module's bytecode, where it did.
type Loading r =
  { loaded :: Ref (Set ModuleName)
  , locate :: ModuleName -> Run (EXCEPT CompileTimeError + AFF + EFFECT + r) (Maybe String)
  }

-- | The session in the reference given, opened by the launch given where it is
-- | not yet open and kept there: a build that runs nothing opens none. Closing
-- | what was opened is the caller's.
opened :: forall r. Ref (Maybe Session) -> Launch -> Run (EXCEPT CompileTimeError + PROCESS + AFF + EFFECT + r) Session
opened held launch = liftEffect (Ref.read held) >>= case _ of
  Just session -> pure session
  Nothing -> Client.open launch >>= case _ of
    Left failure -> throw (SessionNotOpened failure)
    Right session -> session <$ liftEffect (Ref.write (Just session) held)

-- | The module given loaded into the session, after each module of the build
-- | it reaches, each once.
ensureLoaded :: forall r. Loading r -> Session -> BuiltModules -> ModuleName -> Run (EXCEPT CompileTimeError + AFF + EFFECT + r) Unit
ensureLoaded loading session built declaring =
  for_ (reached built declaring) \m -> do
    loaded <- liftEffect (Ref.read loading.loaded)
    unless (Set.member m loaded) do
      path <- loading.locate m >>= case _ of
        Just path -> pure path
        Nothing -> throw (ModuleUnavailable m)
      Client.load session path >>= case _ of
        Left failure -> throw (RequestFailed failure)
        Right (Left failure) -> throw (ModuleNotLoaded { module: m, failure })
        Right (Right _) -> liftEffect (Ref.modify_ (Set.insert m) loading.loaded)

-- | The modules of the build a module reaches through its imports, itself
-- | among them where it is one, each after those it imports.
reached :: BuiltModules -> ModuleName -> Array ModuleName
reached built = _.order <<< visit { seen: Set.empty, order: [] }
  where
  visit acc m
    | Set.member m acc.seen = acc
    | otherwise = case Map.lookup m built of
        Nothing -> acc
        Just i ->
          let
            after = foldl visit (acc { seen = Set.insert m acc.seen }) i.imports
          in
            after { order = Array.snoc after.order m }
