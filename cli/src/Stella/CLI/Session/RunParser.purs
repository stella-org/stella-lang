-- | A macro's parser run on a compile-time session: the `RunParser` the build
-- | driver asks, carried out by a `parse` request.
-- |
-- | **What the parser comes to is an outcome; what keeps the session from
-- | answering is a failure of the runner.** A parser that fails, faults, or
-- | runs out of its steps is answered as such, and the build reports it where
-- | the call stands. A request the session refused or could not carry, an
-- | input that cannot be written to the wire, and an answer that is not what
-- | the descriptor says a parser returns are faults of the session or of this
-- | client, no fault of the module: they stop the compiling, and are returned
-- | beside it rather than as an error of the module.
-- |
-- | **A macro of the build runs from the bytecode the build wrote.** Before its
-- | parser is run, the module declaring it is loaded into the session, after
-- | each module of the build it reaches through its imports, and each only
-- | once; a module from outside the build is the session's own. A module whose
-- | bytecode is not where the build was to write it, or that the session does
-- | not load, stops the compiling as the session does.
module Stella.CLI.Session.RunParser
  ( ParserRunnerError(..)
  , Loading
  , sessionParser
  , loadingParser
  , openingParser
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl, for_)
import Data.Generic.Rep (class Generic)
import Data.Map as Map
import Data.Show.Generic (genericShow)
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Run (AFF, EFFECT, Run, liftEffect)
import Stella.CLI.Effect.Process (PROCESS)
import Run.Except (EXCEPT, throw)
import Stella.CLI.Session.Client (Launch, OpenFailure, RequestFailure, Session)
import Stella.CLI.Session.Client as Client
import Stella.CLI.Session.Guest (LoadFailure)
import Stella.CLI.Session.Syntax (inputOf, readAnswer)
import Stella.Compiler.Build (BuiltModules)
import Stella.Compiler.Elaborate.Protocol.Guest.Shape (Descriptor)
import Stella.Compiler.Macro.Run (RunParser)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..))
import Type.Row (type (+))

data ParserRunnerError
  -- | The session could not be opened.
  = SessionNotOpened OpenFailure
  -- | The session refused the request, or was lost.
  | RequestFailed RequestFailure
  -- | The input could not be written as a value of the wire.
  | InputUnencodable String
  -- | The answer is not what a parser returns.
  | AnswerUnreadable String
  -- | A module of the build whose bytecode is not where the build was to
  -- | write it.
  | ModuleUnavailable ModuleName
  -- | A module of the build the session did not load.
  | ModuleNotLoaded { module :: ModuleName, failure :: LoadFailure }

-- | Run each parser the build asks for on the session given, reading what it
-- | returns by the descriptor of the types crossing to the host. A failure of
-- | the runner is thrown, and stops the compiling where it is caught.
sessionParser :: forall r. Session -> Descriptor -> RunParser (Run (EXCEPT ParserRunnerError + AFF + EFFECT + r))
sessionParser session descriptor (Qualified (ModuleName m) (Ident n)) { input, budget } = do
  encoded <- inputOf input.trees input.end # orThrow InputUnencodable
  answer <- Client.parse session { parser: { module: m, name: n }, input: encoded, budget } >>= orThrow RequestFailed
  readAnswer descriptor answer # orThrow AnswerUnreadable
  where
  orThrow :: forall e a. (e -> ParserRunnerError) -> Either e a -> Run (EXCEPT ParserRunnerError + AFF + EFFECT + r) a
  orThrow wrap = case _ of
    Left e -> throw (wrap e)
    Right a -> pure a

-- | What loading the modules of a build takes: the modules the session has
-- | loaded, and where the build wrote a module's bytecode, where it did.
type Loading r =
  { loaded :: Ref (Set ModuleName)
  , locate :: ModuleName -> Run (EXCEPT ParserRunnerError + AFF + EFFECT + r) (Maybe String)
  }

-- | `sessionParser`, the module declaring the parser and those of the build it
-- | reaches loaded first.
loadingParser :: forall r. Loading r -> Session -> Descriptor -> BuiltModules -> RunParser (Run (EXCEPT ParserRunnerError + AFF + EFFECT + r))
loadingParser loading session descriptor built name@(Qualified declaring _) call = do
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
  sessionParser session descriptor name call

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

derive instance Generic ParserRunnerError _

instance Show ParserRunnerError where
  show = genericShow

-- | `loadingParser` on a session opened by the launch given when the first
-- | parser is run, and kept in the reference given for the parsers after it: a
-- | build that runs none opens none. Closing what was opened is the caller's.
openingParser :: forall r. Ref (Maybe Session) -> Launch -> Descriptor -> Loading (PROCESS + r) -> BuiltModules -> RunParser (Run (EXCEPT ParserRunnerError + PROCESS + AFF + EFFECT + r))
openingParser held launch descriptor loading built name call = do
  session <- liftEffect (Ref.read held) >>= case _ of
    Just session -> pure session
    Nothing -> Client.open launch >>= case _ of
      Left failure -> throw (SessionNotOpened failure)
      Right session -> session <$ liftEffect (Ref.write (Just session) held)
  loadingParser loading session descriptor built name call
