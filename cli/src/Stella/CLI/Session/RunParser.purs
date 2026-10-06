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
module Stella.CLI.Session.RunParser
  ( ParserRunnerError(..)
  , sessionParser
  , openingParser
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Maybe (Maybe(..))
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Run (AFF, EFFECT, Run, liftEffect)
import Stella.CLI.Effect.Process (PROCESS)
import Run.Except (EXCEPT, throw)
import Stella.CLI.Session.Client (Launch, OpenFailure, RequestFailure, Session)
import Stella.CLI.Session.Client as Client
import Stella.CLI.Session.Syntax (inputOf, readAnswer)
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

derive instance Generic ParserRunnerError _

instance Show ParserRunnerError where
  show = genericShow

-- | `sessionParser` on a session opened by the launch given when the first
-- | parser is run, and kept in the reference given for the parsers after it: a
-- | build that runs none opens none. Closing what was opened is the caller's.
openingParser :: forall r. Ref (Maybe Session) -> Launch -> Descriptor -> RunParser (Run (EXCEPT ParserRunnerError + PROCESS + AFF + EFFECT + r))
openingParser held launch descriptor name call = do
  session <- liftEffect (Ref.read held) >>= case _ of
    Just session -> pure session
    Nothing -> Client.open launch >>= case _ of
      Left failure -> throw (SessionNotOpened failure)
      Right session -> session <$ liftEffect (Ref.write (Just session) held)
  sessionParser session descriptor name call
