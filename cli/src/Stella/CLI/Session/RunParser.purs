-- | A macro's parser run on a compile-time session: the `RunParser` the build
-- | driver asks, carried out by a `parse` request.
-- |
-- | **What the parser comes to is an outcome; what keeps the session from
-- | answering is a failure of compile-time execution**
-- | ([CompileTime](CompileTime.purs)). A parser that fails, faults, or runs out
-- | of its steps is answered as such, and the build reports it where the call
-- | stands. A request the session refused or could not carry, an input that
-- | cannot be written to the wire, and an answer that is not what the
-- | descriptor says a parser returns are faults of the session or of this
-- | client, no fault of the module: they stop the compiling, and are returned
-- | beside it rather than as an error of the module.
-- |
-- | **A macro of the build runs from the bytecode the build wrote**: the module
-- | declaring it is loaded first, as [CompileTime](CompileTime.purs) loads one.
module Stella.CLI.Session.RunParser
  ( sessionParser
  , loadingParser
  , openingParser
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Effect.Ref (Ref)
import Run (AFF, EFFECT, Run)
import Run.Except (EXCEPT, throw)
import Stella.CLI.Effect.Process (PROCESS)
import Stella.CLI.Session.Client (Launch, Session)
import Stella.CLI.Session.Client as Client
import Stella.CLI.Session.CompileTime (CompileTimeError(..), Loading, ensureLoaded, opened)
import Stella.CLI.Session.Syntax (inputOf, readAnswer)
import Stella.Compiler.Build (BuiltModules)
import Stella.Compiler.Elaborate.Protocol.Guest.Shape (Descriptor)
import Stella.Compiler.Macro.Run (RunParser)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..))
import Type.Row (type (+))

-- | Run each parser the build asks for on the session given, reading what it
-- | returns by the descriptor of the types crossing to the host. A failure of
-- | the runner is thrown, and stops the compiling where it is caught.
sessionParser :: forall r. Session -> Descriptor -> RunParser (Run (EXCEPT CompileTimeError + AFF + EFFECT + r))
sessionParser session descriptor (Qualified (ModuleName m) (Ident n)) { input, budget } = do
  encoded <- inputOf input.trees input.end # orThrow InputUnencodable
  answer <- Client.parse session { parser: { module: m, name: n }, input: encoded, budget } >>= orThrow RequestFailed
  readAnswer descriptor answer # orThrow AnswerUnreadable
  where
  orThrow :: forall e a. (e -> CompileTimeError) -> Either e a -> Run (EXCEPT CompileTimeError + AFF + EFFECT + r) a
  orThrow wrap = case _ of
    Left e -> throw (wrap e)
    Right a -> pure a

-- | `sessionParser`, the module declaring the parser and those of the build it
-- | reaches loaded first.
loadingParser :: forall r. Loading r -> Session -> Descriptor -> BuiltModules -> RunParser (Run (EXCEPT CompileTimeError + AFF + EFFECT + r))
loadingParser loading session descriptor built name@(Qualified declaring _) call = do
  ensureLoaded loading session built declaring
  sessionParser session descriptor name call

-- | `loadingParser` on the session in the reference given, opened by the launch
-- | given when the first thing is run on it.
openingParser :: forall r. Ref (Maybe Session) -> Launch -> Descriptor -> Loading (PROCESS + r) -> BuiltModules -> RunParser (Run (EXCEPT CompileTimeError + PROCESS + AFF + EFFECT + r))
openingParser held launch descriptor loading built name call = do
  session <- opened held launch
  loadingParser loading session descriptor built name call
