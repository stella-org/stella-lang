-- | The tests that run a program built from source, or check what building it
-- | gives: the bytecode fixtures built from `fixtures/source` and checked to be
-- | what is committed, and programs built and run on Steam. Run with
-- | `spago test -p e2e`.
module Test.E2E where

import Prelude

import Data.Either (Either(..))
import Effect (Effect)
import Effect.Exception (throw)
import Test.E2E.Arrays as Arrays
import Test.E2E.Cells as Cells
import Test.E2E.Continuations as Continuations
import Test.E2E.Facade as Facade
import Test.E2E.Fixtures as Fixtures
import E2E.Build (readSources)
import Test.E2E.HandlerDeclarations as HandlerDeclarations
import Test.E2E.ImplicitHandlers as ImplicitHandlers
import Test.E2E.Sugar as Sugar
import Test.E2E.Handling as Handling
import Test.E2E.Load as Load
import Test.E2E.Matches as Matches
import Test.E2E.Records as Records
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

-- | The sources are read, and what every build of them shares made, once.
main :: Effect Unit
main = readSources >>= case _ of
  Left err -> throw err
  Right sources -> runSpecAndExitProcess [ consoleReporter ] do
    Fixtures.spec sources
    Load.spec sources
    Arrays.spec sources
    Matches.spec sources
    Handling.spec sources
    Cells.spec sources
    HandlerDeclarations.spec sources
    ImplicitHandlers.spec sources
    Sugar.spec sources
    Continuations.spec sources
    Records.spec sources
    Facade.spec sources
