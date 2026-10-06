-- | What compiling reports: an error of each stage of a module, an error of
-- | the build around the modules, a warning, the places each is about, and
-- | what each says to an author.
-- |
-- | **A place is a range of the source.** A range in what an expansion
-- | produced is taken back to the call written in the source, through every
-- | expansion it stands in. An error about the build rather than about a
-- | place — an interface, or a fault of the compiler's own — names none.
-- |
-- | **A fault of the compiler's is said to be one**, so that an author tells a
-- | program to correct from a compiler to report.
module Stella.Compiler.Build.Report
  ( CompileError(..)
  , SyntaxProblem(..)
  , EnvironmentProblem(..)
  , BackendProblem(..)
  , CompileWarning
  , DiagnosticLocation
  , locationsOf
  , primaryLocationOf
  , warningLocationOf
  , printCompileError
  , printCompileWarning
  , BuildError(..)
  , BuildMessage
  , buildMessages
  ) where

import Prelude

import Fmt (fmt)
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Maybe (Maybe(..))
import Data.String (joinWith)
import Stella.Compiler.CST (SyntaxError, syntaxErrorMessage, syntaxErrorPosition)
import Stella.Compiler.CST.Check (CheckError(..), printCheckReason)
import Stella.Compiler.CST.Types (SourcePos, SourceRange)
import Stella.Compiler.Bytecode.Lower (LowerError)
import Stella.Compiler.Elaborate.Environment.Imported (ImportError)
import Stella.Compiler.Elaborate.Surface.Module (ElaborationError)
import Stella.Compiler.Elaborate.Surface.Report (elaborationOrigins, printElaborationError)
import Stella.Compiler.Interface (InterfaceError)
import Stella.Compiler.Interface.Environment (EnvironmentError(..))
import Stella.Compiler.Macro.Expand (ExpansionError(..), ExpansionReason(..), printExpansionReason)
import Stella.Compiler.MiddleEnd.Translate (TranslateError)
import Stella.Compiler.Resolve.Group (GroupError(..), printGroupReason)
import Stella.Compiler.Resolve.Module (ResolutionError(..), ResolutionWarning(..))
import Stella.Compiler.Resolve.Monad (ResolveError(..), ResolveWarning(..), printResolveReason, printResolveWarning)
import Stella.Compiler.Resolve.Scope (ScopeError(..), ScopeWarning(..), printScopeReason, printScopeWarning)
import Stella.Compiler.Surface.Origin (originOf, rangeOf)
import Stella.Compiler.Surface.Origin as Surface
import Stella.Compiler.TypedCore.Name (ModuleName(..))

-- | An error of one stage of compiling a module.
data CompileError
  = Syntax SyntaxProblem
  | Resolution ResolutionError
  | Environment EnvironmentProblem
  | Elaboration ElaborationError
  | Backend BackendProblem

-- | Text that is no module, or a module whose syntax no later stage reads.
data SyntaxProblem
  = Unparsed SyntaxError
  | IllFormed CheckError

-- | What the build environment cannot give the module: the view of its
-- | imports, the signature they make, or the interfaces translation reads.
data EnvironmentProblem
  = ViewRefused EnvironmentError
  | ImportsRefused ImportError
  | InterfacesRefused InterfaceError

-- | A checked Core module translation or lowering refused, which is the
-- | compiler's fault.
data BackendProblem
  = TranslateFailed TranslateError
  | LowerFailed LowerError

type CompileWarning = ResolutionWarning

-- | A range of the source: the first position it covers and the one just
-- | after it; a point where the two are one.
type DiagnosticLocation = { start :: SourcePos, end :: SourcePos }

-- | The places an error is about, the one it is chiefly about first.
locationsOf :: CompileError -> Array DiagnosticLocation
locationsOf = case _ of
  Syntax (Unparsed e) -> [ point (syntaxErrorPosition e) ]
  Syntax (IllFormed (CheckError r _)) -> [ inSource r ]
  Resolution e -> map inSource (resolutionRanges e)
  Environment _ -> []
  Elaboration e -> map fromOrigin (elaborationOrigins e)
  Backend _ -> []
  where
  point pos = { start: pos, end: pos }

primaryLocationOf :: CompileError -> Maybe DiagnosticLocation
primaryLocationOf = Array.head <<< locationsOf

resolutionRanges :: ResolutionError -> Array SourceRange
resolutionRanges = case _ of
  GroupingError (GroupError r _) -> [ r ]
  ScopingError (ScopeError r _) -> [ r ]
  ResolvingError (ResolveError r _) -> [ r ]
  -- where in its input the parser failed, then the call
  ExpandingError (ExpansionError r (ParserFailed at _)) -> [ at, r ]
  ExpandingError (ExpansionError r _) -> [ r ]

warningLocationOf :: CompileWarning -> DiagnosticLocation
warningLocationOf = inSource <<< case _ of
  ScopingWarning (HidesImport r _ _) -> r
  ResolvingWarning (HidesTypeVariable r _) -> r
  ResolvingWarning (HidesValue r _) -> r
  ResolvingWarning (OpenHidesLocal r _) -> r

-- | A range of any text, as the range of the source it stands for.
inSource :: SourceRange -> DiagnosticLocation
inSource = fromOrigin <<< originOf

fromOrigin :: Surface.Origin -> DiagnosticLocation
fromOrigin o = let r = rangeOf o in { start: r.start, end: r.end }

printCompileError :: CompileError -> String
printCompileError = case _ of
  Syntax (Unparsed e) -> syntaxErrorMessage e
  Syntax (IllFormed (CheckError _ reason)) -> printCheckReason reason
  Resolution e -> case e of
    GroupingError (GroupError _ reason) -> printGroupReason reason
    ScopingError (ScopeError _ reason) -> printScopeReason reason
    ResolvingError (ResolveError _ reason) -> printResolveReason reason
    ExpandingError (ExpansionError _ reason) -> printExpansionReason reason
  Environment problem -> case problem of
    ViewRefused (NotInEnvironment m) -> fmt @"The module `{m}` is not available to this build" { m: moduleText m }
    ViewRefused e -> internal ("the build environment is inconsistent: " <> show e)
    ImportsRefused e -> "The interfaces of the imported modules do not agree: " <> show e
    InterfacesRefused e -> "The interfaces of the imported modules do not agree: " <> show e
  Elaboration e -> printElaborationError e
  Backend problem -> case problem of
    TranslateFailed e -> internal ("translation refused the checked module: " <> show e)
    LowerFailed e -> internal ("lowering refused the translated module: " <> show e)
  where
  internal what = "Internal compiler error: " <> what
  moduleText (ModuleName m) = m

printCompileWarning :: CompileWarning -> String
printCompileWarning = case _ of
  ScopingWarning w -> printScopeWarning w
  ResolvingWarning w -> printResolveWarning w

-- | What keeps a build from going on: a file it cannot place or read, modules
-- | whose imports make no order, or a module that does not compile.
data BuildError
  -- | A file standing in neither `src` nor `test` of the package, or with no
  -- | `.stel` extension.
  = OutsidePackage String
  -- | A file whose path holds a segment no module's name may: one that is no
  -- | name beginning with an upper case letter.
  | NotAModuleName String
  | ListedTwice String
  -- | Two files whose paths name one module.
  | NamedTwice { name :: ModuleName, paths :: Array String }
  | Unreadable { path :: String, detail :: String }
  -- | A module whose header names another module than its path does.
  | NameMismatch { path :: String, written :: ModuleName, expected :: ModuleName, at :: DiagnosticLocation }
  -- | A module of `src` whose path gives it a name beginning with `Test`, which
  -- | the modules of `test` are named under.
  | NameReserved { path :: String, name :: ModuleName }
  -- | Modules importing one another, in the order the build was given them.
  | ImportCycle (NonEmptyArray { path :: String, name :: ModuleName })
  -- | An import of another module of the build, which this version does not
  -- | compile against.
  | ImportWithinBuild { path :: String, imported :: ModuleName, at :: DiagnosticLocation }
  | ModuleFailed { path :: String, name :: ModuleName, errors :: NonEmptyArray CompileError }

-- | One thing a build error says: the file it is about, the places in it, and
-- | what it says.
type BuildMessage = { path :: Maybe String, locations :: Array DiagnosticLocation, message :: String }

-- | What a build error says, one message for each error of a module.
buildMessages :: BuildError -> NonEmptyArray BuildMessage
buildMessages = case _ of
  OutsidePackage path -> one path [] "This file is in neither `src` nor `test` of the package, or is no `.stel` file"
  NotAModuleName path -> one path [] "This path names no module: each directory and the file's name must begin with an upper case letter, and hold letters, digits, `_`, and `'` alone"
  ListedTwice path -> one path [] "This file is given to the build twice"
  NamedTwice r -> NonEmptyArray.singleton
    { path: Nothing
    , locations: []
    , message: fmt @"These files name one module, `{name}`: {paths}" { name: moduleText r.name, paths: joinWith ", " r.paths }
    }
  Unreadable r -> one r.path [] ("This file cannot be read: " <> r.detail)
  NameMismatch r -> one r.path [ r.at ]
    (fmt @"This module is named `{written}`, and its path names it `{expected}`" { written: moduleText r.written, expected: moduleText r.expected })
  NameReserved r -> one r.path [] (fmt @"A module of `src` cannot be named `{name}`: the modules of `test` are named under `Test`" { name: moduleText r.name })
  ImportCycle members -> NonEmptyArray.singleton
    { path: Nothing
    , locations: []
    , message: "These modules import one another: " <> joinWith ", " (map (moduleText <<< _.name) (NonEmptyArray.toArray members))
    }
  ImportWithinBuild r -> one r.path [ r.at ]
    (fmt @"`{imported}` is a module of this build, and this version of the compiler compiles a module only against modules built before" { imported: moduleText r.imported })
  ModuleFailed r -> map (\e -> { path: Just r.path, locations: locationsOf e, message: printCompileError e }) r.errors
  where
  one path locations message = NonEmptyArray.singleton { path: Just path, locations, message }
  moduleText (ModuleName m) = m
