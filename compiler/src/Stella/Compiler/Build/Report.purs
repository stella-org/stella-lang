-- | What compiling reports: an error of each stage of a module, an error of
-- | the build around the modules, a warning, the places each is about, and
-- | what each says to an author.
-- |
-- | **A place is a range of the source.** A range in what an expansion
-- | produced is taken back to the call written in the source, through every
-- | expansion it stands in, and the place says beside it where what it covers
-- | was written: in the input of a call, or in a quotation of the module given.
-- | An error about the build rather than about a place — an interface, or a
-- | fault of the compiler's own — names none.
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
  , WrittenLocation
  , WrittenSource(..)
  , locationOf
  , locationsOf
  , primaryLocationOf
  , warningLocationOf
  , printCompileError
  , printCompileWarning
  , BuildError(..)
  , SourceRoot
  , BuildMessage
  , MessageLocation
  , WrittenFile(..)
  , buildMessages
  , warningMessage
  , printBuildMessage
  ) where

import Prelude

import Fmt (fmt)
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Foldable (foldMap)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.String (joinWith)
import Stella.Compiler.CST (SyntaxError, syntaxErrorMessage, syntaxErrorPosition)
import Stella.Compiler.CST.Check (CheckError(..), printCheckReason)
import Stella.Compiler.CST.Types (RangeSpace(..), SourcePos, SourceRange)
import Stella.Compiler.Bytecode.Lower (LowerError)
import Stella.Compiler.Elaborate.Environment.Imported (ImportError)
import Stella.Compiler.Elaborate.Surface.Module (ElaborationError)
import Stella.Compiler.Elaborate.Surface.Report (elaborationOrigins, printElaborationError)
import Stella.Compiler.Interface (InterfaceError)
import Stella.Compiler.Interface.Assemble (AssembleError)
import Stella.Compiler.Interface.Environment (EnvironmentError(..))
import Stella.Compiler.Macro.Expand (ExpansionError(..), ExpansionReason(..), printExpansionReason)
import Stella.Compiler.MiddleEnd.Translate (TranslateError)
import Stella.Compiler.Resolve.Group (GroupError(..), printGroupReason)
import Stella.Compiler.Resolve.Module (ResolutionError(..), ResolutionWarning(..))
import Stella.Compiler.Resolve.Monad (ResolveError(..), ResolveWarning(..), printResolveReason, printResolveWarning)
import Stella.Compiler.Resolve.Scope (ScopeError(..), ScopeWarning(..), printScopeReason, printScopeWarning)
import Stella.Compiler.Surface.Origin (Origin(..), originOf, rangeOf)
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
-- | imports, the signature they make, or the interfaces translation reads; or
-- | the module's interface the environment does not take, which is the
-- | compiler's fault.
data EnvironmentProblem
  = ViewRefused EnvironmentError
  | ImportsRefused ImportError
  | InterfacesRefused InterfaceError
  | InterfaceNotAdded EnvironmentError

-- | A checked Core module translation or lowering refused, or one whose
-- | interface does not assemble, which is the compiler's fault.
data BackendProblem
  = TranslateFailed TranslateError
  | LowerFailed LowerError
  -- | A module resolved without error with no surface part of an interface.
  | SurfaceInterfaceMissing
  | InterfaceUnassembled AssembleError

type CompileWarning = ResolutionWarning

-- | A range of the source: the first position it covers and the one just
-- | after it, a point where the two are one; and where what it covers was
-- | written, where an expansion produced it and it was written elsewhere.
type DiagnosticLocation = { start :: SourcePos, end :: SourcePos, written :: Maybe WrittenLocation }

-- | Where what an expansion produced was written: a range of a source.
type WrittenLocation = { source :: WrittenSource, start :: SourcePos, end :: SourcePos }

-- | The source a range is of: that of the file a diagnostic is about, or that
-- | of the module given, a quotation of which it is in.
data WrittenSource
  = ThisFile
  | ModuleAt ModuleName

derive instance Eq WrittenSource

instance Show WrittenSource where
  show = case _ of
    ThisFile -> "ThisFile"
    ModuleAt m -> "(ModuleAt " <> show m <> ")"

-- | The places an error is about, the one it is chiefly about first.
locationsOf :: CompileError -> Array DiagnosticLocation
locationsOf = case _ of
  Syntax (Unparsed e) -> [ point (syntaxErrorPosition e) ]
  Syntax (IllFormed (CheckError r _)) -> [ locationOf r ]
  Resolution e -> map locationOf (resolutionRanges e)
  Environment _ -> []
  Elaboration e -> map fromOrigin (elaborationOrigins e)
  Backend _ -> []
  where
  point pos = { start: pos, end: pos, written: Nothing }

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
warningLocationOf = locationOf <<< case _ of
  ScopingWarning (HidesImport r _ _) -> r
  ResolvingWarning (HidesTypeVariable r _) -> r
  ResolvingWarning (HidesValue r _) -> r
  ResolvingWarning (OpenHidesLocal r _) -> r

-- | A range of any text, as the range of the source it stands for.
locationOf :: SourceRange -> DiagnosticLocation
locationOf = fromOrigin <<< originOf

-- | The range of the source an origin is located by, and where what it covers
-- | was written: the source range the origins it was written as lead to,
-- | through every expansion, where it covers a token of its expansion and that
-- | range is another.
fromOrigin :: Surface.Origin -> DiagnosticLocation
fromOrigin o = { start: at.start, end: at.end, written: writtenOf o }
  where
  at = rangeOf o
  writtenOf = case _ of
    FromSource _ -> Nothing
    FromExpansion e | e.written == e.call -> Nothing
    FromExpansion e ->
      let
        w = sourceOf e.written
      in
        if w.source == ThisFile && w.start == at.start && w.end == at.end then Nothing else Just w
  sourceOf = case _ of
    FromSource r -> { source: sourceIn r.space, start: r.start, end: r.end }
    FromExpansion e -> sourceOf e.written
  sourceIn = case _ of
    Quotation m -> ModuleAt m
    _ -> ThisFile

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
    InterfaceNotAdded e -> internal ("the build environment does not take the module's interface: " <> show e)
  Elaboration e -> printElaborationError e
  Backend problem -> case problem of
    TranslateFailed e -> internal ("translation refused the checked module: " <> show e)
    LowerFailed e -> internal ("lowering refused the translated module: " <> show e)
    SurfaceInterfaceMissing -> internal "a module resolved without error has no interface"
    InterfaceUnassembled e -> internal ("the module's interface does not assemble: " <> show e)
  where
  internal what = "Internal compiler error: " <> what
  moduleText (ModuleName m) = m

printCompileWarning :: CompileWarning -> String
printCompileWarning = case _ of
  ScopingWarning w -> printScopeWarning w
  ResolvingWarning w -> printResolveWarning w

-- | Where a package keeps the modules named under a prefix: the prefix, and the
-- | directory from the package's root, one segment each.
type SourceRoot = { prefix :: Array String, dir :: Array String }

-- | What keeps a build from going on: source directories that do not name
-- | modules apart, a file it cannot place or read, modules whose imports make
-- | no order, or a module that does not compile.
data BuildError
  -- | A source directory whose prefix holds a segment no module's name may, or
  -- | that names no directory.
  = SourceRootInvalid SourceRoot
  -- | Two source directories under one prefix, or one standing in the other.
  | SourceRootsConflict { first :: SourceRoot, second :: SourceRoot }
  -- | A file standing in no source directory of the package, or with no
  -- | `.stel` extension.
  | OutsidePackage String
  -- | A file whose path holds a segment no module's name may: one that is no
  -- | name beginning with an upper case letter.
  | NotAModuleName String
  | ListedTwice String
  -- | Two files whose paths name one module.
  | NamedTwice { name :: ModuleName, paths :: Array String }
  | Unreadable { path :: String, detail :: String }
  -- | A module whose header names another module than its path does.
  | NameMismatch { path :: String, written :: ModuleName, expected :: ModuleName, at :: DiagnosticLocation }
  -- | A file whose path gives it a name the prefix of another source directory
  -- | claims, that directory being the one its longest prefix names.
  | NameReserved { path :: String, name :: ModuleName, owner :: SourceRoot }
  -- | A module of the build named as one the build is compiled against is.
  | NameInEnvironment { path :: String, name :: ModuleName }
  -- | Modules importing one another, in the order the build was given them.
  | ImportCycle (NonEmptyArray { path :: String, name :: ModuleName })
  -- | A module that does not compile, with the path of each module of the
  -- | build, which a place its errors name may be written in.
  | ModuleFailed { path :: String, name :: ModuleName, errors :: NonEmptyArray CompileError, paths :: Map ModuleName String }

-- | One thing a build error or a warning says: the file it is about, the
-- | places in it, and what it says.
type BuildMessage = { path :: Maybe String, locations :: Array MessageLocation, message :: String }

-- | A place in the file a message is about, and where what it covers was
-- | written.
type MessageLocation =
  { start :: SourcePos
  , end :: SourcePos
  , written :: Maybe { file :: WrittenFile, start :: SourcePos, end :: SourcePos }
  }

-- | A file a range is of: by its path, or, for a module the build is compiled
-- | against, by the module's name.
data WrittenFile
  = FileAt String
  | InModule ModuleName

derive instance Eq WrittenFile

instance Show WrittenFile where
  show = case _ of
    FileAt p -> "(FileAt " <> show p <> ")"
    InModule m -> "(InModule " <> show m <> ")"

-- | What a build error says, one message for each error of a module.
buildMessages :: BuildError -> NonEmptyArray BuildMessage
buildMessages = case _ of
  SourceRootInvalid root -> none (fmt @"The source directory `{dir}` for modules under `{prefix}` names no directory, or its prefix holds a segment no module's name may" { dir: dirText root, prefix: prefixText root })
  SourceRootsConflict r -> none (fmt @"The source directories `{first}` and `{second}` do not name their modules apart: they share a prefix, or one stands in the other" { first: dirText r.first, second: dirText r.second })
  OutsidePackage path -> one path [] "This file is in no source directory of the package, or is no `.stel` file"
  NotAModuleName path -> one path [] "This path names no module: each directory and the file's name must begin with an upper case letter, and hold letters, digits, `_`, and `'` alone"
  ListedTwice path -> one path [] "This file is given to the build twice"
  NamedTwice r -> NonEmptyArray.singleton
    { path: Nothing
    , locations: []
    , message: fmt @"These files name one module, `{name}`: {paths}" { name: moduleText r.name, paths: joinWith ", " r.paths }
    }
  Unreadable r -> one r.path [] ("This file cannot be read: " <> r.detail)
  NameMismatch r -> one r.path [ located Map.empty r.path r.at ]
    (fmt @"This module is named `{written}`, and its path names it `{expected}`" { written: moduleText r.written, expected: moduleText r.expected })
  NameReserved r -> one r.path [] (fmt @"This file cannot hold `{name}`: modules under `{prefix}` are kept in `{dir}`" { name: moduleText r.name, prefix: prefixText r.owner, dir: dirText r.owner })
  NameInEnvironment r -> one r.path [] (fmt @"This file holds `{name}`, which names a module the build is compiled against" { name: moduleText r.name })
  ImportCycle members -> NonEmptyArray.singleton
    { path: Nothing
    , locations: []
    , message: "These modules import one another: " <> joinWith ", " (map (moduleText <<< _.name) (NonEmptyArray.toArray members))
    }
  ModuleFailed r -> map (\e -> { path: Just r.path, locations: map (located r.paths r.path) (locationsOf e), message: printCompileError e }) r.errors
  where
  one path locations message = NonEmptyArray.singleton { path: Just path, locations, message }
  none message = NonEmptyArray.singleton { path: Nothing, locations: [], message }
  dirText root = joinWith "/" root.dir
  prefixText root = joinWith "." root.prefix
  moduleText (ModuleName m) = m

-- | What a warning about the file given says, the path of each module of the
-- | build given.
warningMessage :: Map ModuleName String -> String -> CompileWarning -> BuildMessage
warningMessage paths path w = { path: Just path, locations: [ located paths path (warningLocationOf w) ], message: printCompileWarning w }

-- | A place in the file given, where it was written named by the path of a
-- | module of the build, or by the module's name.
located :: Map ModuleName String -> String -> DiagnosticLocation -> MessageLocation
located paths path l = l { written = map (\w -> { file: fileOf w.source, start: w.start, end: w.end }) l.written }
  where
  fileOf = case _ of
    ThisFile -> FileAt path
    ModuleAt m -> maybe (InModule m) FileAt (Map.lookup m paths)

-- | A message as an author reads it: the file and the first place, what it
-- | says, and the other places; each place followed by where what it covers
-- | was written, where that is elsewhere.
printBuildMessage :: BuildMessage -> String
printBuildMessage m = case m.path, Array.uncons m.locations of
  Just path, Just { head, tail } ->
    fmt @"{path}:{place}: {message}{written}{also}" { path, place: place head, message: m.message, written: writtenAt head, also: seeAlso tail }
  Just path, Nothing -> fmt @"{path}: {message}" { path, message: m.message }
  Nothing, _ -> m.message
  where
  place :: forall r. { start :: SourcePos | r } -> String
  place l = fmt @"{line}:{column}" { line: l.start.line, column: l.start.column }
  writtenAt l = foldMap (\w -> fmt @" (written at {file}:{place})" { file: fileText w.file, place: place w }) l.written
  seeAlso locations
    | Array.null locations = ""
    | otherwise = fmt @" (see also {places})" { places: joinWith ", " (map (\l -> place l <> writtenAt l) locations) }
  fileText = case _ of
    FileAt p -> p
    InModule (ModuleName n) -> n
