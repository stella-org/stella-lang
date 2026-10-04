-- | What expanding a macro call asks of whoever runs parsers, in the
-- | compiler's own terms
-- | ([Syntax Extensions and Parsers](../../../../docs/proposals/09-Syntax-Extensions-and-Parsers.md)).
-- |
-- | **The compiler does not run a parser itself.** A macro is guest code, run
-- | on a compile-time session the compiler knows nothing of; the expansion
-- | stage is handed a `RunParser` and asks it, and what answers is the host's
-- | to supply — a session in a build, a table in a test.
module Stella.Compiler.Macro.Run
  ( MacroInput
  , ParseFailure
  , ExecutionReason(..)
  , ParseOutcome(..)
  , RunParser
  , ExpansionSettings
  , defaultSettings
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Set (Set)
import Data.Show.Generic (genericShow)
import Stella.Compiler.Macro.Tree (Position, Syntax, Term, TokenTree)
import Stella.Compiler.TypedCore.Name (Ident, Qualified)

-- | What a parser reads: the trees of a call, and the position the input they
-- | were delimited by ends at.
type MacroInput = { trees :: Array TokenTree, end :: Position }

-- | Why a parser failed: where, the set of what it expected there, and the
-- | labels of the contexts it was in.
type ParseFailure = { position :: Position, expected :: Set String, labels :: Array String }

-- | Why a parser did not run to an answer of its own.
data ExecutionReason
  = NoSuchModule
  | NoSuchGlobal
  -- | The global holds no `Stella.Syntax.Parser`.
  | NotAParser
  -- | The global holds a `Stella.Syntax.Parser` whose function is not callable.
  | ParserNotCallable
  -- | The input is no canonical value, or none of the type its place wants.
  | InputInvalid
  -- | The parser performed an effect it handles nowhere.
  | EffectRequested
  -- | The parser called a foreign the host carries out.
  | ForeignRequested
  -- | The parser reached state it did not make: an array made before it ran.
  | StateRequested
  -- | The parser called an operation no parser may.
  | OperationWithheld
  -- | The parser faulted.
  | Fault
  -- | What the parser returned is not a `Stella.Syntax.Result (Stella.Syntax.Syntax
  -- | Stella.Syntax.Term)`.
  | ResultInvalid

-- | What running a parser came to.
data ParseOutcome
  = ParsedAs (Syntax Term)
  | FailedAs ParseFailure
  | ExecutionFailedAs { reason :: ExecutionReason, detail :: String }
  | BudgetExceededAs

-- | Run the parser the global holds, on the input, within the steps given.
type RunParser m = Qualified Ident -> { input :: MacroInput, budget :: Int } -> m ParseOutcome

-- | The steps one parse may take, and how many expansions deep a chain of calls
-- | may go: a call written in the source is at depth 1, and one an expansion at
-- | depth `n` produced at `n + 1`.
type ExpansionSettings = { budget :: Int, maxDepth :: Int }

defaultSettings :: ExpansionSettings
defaultSettings = { budget: 1_000_000, maxDepth: 64 }

derive instance Eq ExecutionReason
derive instance Generic ExecutionReason _
instance Show ExecutionReason where
  show = genericShow
