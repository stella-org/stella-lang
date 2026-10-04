-- | The request that runs a parser a loaded module declares on the token tree
-- | of a macro call.
-- |
-- | ```text
-- | parse  { parser: { module, name },     → parsed { syntax }
-- |          input: { trees, end },          or parseFailed { failure }
-- |          budget }                        or executionFailed { reason, detail }
-- |                                          or budgetExceeded {}
-- | ```
-- |
-- | **The session runs `Stella.Syntax.runParser` on the parser's value**, the
-- | trees, and the position the input ends at, and answers with what it
-- | returns: `parsed` with the syntax, or `parseFailed` with the failure. A
-- | parser reaches no observable state outside its run, so an effect it performs
-- | and handles nowhere ends it, as one failing to execute does.
-- |
-- | **A budget bounds the steps a parse takes**, an integer from 1 to
-- | 2147483647, as it bounds an invocation's; a parser needing more is answered
-- | with `budgetExceeded`. A parse has no attempt and is not cancelled: nothing
-- | it does waits on anything outside it.
-- |
-- | **Every payload has exactly the fields shown.** `trees`, `end`, `syntax`,
-- | and `failure` are generic values ([Value](Value.purs)), read here as JSON and
-- | no further: whether one is a canonical value of the type its place wants is
-- | the reader's to settle, `trees` being a `Stella.Syntax.List
-- | Stella.Syntax.TokenTree` and `end` a `Stella.Syntax.Position`.
module Stella.CLI.Session.Parse
  ( ParseRequest
  , ExecutionReason(..)
  , ExecutionFailure
  , ParseAnswer(..)
  , parseKind
  , parsedKind
  , parseFailedKind
  , executionFailedKind
  , budgetExceededKind
  , encodeParse
  , decodeParse
  , encodeParsed
  , decodeParsed
  , encodeParseFailed
  , decodeParseFailed
  , encodeExecutionFailed
  , decodeExecutionFailed
  , encodeBudgetExceeded
  , decodeBudgetExceeded
  ) where

import Prelude

import Data.Argonaut.Core (Json, caseJsonObject, caseJsonString, fromNumber, fromObject, fromString)
import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))
import Foreign.Object (Object)
import Foreign.Object as Object
import Stella.CLI.Session.Guest (GlobalName, positiveOf)

-- | A `parse`: the global holding the parser, the trees it reads and where they
-- | end, and the steps it may take.
type ParseRequest =
  { parser :: GlobalName
  , input :: { trees :: Json, end :: Json }
  , budget :: Int
  }

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

derive instance Eq ExecutionReason
derive instance Generic ExecutionReason _
instance Show ExecutionReason where
  show = genericShow

type ExecutionFailure = { reason :: ExecutionReason, detail :: String }

-- | What a `parse` is answered with, its values as JSON.
data ParseAnswer
  = Parsed Json
  | ParseFailed Json
  | ExecutionFailed ExecutionFailure
  | BudgetExceeded

parseKind :: String
parseKind = "parse"

parsedKind :: String
parsedKind = "parsed"

parseFailedKind :: String
parseFailedKind = "parseFailed"

executionFailedKind :: String
executionFailedKind = "executionFailed"

budgetExceededKind :: String
budgetExceededKind = "budgetExceeded"

encodeParse :: ParseRequest -> Object Json
encodeParse r = Object.fromFoldable
  [ Tuple "parser" $ fromObject $ Object.fromFoldable
      [ Tuple "module" (fromString r.parser.module)
      , Tuple "name" (fromString r.parser.name)
      ]
  , Tuple "input" $ fromObject $ Object.fromFoldable
      [ Tuple "trees" r.input.trees
      , Tuple "end" r.input.end
      ]
  , Tuple "budget" (fromNumber (Int.toNumber r.budget))
  ]

-- | A `parse` whose budget is not an integer from 1 to 2147483647 has no reading.
decodeParse :: Object Json -> Maybe ParseRequest
decodeParse o = do
  exactly [ "parser", "input", "budget" ] o
  p <- Object.lookup "parser" o >>= objectOf
  exactly [ "module", "name" ] p
  m <- Object.lookup "module" p >>= stringOf
  name <- Object.lookup "name" p >>= stringOf
  i <- Object.lookup "input" o >>= objectOf
  exactly [ "trees", "end" ] i
  trees <- Object.lookup "trees" i
  end <- Object.lookup "end" i
  budget <- Object.lookup "budget" o >>= positiveOf
  pure { parser: { module: m, name }, input: { trees, end }, budget }

encodeParsed :: Json -> Object Json
encodeParsed = Object.singleton "syntax"

decodeParsed :: Object Json -> Maybe Json
decodeParsed o = exactly [ "syntax" ] o *> Object.lookup "syntax" o

encodeParseFailed :: Json -> Object Json
encodeParseFailed = Object.singleton "failure"

decodeParseFailed :: Object Json -> Maybe Json
decodeParseFailed o = exactly [ "failure" ] o *> Object.lookup "failure" o

encodeExecutionFailed :: ExecutionFailure -> Object Json
encodeExecutionFailed f = Object.fromFoldable
  [ Tuple "reason" (fromString (reasonCode f.reason))
  , Tuple "detail" (fromString f.detail)
  ]

decodeExecutionFailed :: Object Json -> Maybe ExecutionFailure
decodeExecutionFailed o = do
  exactly [ "reason", "detail" ] o
  reason <- Object.lookup "reason" o >>= stringOf >>= reasonOf
  detail <- Object.lookup "detail" o >>= stringOf
  pure { reason, detail }

encodeBudgetExceeded :: Object Json
encodeBudgetExceeded = Object.empty

decodeBudgetExceeded :: Object Json -> Maybe Unit
decodeBudgetExceeded = exactly []

reasonCode :: ExecutionReason -> String
reasonCode = case _ of
  NoSuchModule -> "noSuchModule"
  NoSuchGlobal -> "noSuchGlobal"
  NotAParser -> "notAParser"
  ParserNotCallable -> "parserNotCallable"
  InputInvalid -> "inputInvalid"
  EffectRequested -> "effectRequested"
  ForeignRequested -> "foreignRequested"
  StateRequested -> "stateRequested"
  OperationWithheld -> "operationWithheld"
  Fault -> "fault"
  ResultInvalid -> "resultInvalid"

reasonOf :: String -> Maybe ExecutionReason
reasonOf code = Array.find (\r -> reasonCode r == code) allReasons

allReasons :: Array ExecutionReason
allReasons =
  [ NoSuchModule
  , NoSuchGlobal
  , NotAParser
  , ParserNotCallable
  , InputInvalid
  , EffectRequested
  , ForeignRequested
  , StateRequested
  , OperationWithheld
  , Fault
  , ResultInvalid
  ]

-- | The object has exactly these fields.
exactly :: Array String -> Object Json -> Maybe Unit
exactly names o
  | Array.sort (Object.keys o) == Array.sort names = Just unit
  | otherwise = Nothing

stringOf :: Json -> Maybe String
stringOf = caseJsonString Nothing Just

objectOf :: Json -> Maybe (Object Json)
objectOf = caseJsonObject Nothing Just
