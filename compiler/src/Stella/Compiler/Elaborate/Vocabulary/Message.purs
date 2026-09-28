-- | What a synthesizer says when it fails or warns, and what the host keeps of
-- | it.
-- |
-- | **A synthesizer builds a message over the handles it holds, and the host
-- | freezes it where it is said.** A frozen part holds a value, the type zonked
-- | against `Ψ` as it was then and the term with the type it was claimed at, and
-- | never a handle: a handle is invalid once its attempt ends, and a message
-- | resolved later would show whatever `Ψ` came to hold instead of what the
-- | synthesizer saw. A report never changes after it is made.
-- |
-- | A report is data, not text: the text an author wrote is kept as they wrote
-- | it, and what the host adds is structured, so that one report can be shown by
-- | whatever shows it.
module Stella.Compiler.Elaborate.Vocabulary.Message
  ( MessagePart(..)
  , FrozenMessagePart(..)
  , GoalSummary
  ) where

import Prelude

import Stella.Compiler.Elaborate.CorePlus.Context (Origin)
import Stella.Compiler.Elaborate.Vocabulary.Handle (Handle)
import Stella.Compiler.Elaborate.Mechanism.Kinding (KindEvidence)
import Stella.Compiler.Elaborate.Mechanism.Pending (PendingId, SynthRef)
import Stella.Compiler.Elaborate.CorePlus.Term (XExpr)
import Stella.Compiler.Elaborate.CorePlus.Type (XType)
import Stella.Compiler.TypedCore (Ident, Qualified)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- | A part of a message as a synthesizer builds it.
data MessagePart
  -- | Text the author wrote.
  = TextPart String
  -- | A type the synthesizer holds.
  | TypePart Handle
  -- | A term the synthesizer holds.
  | TermPart Handle
  -- | A name, as the catalog has it.
  | NamePart (Qualified Ident)

-- | A part of a message as the host keeps it.
data FrozenMessagePart
  = FrozenText String
  | FrozenType { type :: XType, kind :: KindEvidence }
  | FrozenTerm { term :: XExpr Unit, claimed :: XType }
  | FrozenName (Qualified Ident)

-- | The goal a report is about: where it stands, the job running it, the
-- | synthesizer it was asked of, and the type it was asked at, zonked where the
-- | report was made.
type GoalSummary =
  { origin :: Origin
  , pending :: PendingId
  , synthesizer :: SynthRef
  , expectedType :: XType
  }

derive instance Eq MessagePart
derive instance Generic MessagePart _

instance Show MessagePart where
  show x = genericShow x

derive instance Eq FrozenMessagePart
derive instance Generic FrozenMessagePart _

instance Show FrozenMessagePart where
  show x = genericShow x
