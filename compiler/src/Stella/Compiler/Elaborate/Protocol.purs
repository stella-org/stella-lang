-- | What identifies a conversation a runner holds with a synthesizer, and a
-- | transaction inside one.
-- |
-- | A synthesizer running apart from the host asks for one thing at a time, so
-- | an attempt is held open across its requests as a conversation, and a
-- | `transact` is opened and closed by requests of their own. Each request
-- | names the conversation it belongs to and the transaction the synthesizer
-- | believes it stands in, innermost, and the host holds it to both: a request
-- | arriving late from an attempt that has ended, or one continuing inside a
-- | transaction the host has already rolled back, names what the host does not
-- | hold.
-- |
-- | **Neither is ever issued twice.** A conversation's identifier is drawn from a
-- | counter no rollback restores, and a transaction's is that conversation's and
-- | a number drawn from a counter the conversation holds, which no rollback
-- | restores either: a transaction a failure closed is never confused with the
-- | next one opened.
module Stella.Compiler.Elaborate.Protocol
  ( ConversationId(..)
  , TransactionToken(..)
  , Envelope
  ) where

import Prelude

import Prim as P

import Data.Maybe (Maybe)

newtype ConversationId = ConversationId P.Int

-- | What a request carries beside what it asks: the conversation it belongs to,
-- | and the transaction the synthesizer stands in, innermost, if any.
type Envelope =
  { conversation :: ConversationId
  , transaction :: Maybe TransactionToken
  }

newtype TransactionToken = TransactionToken
  { conversation :: ConversationId
  , serial :: P.Int
  }

derive instance Eq ConversationId
derive instance Ord ConversationId
derive newtype instance Show ConversationId

derive instance Eq TransactionToken
derive newtype instance Show TransactionToken
