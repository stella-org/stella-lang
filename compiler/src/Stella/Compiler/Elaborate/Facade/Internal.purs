-- | The representation of a host script, for the driver that runs one and the
-- | tests that inspect one.
-- |
-- | A synthesizer reaches none of this: it builds scripts from the operations
-- | `Facade` exports, each of which makes its own request and takes back its
-- | own shape of answer, so that nothing a synthesizer writes can make a
-- | request with an answer another shape than the host gives it.
module Stella.Compiler.Elaborate.Facade.Internal
  ( Facade(..)
  , transact
  , kernel
  ) where

import Prelude

import Stella.Compiler.Elaborate.Diagnostic (Diagnostic)
import Stella.Compiler.Elaborate.Request (KernelAnswer, KernelRequest)
import Data.Either (Either(..))
import Data.Maybe (Maybe)

-- | A script ending in an `a`.
data Facade a
  = Pure a
  -- | Make the request, and go on with its answer where it is in the shape the
  -- | request is answered in, `Nothing` being any other.
  | Ask KernelRequest (KernelAnswer -> Maybe (Facade a))
  -- | Run the body inside a transaction: where it ends, the transaction commits
  -- | and the script goes on as the body says; where a failure is answered
  -- | inside it, the script goes on with the diagnostic instead.
  | Transact (Facade (Facade a)) (Diagnostic -> Facade a)

instance Functor Facade where
  map f = case _ of
    Pure a -> Pure (f a)
    Ask request next -> Ask request (map (map f) <<< next)
    Transact body onFailure -> Transact (map (map f) body) (map f <<< onFailure)

instance Apply Facade where
  apply = ap

instance Applicative Facade where
  pure = Pure

instance Bind Facade where
  bind script f = case script of
    Pure a -> f a
    Ask request next -> Ask request (map (_ >>= f) <<< next)
    Transact body onFailure -> Transact (map (_ >>= f) body) (\d -> onFailure d >>= f)

instance Monad Facade

-- | Try the script given: its result, or the failure that ended it, with what it
-- | did rolled back.
transact :: forall a. Facade a -> Facade (Either Diagnostic a)
transact body = Transact (map (pure <<< Right) body) (pure <<< Left)

-- | Make the request given, and take back the answer the function given
-- | accepts.
kernel :: forall a. KernelRequest -> (KernelAnswer -> Maybe a) -> Facade a
kernel request accepted = Ask request (map Pure <<< accepted)
