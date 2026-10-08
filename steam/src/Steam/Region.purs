-- | The identity of a region
-- | ([Abstract Machine](../../../docs/technical-references/07-Runtime/01-Abstract-Machine.md)).
-- |
-- | Opening a region gives it an identity unequal to every other opening's, and a
-- | copy a continuation makes of the region's frame keeps it. A cell is reached by
-- | the identity and a position, so what a read or a write reaches is the innermost
-- | frame of that identity on the stack.
-- |
-- | An identity reaches the registers as a `VOpaque`, as an array does, and nothing
-- | outside this module takes one apart. Typing keeps one inside Stella code: no
-- | foreign is handed one.
module Steam.Region
  ( fresh
  , same
  , fromOpaque
  , toOpaque
  ) where

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Prim as P
import Steam.Value (Opaque, RegionId)
import Unsafe.Coerce (unsafeCoerce)

-- | An identity no opening has had.
foreign import fresh :: Effect RegionId

foreign import same :: RegionId -> RegionId -> P.Boolean

-- | Whether an opaque value is an identity, by the brand it carries.
foreign import isRegion :: Opaque -> P.Boolean

fromOpaque :: Opaque -> Maybe RegionId
fromOpaque o = if isRegion o then Just (unsafeCoerce o) else Nothing

toOpaque :: RegionId -> Opaque
toOpaque = unsafeCoerce
