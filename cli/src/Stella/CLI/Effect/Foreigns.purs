-- | Reaching the implementations a manifest points at.
-- |
-- | **The operation is "reach this entry" and not "import an ES module"**, and the
-- | level matters. A manifest's payload belongs to the target it names
-- | ([Foreign Manifest](../../../../docs/technical-references/05-Backend/04-Foreign-Manifest.md)),
-- | so what a specifier is, and what reaching one means, is the handler's — on a
-- | native target there is no import to speak of and the payload is something else
-- | entirely. Naming the mechanism here would have fixed one target in a place that
-- | exists to be open to the next.
-- |
-- | **What comes back is opaque.** A host value has no type this package can give
-- | it, and the interpreter that asked is the one that knows what it wants it to be.
module Stella.CLI.Effect.Foreigns
  ( HostExport
  , Foreigns(..)
  , FOREIGNS
  , _foreigns
  , interpret
  , reach
  ) where

import Prelude

import Data.Either (Either)
import Data.Map (Map)
import Prim as P
import Run (Run)
import Run as Run
import Stella.Compiler.ForeignManifest (ManifestEntry)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))

-- | A value the host supplied, of a type nothing here can name.
foreign import data HostExport :: P.Type

-- | **A failure is answered rather than thrown**, as with reading a file: what a
-- | command makes of implementations it could not reach is the command's.
-- |
-- | `base` is the directory the manifest was read from, which is what a payload's
-- | relative parts are resolved against — the one base that makes a manifest mean
-- | the same thing wherever it is read from.
data Foreigns a = Reach
  { base :: P.String
  , entry :: ManifestEntry
  }
  (Either P.String (Map P.String HostExport) -> a)

derive instance Functor Foreigns

type FOREIGNS r = (foreigns :: Foreigns | r)

_foreigns :: Proxy "foreigns"
_foreigns = Proxy

interpret :: forall r a. (Foreigns ~> Run r) -> Run (FOREIGNS + r) a -> Run r a
interpret handler = Run.interpret (Run.on _foreigns handler Run.send)

-- | What that entry's module exports, by name, or what the target said about not
-- | reaching it.
-- |
-- | **Reaching the same entry twice is not twice the work**, which is the handler's
-- | to honour: a session pays once per host module however many Stella modules
-- | declare against it.
reach
  :: forall r
   . P.String
  -> ManifestEntry
  -> Run (FOREIGNS + r) (Either P.String (Map P.String HostExport))
reach base entry = Run.lift _foreigns (Reach { base, entry } identity)
