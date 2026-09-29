-- | Reading what a command was pointed at.
-- |
-- | **The operation is an effect rather than a call into the host**, for the same
-- | reason logging is: a command's logic should say what it needs and not where it
-- | runs. A Node interpreter is one handler, and a command compiled for somewhere
-- | else needs another handler rather than a different command.
-- |
-- | What crosses the boundary is `Bytes` and not a host buffer, so nothing above
-- | this module names a representation the host chose.
module Stella.CLI.Effect.FS
  ( FS
  , FilePath
  , FileSystem(..)
  , _fs
  , interpret
  , readBytes
  , readText
  )
  where

import Prelude

import Data.Either (Either)
import Prim as P
import Run (Run)
import Run as Run
import Stella.Compiler.Bytecode.Bytes (Bytes)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))

type FilePath = P.String

-- | **A failure is answered rather than thrown.** What a command makes of a file
-- | it could not read is the command's — one may refuse, another may go on — so the
-- | effect reports and does not decide.
data FileSystem a
  = ReadBytes P.String (Either P.String Bytes -> a)
  -- | The same file as text. **Two operations and not one with a decoding above
  -- | it**: what an encoding is belongs to the host, and a caller that wanted text
  -- | should not have to know which one this host writes.
  | ReadText P.String (Either P.String P.String -> a)

derive instance Functor FileSystem

type FS r = (fs :: FileSystem | r)

_fs :: Proxy "fs"
_fs = Proxy

interpret :: forall r a. (FileSystem ~> Run r) -> Run (FS + r) a -> Run r a
interpret handler = Run.interpret (Run.on _fs handler Run.send)

-- | The bytes of that file, or what the host said about not giving them.
readBytes :: forall r. P.String -> Run (FS + r) (Either P.String Bytes)
readBytes path = Run.lift _fs (ReadBytes path identity)

readText :: forall r. P.String -> Run (FS + r) (Either P.String P.String)
readText path = Run.lift _fs (ReadText path identity)

