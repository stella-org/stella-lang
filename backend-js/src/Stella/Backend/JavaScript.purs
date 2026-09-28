-- | The JavaScript backend: a `.dmo` in, an ES module out (D45).
-- |
-- | It reads the module a decoder returns and nothing beside it, so what it finds
-- | missing is missing from the format
-- | ([JavaScript](../../../../docs/technical-references/05-Backend/05-JavaScript.md)).
-- | The path is `.dmo` → a resolved module cut into segments (Frame IR, the lower
-- | IR of the frame strategy) → the JavaScript syntax every strategy shares → text.
-- |
-- | **A module handed across without its bytes is accepted exactly where an encoder
-- | would write it.** What an encoder refuses is not only the structure a decoder
-- | reads but text no reader may read, so the module is run through the encoder
-- | itself, whose bytes are then dropped: one walk decides both routes, and they
-- | cannot come to accept different modules. What a loader establishes of one
-- | module is checked next, before any code is generated
-- | ([Check](JavaScript/Check.purs)).
-- |
-- | **This is the package's whole interface.** The resolved module, Frame IR, and
-- | the JavaScript syntax are its own and change with the strategy; what a caller
-- | depends on is a `.dmo` in, text out, and the file that text is written to.
module Stella.Backend.JavaScript
  ( module Exported
  , generate
  ) where

import Prelude

import Prim as P

import Data.Either (Either(..))
import Stella.Compiler.Bytecode.Encode (encode)
import Stella.Compiler.Bytecode.Module (Dmo)
import Stella.Backend.JavaScript.Check (check)
import Stella.Backend.JavaScript.Emit (Options)
import Stella.Backend.JavaScript.Emit (Options, fileName) as Exported
import Stella.Backend.JavaScript.Emit (emit) as E
import Stella.Backend.JavaScript.Error (JsError(..))
import Stella.Backend.JavaScript.Error (JsError(..)) as Exported
import Stella.Backend.JavaScript.Syntax (print)
import Stella.Backend.JavaScript.ToFrame (toFrame)

generate :: Options -> Dmo -> Either JsError P.String
generate options dmo = do
  case encode dmo of
    Left refusal -> Left (NotEncodable refusal)
    Right _ -> Right unit
  check dmo
  fm <- toFrame dmo
  out <- E.emit options fm
  pure (print out)
