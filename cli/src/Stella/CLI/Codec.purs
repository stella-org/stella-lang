module Stella.CLI.Codec
  ( exactly
  , nonEmpty
  , moduleName
  ) where

import Prelude

import Data.Array as Array
import Data.Codec as Codec
import Data.Codec.Argonaut (JsonCodec, JsonDecodeError(..))
import Data.Codec.Argonaut as CA
import Data.Codec.Argonaut.Record as CAR
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Data.String.CodeUnits as SCU
import Foreign.Object as Object
import Prim.RowList as RL
import Record.Extra (class Keys, keys)
import Stella.Compiler.TypedCore (ModuleName(..))

-- | A codec for objects with exactly the fields given by the second argument/
-- | Unlike `Data.Codec.Argonaut.object`, this codec will refuse inputs with
-- | extra fields.
exactly
  :: forall ri ro rl
   . RL.RowToList ri rl
  => CAR.RowListCodec rl ri ro
  => Keys rl
  => String
  -> Record ri
  -> JsonCodec (Record ro)
exactly name codecs = Codec.codec' decoded (Codec.encode object)
  where
  object = CAR.object name codecs
  taken = Array.fromFoldable (keys codecs)
  decoded json = do
    fields <- Codec.decode CA.jobject json
    case Array.find (\k -> not (Array.elem k taken)) (Array.sort (Object.keys fields)) of
      Just other -> Left (Named name (AtKey other (UnexpectedValue (fromMaybe json (Object.lookup other fields)))))
      Nothing -> Codec.decode object json

nonEmpty :: JsonCodec String
nonEmpty = CA.prismaticCodec "NonEmptyString" (\s -> if s == "" then Nothing else Just s) identity CA.string

moduleName :: JsonCodec ModuleName
moduleName = CA.prismaticCodec "ModuleName" named (\(ModuleName m) -> m) CA.string
  where
  named m = if Array.all isProperName (String.split (String.Pattern ".") m) then Just (ModuleName m) else Nothing

-- | A segment of a module's name: an upper case letter, then letters, digits,
-- | `_`, and `'`.
isProperName :: String -> Boolean
isProperName segment = case SCU.uncons segment of
  Just { head, tail } -> isUpper head && Array.all isNameChar (SCU.toCharArray tail)
  Nothing -> false
  where
  isUpper c = c >= 'A' && c <= 'Z'
  isNameChar c = c >= 'a' && c <= 'z' || isUpper c || c >= '0' && c <= '9' || c == '_' || c == '\''
