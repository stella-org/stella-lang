-- | The source files a command is given, as `--workdir` and `--src` name them:
-- | the files the patterns name under the directory `--workdir` names, and
-- | `src/**/*.stel` where no pattern is given.
module Stellac.Sources (underRoot, sourceFiles) where

import Prelude

import Data.Array as Array
import Data.Either (either)
import Data.String (Pattern(..), joinWith, split)
import Fmt (fmt)
import Run (Run)
import Run.Except (EXCEPT, throw)
import Stella.CLI.Effect.FS (FS, FilePath)
import Stella.CLI.Effect.FS as FS
import Stella.Compiler.Build (PackageFile)
import Type.Row (type (+))

-- | A path given from the directory given, under that directory.
underRoot :: FilePath -> FilePath -> FilePath
underRoot root path
  | root == "." = path
  | otherwise = fmt @"{root}/{path}" { root, path }

-- | The files the patterns given name under the root given, in order; where
-- | they name none, or the files cannot be listed, it fails.
sourceFiles :: forall r. FilePath -> Array String -> Run (FS + EXCEPT String + r) (Array PackageFile)
sourceFiles root given = do
  found <- FS.glob root patterns >>= either (\why -> throw (fmt @"The source files could not be listed: {why}" { why })) pure
  when (Array.null found) do
    throw (fmt @"No source file matches {patterns}" { patterns: joinWith ", " patterns })
  pure (map (\within -> { path: underRoot root within, within: split (Pattern "/") within }) found)
  where
  patterns = if Array.null given then [ "src/**/*.stel" ] else given
