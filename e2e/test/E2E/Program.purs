-- | What the package manager does between `stellac compile` and `steam run`,
-- | done here until there is one: the program descriptor of an entry module,
-- | from the `output.json` of every build the program draws on.
module Test.E2E.Program
  ( programFrom
  , statedSeeds
  ) where

import Prelude

import Data.Argonaut.Core (Json, fromArray, fromObject, fromString)
import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.String as String
import Data.Traversable (for, sequence)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Foreign.Object as Object
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Aff as FS
import Node.Process as Process
import Stella.Compiler.Bytecode (decode) as Bytecode
import Stella.Compiler.ForeignManifest (ResultKind(..), kindSpelling)
import Stella.Compiler.Interface.File as Interface
import Stella.Compiler.ProgramDescriptor as ProgramDescriptor
import Stella.Compiler.TypedCore (Ident, ModuleName(..), Qualified(..))
import Stella.Compiler.TypedCore.Prim (primModule)
import Stellac.Config (normalize, relativeSpecifier)
import Stellac.Output (Supplying)
import Stellac.Output as Output
import Stellac.Paths (relativeTo)

type Module =
  { object :: String
  , imports :: Array ModuleName
  , entrypoint :: Maybe Ident
  , supplied :: Maybe { target :: String, supplying :: Supplying, directory :: String }
  }

-- | The `output.json` of the seed modules `stella-devtools build-seeds` wrote
-- | to the directory given, which states nothing of them as `stellac compile`
-- | does.
statedSeeds :: String -> Array String -> Aff (Either String Unit)
statedSeeds directory names = do
  built <- for names \n -> do
    dmi <- bytesOf (directory <> "/" <> n <> ".dmi")
    dmo <- bytesOf (directory <> "/" <> n <> ".dmo")
    pure do
      stored <- lmap show (Interface.decode dmi)
      object <- lmap show (Bytecode.decode dmo)
      pure { module: ModuleName n, interface: n <> ".dmi", object: n <> ".dmo", imports: object.imports, entrypoint: stored.interface.entrypoint }
  case sequence built of
    Left why -> pure (Left why)
    Right modules -> Right <$> FS.writeTextFile UTF8 (directory <> "/output.json") (Output.encode { modules, foreign: Nothing })
  where
  bytesOf path = FS.readFile path >>= liftEffect <<< Buffer.toArray

programFrom :: { outputs :: Array String, entry :: String, at :: String } -> Aff (Either String Unit)
programFrom p = do
  here <- liftEffect Process.cwd
  let absolute path = normalize (if String.take 1 path == "/" then path else here <> "/" <> path)
  read <- for p.outputs \file -> do
    text <- FS.readTextFile UTF8 file
    pure (Tuple (directoryOf (absolute file)) (Output.decode text))
  let descriptorDirectory = directoryOf (absolute p.at)
  case gathered read of
    Left why -> pure (Left why)
    Right modules -> case program descriptorDirectory modules of
      Left why -> pure (Left why)
      Right text -> Right <$> FS.writeTextFile UTF8 p.at text
  where
  entry = ModuleName p.entry

  gathered read = foldM add Map.empty read
    where
    add acc (Tuple directory decoded) = case decoded of
      Left err -> Left ("an `output.json` does not read: " <> show err)
      Right output -> Right (Map.union acc (Map.fromFoldable (map (\b -> Tuple b.module (described directory output b)) output.modules)))

  described directory output b =
    { object: directory <> "/" <> b.object
    , imports: Array.filter (_ /= primModule) b.imports
    , entrypoint: b.entrypoint
    , supplied: output.foreign >>= \f -> (\s -> { target: f.target, supplying: s, directory }) <$> Array.find (\s -> s.module == b.module) f.modules
    }

  program :: String -> Map ModuleName Module -> Either String String
  program directory modules = do
    closure <- (_.order) <$> visit [] { done: Set.empty, order: [] } entry
    global <- maybe (Left ("`" <> p.entry <> "` has no entry point")) Right (Map.lookup entry modules >>= _.entrypoint)
    let supplied = Array.mapMaybe (\(Tuple _ m) -> m.supplied) closure
    foreign' <- case Array.nub (map _.target supplied) of
      [] -> Right Nothing
      [ target ] -> Right (Just (manifest directory target supplied))
      _ -> Left "the modules the program runs are supplied for several targets"
    pure $ ProgramDescriptor.print
      { entry: Qualified entry global
      , modules: map (\(Tuple name m) -> { module: name, object: relativeTo directory m.object }) closure
      , foreign: foreign'
      }
    where
    visit :: Array ModuleName -> { done :: Set ModuleName, order :: Array (Tuple ModuleName Module) } -> ModuleName -> Either String { done :: Set ModuleName, order :: Array (Tuple ModuleName Module) }
    visit taking acc m
      | Set.member m acc.done = Right acc
      | Array.elem m taking = Left ("the bytecode of these modules imports one another: " <> String.joinWith ", " (map nameOf (Array.dropWhile (_ /= m) taking)))
      | otherwise = case Map.lookup m modules of
          Nothing -> Left ("no `output.json` states `" <> nameOf m <> "`")
          Just found -> do
            after <- foldM (visit (Array.snoc taking m)) acc found.imports
            pure { done: Set.insert m after.done, order: Array.snoc after.order (Tuple m found) }

  -- a relative specifier keeps what it refers to, from the descriptor's directory
  manifest :: String -> String -> Array { target :: String, supplying :: Supplying, directory :: String } -> Json
  manifest directory target supplied = fromObject $ Object.fromFoldable
    [ Tuple "target" (fromString target)
    , Tuple "modules" $ fromArray $ supplied <#> \s -> fromObject $ Object.fromFoldable
        [ Tuple "module" (fromString (nameOf s.supplying.module))
        , Tuple "specifier" (fromString (moved s.directory s.supplying.specifier))
        , Tuple "foreigns" $ fromArray $ s.supplying.foreigns <#> \f -> fromObject $ Object.fromFoldable
            [ Tuple "name" (fromString f.name)
            , Tuple "params" (fromArray (map (fromString <<< kindSpelling) f.params))
            , Tuple "result" case f.result of
                AsValue k -> fromString (kindSpelling k)
                AsAction k -> fromObject (Object.singleton "action" (fromString (kindSpelling k)))
            ]
        ]
    ]
    where
    moved from specifier
      | relativeSpecifier specifier = case relativeTo directory (normalize (from <> "/" <> specifier)) of
          path | String.take 3 path == "../" -> path
          path -> "./" <> path
      | otherwise = specifier

nameOf :: ModuleName -> String
nameOf (ModuleName n) = n

directoryOf :: String -> String
directoryOf path = maybe "." (\i -> String.take i path) (String.lastIndexOf (String.Pattern "/") path)
