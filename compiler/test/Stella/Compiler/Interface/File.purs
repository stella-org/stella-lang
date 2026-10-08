-- | The `.dmi` file: an interface carried through its bytes and back, the bytes
-- | one interface has, and what each direction refuses.
module Test.Stella.Compiler.Interface.File (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Char as Char
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set as Set
import Data.String.CodeUnits as CodeUnits
import Data.Tuple (Tuple(..))
import Stella.Compiler.Bytecode.Bytes (Bytes, DecodeError(..), EncodeError(..), TableKind(..), TagKind(..), utf8)
import Stella.Compiler.Interface.File (StoredInterface, decode, encode)
import Stella.Compiler.Interface.Module (ModuleInterface, TypeEntity(..), TypeSort(..), ValueSort(..), Via(..), emptyDeclarations, emptyExports)
import Stella.Compiler.TypedCore.Decl (Constant(..))
import Stella.Compiler.Interface.Scheme (SchemeBody(..))
import Stella.Compiler.Surface.Decl (Associativity(..), FixityTarget(..), Observation(..))
import Stella.Compiler.Surface.Name (OperatorName(..))
import Stella.Compiler.Surface.Type (TypeOperatorTarget(..))
import Stella.Compiler.TypedCore.Domain (scalarString, scalarValue)
import Stella.Compiler.TypedCore.Kind (Kind(..), RowElemKind(..), monoScheme)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), KindVar(..), ModuleName(..), Qualified(..), RegionName(..), Symbol(..), Tag(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (intTy)
import Stella.Compiler.TypedCore.Signature (CanonicalClass(..))
import Stella.Compiler.TypedCore.Term (Literal(..))
import Stella.Compiler.TypedCore.Type (Constraint(..), RowEntry(..), RowKey(..), Type(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

moduleM :: ModuleName
moduleM = ModuleName "M"

inM :: forall a. a -> Qualified a
inM = Qualified moduleM

int :: Type
int = TCon intTy []

-- | An interface holding something of every form a file carries.
rich :: ModuleInterface
rich =
  { name: moduleM
  , imports: [ ModuleName "A", ModuleName "B" ]
  , exports:
      { values: Map.fromFoldable
          [ Tuple "f" { entity: inM (Ident "f"), via: Declared }
          , Tuple "x" { entity: Qualified (ModuleName "A") (Ident "x"), via: ThroughImport (ModuleName "A") }
          ]
      , types: Map.fromFoldable
          [ Tuple "T" { entity: TypeEntity (inM (TyName "T")), via: Declared, members: [ Ident "Leaf", Ident "Node" ] }
          , Tuple "E" { entity: EffectEntity (inM (EffName "E")), via: Declared, members: [ Ident "get" ] }
          ]
      , operators: Map.singleton "+++" { entity: inM (OperatorName "+++"), via: Declared }
      , typeOperators: Map.singleton "***" { entity: inM (OperatorName "***"), via: Declared }
      , macros: Map.singleton "m" { entity: inM (Ident "m"), via: Declared }
      , attributes: Map.singleton "json" { entity: inM (Ident "json"), via: Declared }
      , modules: [ ModuleName "B" ]
      }
  , declarations:
      { values: Map.fromFoldable
          [ Tuple (Ident "f") { sort: SortValue, scheme: { kindVars: [ KindVar "k" ], body: scheme }, attributes: [ attribute ] }
          , Tuple (Ident "c") { sort: SortValue, scheme: { kindVars: [], body: Computation int row }, attributes: [] }
          , Tuple (Ident "sqrt") { sort: SortForeign ObservesNone, scheme: plain, attributes: [] }
          , Tuple (Ident "h") { sort: SortHandler, scheme: plain, attributes: [] }
          , Tuple (Ident "Leaf") { sort: SortConstructor (inM (TyName "T")), scheme: plain, attributes: [] }
          , Tuple (Ident "get") { sort: SortOperation (inM (EffName "E")), scheme: plain, attributes: [] }
          ]
      , types: Map.fromFoldable
          [ Tuple (TyName "T")
              { kind: { kindVars: [], body: KFun KType KType }
              , sort: DataType { params: [ { name: a, kind: KType } ], constructors: [ { name: Ident "Leaf", fields: [] }, { name: Ident "Node", fields: [ TVar a, int ] } ], isNewtype: false }
              , attributes: []
              }
          , Tuple (TyName "S") { kind: monoScheme (KRow RowEffect), sort: Synonym { params: [], body: row }, attributes: [] }
          , Tuple (TyName "Ref") { kind: monoScheme (KFun KType KType), sort: ForeignType, attributes: [] }
          , Tuple (TyName "Raw") { kind: monoScheme KType, sort: Intrinsic CanonicalOpaque, attributes: [] }
          ]
      , effects: Map.singleton (EffName "E")
          { params: [ { name: a, kind: KType } ]
          , operations: [ { name: Ident "get", binders: [ { name: TyVar "b", kind: KType } ], arguments: [ int ], resumesWith: TVar a } ]
          , attributes: []
          }
      , operators: Map.singleton (OperatorName "+++") { associativity: AssociateLeft, precedence: 6, target: FixityValue (inM (Ident "f")) }
      , typeOperators: Map.singleton (OperatorName "***") { associativity: AssociateRight, precedence: 0, target: TargetTypeSynonym (inM (TyName "S")) }
      , attributes: Map.singleton (Ident "json")
          { positional: [ int ]
          , keyword: [ { label: "name", type: int, default: Nothing }, { label: "level", type: int, default: Just (ConstantLiteral (LitInt 3)) } ]
          }
      }
  , implicitHandlers: [ { handler: Ident "h", source: RowEffectEntry (inM (EffName "E")) [ int ], targets: [ RowLabelledEffectEntry (Symbol "log") (inM (EffName "E")) [] ] } ]
  , catalogOnly: Set.fromFoldable [ Ident "hidden", Ident "secret" ]
  , arities: Map.fromFoldable [ Tuple (Ident "f") 2, Tuple (Ident "h") 1 ]
  }
  where
  a = TyVar "a"
  plain = { kindVars: [], body: Plain int }
  row = TRowExtend (RowEffectEntry (inM (EffName "E")) [ int ]) (TRowUnion (TVar (TyVar "e")) TRowEmpty)
  scheme =
    Forall a (KVar (KindVar "k"))
      ( Constrained (Lacks (EffectKey (inM (EffName "E"))) (TVar (TyVar "e")))
          ( Constrained (Disjoint (TVar (TyVar "e")) TRowEmpty)
              ( Synthesized { name: Just (Ident "d"), dictionary: TApp (TCon (inM (TyName "T")) [ KType ]) (TVar a), synthesizer: inM (Ident "resolve") }
                  ( Plain
                      ( TForall (TyVar "r") (KRow RowType)
                          ( TRowExtend (RowTypeEntry (SymbolKey (Symbol "s")) int)
                              (TRowExtend (RowTypeEntry (TagKey (Tag "Ok")) int) (TRowExtend (RowTypeEntry (PositionKey 1) int) TRowEmpty))
                          )
                      )
                  )
              )
          )
      )
  attribute =
    { name: inM (Ident "json")
    , positional: [ ConstantConstructor (inM (Ident "Node")) [ ConstantValue (inM (Ident "f")), ConstantRecord [ { label: Symbol "n", value: ConstantLiteral (LitNumber 1.5) } ] ] ]
    , keyword:
        [ { label: "name", value: stringConstant "u" }
        , { label: "level", value: charConstant 0x1F600 }
        ]
    }

stringConstant :: P.String -> Constant
stringConstant s = case scalarString s of
  Just v -> ConstantLiteral (LitString v)
  Nothing -> ConstantLiteral (LitInt 0)

charConstant :: P.Int -> Constant
charConstant c = case scalarValue c of
  Just v -> ConstantLiteral (LitChar v)
  Nothing -> ConstantLiteral (LitBoolean true)

empty :: ModuleInterface
empty =
  { name: moduleM
  , imports: []
  , exports: emptyExports
  , declarations: emptyDeclarations
  , implicitHandlers: []
  , catalogOnly: Set.empty
  , arities: Map.empty
  }

stored :: ModuleInterface -> StoredInterface
stored i = { interface: i, buildHash: Nothing }

bytesOf :: StoredInterface -> Bytes
bytesOf s = case encode s of
  Left _ -> []
  Right bytes -> bytes

-- | The header a file of this format and ABI version begins with.
header :: Bytes
header = [ 0x44, 0x4D, 0x49, 0x00, 0x00, 0x00 ] <> text "stella-base-0.1"

text :: P.String -> Bytes
text s = case utf8 s of
  Right bytes -> [ Array.length bytes ] <> bytes
  Left _ -> []

-- | A file of module `M` whose string table holds the strings given after `M`,
-- | with the sections given in place of the empty ones of the same id.
file :: P.Array P.String -> P.Array (Tuple P.Int Bytes) -> Bytes
file extra replaced = header <> section 0x01 ([ Array.length ss ] <> Array.concatMap text ss) <> Array.concatMap one ids
  where
  ss = [ "M" ] <> extra
  ids = Array.range 0x02 0x0D
  one id = section id (fromMaybe (emptyOf id) (map (\(Tuple _ b) -> b) (Array.find (\(Tuple i _) -> i == id) replaced)))
  emptyOf id
    | id == 0x02 = [ 0x00 ]
    | id == 0x04 = [ 0, 0, 0, 0, 0, 0, 0 ]
    | otherwise = [ 0x00 ]

section :: P.Int -> Bytes -> Bytes
section id payload = [ id, Array.length payload ] <> payload

astral :: P.String
astral = "😀"

privateUse :: Maybe P.String
privateUse = map CodeUnits.singleton (Char.fromCharCode 0xE000)

loneSurrogate :: Maybe P.String
loneSurrogate = map CodeUnits.singleton (Char.fromCharCode 0xD800)

indexOfBytes :: Bytes -> Bytes -> Maybe P.Int
indexOfBytes needle haystack = go 0
  where
  go i
    | i + Array.length needle > Array.length haystack = Nothing
    | Array.slice i (i + Array.length needle) haystack == needle = Just i
    | otherwise = go (i + 1)

spec :: Spec Unit
spec = describe "Stella.Compiler.Interface.File" do
  describe "an interface" do
    it "is carried through its bytes and back, a build hash with it where it has one" do
      decode (bytesOf (stored rich)) `shouldEqual` Right (stored rich)
      decode (bytesOf { interface: rich, buildHash: Just [ 1, 2, 3 ] }) `shouldEqual` Right { interface: rich, buildHash: Just [ 1, 2, 3 ] }
      decode (bytesOf (stored empty)) `shouldEqual` Right (stored empty)

    it "has one file, its maps written by the scalar values of their keys" do
      case privateUse of
        Nothing -> fail "a code unit is the only way to write one"
        Just name -> do
          let
            two = empty { arities = Map.fromFoldable [ Tuple (Ident astral) 1, Tuple (Ident name) 2 ] }
            bytes = bytesOf (stored two)
          (indexOfBytes [ 0xEE, 0x80, 0x80 ] bytes < indexOfBytes [ 0xF0, 0x9F, 0x98, 0x80 ] bytes) `shouldEqual` true
          decode bytes `shouldEqual` Right (stored two)

  describe "the bytes" do
    it "begin with the magic, the format version, the flags, and the ABI version" do
      Array.take (Array.length header) (bytesOf (stored empty)) `shouldEqual` header

    it "of an empty interface are the string table and every section, empty" do
      bytesOf (stored empty) `shouldEqual` file [] []

  describe "what a reader refuses" do
    it "other magic, another format version, unknown flags, and another ABI version" do
      decode [ 0x44, 0x4D, 0x4F, 0x00 ] `shouldEqual` Left BadMagic
      decode ([ 0x44, 0x4D, 0x49, 0x00, 0x01 ] <> Array.drop 5 (file [] [])) `shouldEqual` Left (UnsupportedFormatVersion 1)
      decode ([ 0x44, 0x4D, 0x49, 0x00, 0x00, 0x01 ] <> Array.drop 6 (file [] [])) `shouldEqual` Left (UnknownFlags 1)
      decode ([ 0x44, 0x4D, 0x49, 0x00, 0x00, 0x00 ] <> text "other" <> Array.drop (Array.length header) (file [] []))
        `shouldEqual` Left (UnknownAbiVersion "other")

    it "a section missing, or one it does not know below the boundary" do
      decode (Array.take (Array.length (file [] []) - 3) (file [] [])) `shouldEqual` Left (SectionMissing 0x0D)
      decode (file [] [] <> section 0x20 []) `shouldEqual` Left (UnknownSection 0x20)

    it "nothing it does not know at or above the boundary, which it skips" do
      decode (file [] [] <> section 0x71 [ 9, 9 ]) `shouldEqual` Right (stored empty)

    it "a tag it does not know, and an index outside the string table" do
      -- a value `f` of a plain scheme whose type carries the tag 9
      decode (file [ "f" ] [ Tuple 0x05 [ 1, 1, 0, 0, 0, 9 ] ]) `shouldEqual` Left (UnknownTag TypeTag 9)
      decode (file [] [ Tuple 0x02 [ 5 ] ]) `shouldEqual` Left (IndexOutOfRange StringTable 5)

    it "an arity below one, and a map whose keys do not ascend" do
      decode (file [ "f" ] [ Tuple 0x0D [ 1, 1, 0 ] ]) `shouldEqual` Left (ArityNotPositive 0)
      decode (file [ "b", "a" ] [ Tuple 0x0D [ 2, 1, 1, 2, 1 ] ]) `shouldEqual` Left EntriesOutOfOrder
      decode (file [ "a" ] [ Tuple 0x0D [ 2, 1, 1, 1, 1 ] ]) `shouldEqual` Left EntriesOutOfOrder

  describe "what an encoder refuses" do
    it "an arity below one, a count below zero, and a name no reader could read" do
      encode (stored empty { arities = Map.singleton (Ident "f") 0 }) `shouldEqual` Left (ArityBelowOne (Ident "f") 0)
      encode (stored empty { declarations = emptyDeclarations { operators = Map.singleton (OperatorName "+") { associativity: AssociateLeft, precedence: -1, target: FixityValue (inM (Ident "f")) } } })
        `shouldEqual` Left (CountBelowZero (-1))
      case loneSurrogate of
        Nothing -> fail "a code unit is the only way to write one"
        Just name -> encode (stored empty { arities = Map.singleton (Ident name) 1 }) `shouldEqual` Left (NotScalarText name)

    it "a region name, which no published scheme mentions" do
      encode (stored empty { implicitHandlers = [ { handler: Ident "h", source: RowRegionEntry (RegionName "r"), targets: [] } ] })
        `shouldEqual` Left (RegionInInterface (RegionName "r"))
