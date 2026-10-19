-- | Declarations and the signature a module contributes.
-- |
-- | The cases the Implementation Plan singles out are here: D23 on both sides
-- | of an arrow, the shape a `newtype` claims, and the dependency order of
-- | value declarations.
module Test.Stella.Compiler.TypedCore.Declare (spec) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore (Constraint(..), CtorDecl, Decl(..), EffName(..), OpDecl, TyBinder, Export(..), Expr(..), Ident(..), Kind(..), KindVar(..), Literal(..), Module, ModuleName(..), OpName(..), Qualified(..), RowElemKind(..), RowEntry(..), RowKey(..), Symbol(..), TyName(..), TyVar(..), Type(..), TypeScheme, monoScheme)
import Stella.Compiler.TypedCore.Declare (DeclError(..), declare, initialSignature)
import Stella.Compiler.TypedCore.SignatureCheck (SignatureError(..), sigOk)
import Stella.Compiler.TypedCore.Kinding (KindError(..), Synthesized(..))
import Stella.Compiler.TypedCore.Prim (fn, intTy, ioTy, primSignature, pureFn, recordTy, stringTy, unitTy)
import Stella.Compiler.TypedCore.Signature (CanonicalClass(..), Signature, TyConInfo(..), emptySignature, lookupCtor)
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

main :: ModuleName
main = ModuleName "Main"

value :: P.String -> Qualified Ident
value name = Qualified main (Ident name)

tyCon :: P.String -> Qualified TyName
tyCon name = Qualified main (TyName name)

consoleEff :: Qualified EffName
consoleEff = Qualified main (EffName "Console")

string :: Type
string = TCon stringTy []

int :: Type
int = TCon intTy []

unitTy' :: Type
unitTy' = TCon unitTy []

io :: Type -> Type
io ty = TApp (TCon ioTy []) ty

-- | `effect Console where log : String ->* Unit`, which the foreign cases need
-- | in order to write an effectful arrow at all.
consoleDecl :: Decl Unit
consoleDecl = DeclEffect unit
  { name: EffName "Console"
  , params: []
  , operations:
      [ { name: OpName "log", tyBinders: [], argument: string, resumesWith: unitTy' } ]
  , attributes: []
  }

-- | `( Console )`
consoleRow :: Type
consoleRow = TRowExtend (RowEffectEntry consoleEff []) TRowEmpty

moduleOf :: P.Array (Decl Unit) -> Module Unit
moduleOf decls =
  { annotation: unit, name: main, imports: [], exports: [], decls }

exporting :: P.Array Export -> P.Array (Decl Unit) -> Module Unit
exporting exports decls = (moduleOf decls) { exports = exports }

-- | The verdict on a module, with the signature it would contribute dropped.
verdict :: Module Unit -> Either DeclError Unit
verdict m = case declare primSignature m of
  Left failure -> Left failure.error
  Right _ -> Right unit

-- | The scheme `Σ` records for a data constructor.
ctorScheme :: Module Unit -> Qualified Ident -> Maybe TypeScheme
ctorScheme m name = case declare primSignature m of
  Left _ -> Nothing
  Right sig -> map _.scheme (lookupCtor sig name)

-- | `newtype N = …`, whose shape the checker verifies.
newtypeOf :: P.Array CtorDecl -> Decl Unit
newtypeOf constructors = DeclData unit
  { name: TyName "N"
  , kindVars: []
  , params: []
  , constructors
  , isNewtype: true
  , attributes: []
  }

foreignDecl :: P.String -> TypeScheme -> Decl Unit
foreignDecl name scheme = DeclForeign unit { name: Ident name, scheme, attributes: [] }

nonrec :: P.String -> TypeScheme -> Expr Unit -> Decl Unit
nonrec name scheme expr = DeclNonRec unit
  { name: Ident name, scheme, value: expr, attributes: [] }

globalRef :: P.String -> Expr Unit
globalRef name = Global unit (value name) []

-- | A pure λ.
lam :: P.String -> Type -> Expr Unit -> Expr Unit
lam name ty body = Lam unit (Ident name) ty TRowEmpty body

-- | A kind variable no scheme binds.
ghost :: KindVar
ghost = KindVar "ghost"

entry :: Kind -> P.Array KindVar -> TyConInfo
entry body kindVars = IntrinsicTyCon { kindVars, body } CanonicalOpaque

-- | `Σ_Prim` with one entry of the kind no declaration produces.
withEntry :: TyConInfo -> Signature
withEntry info =
  primSignature { types = Map.insert (tyCon "Weird") info primSignature.types }

-- | `Σ_Prim` with one effect entry of the kind no declaration produces.
withEffectEntry :: P.Array TyBinder -> P.Array OpDecl -> Signature
withEffectEntry params operations =
  primSignature
    { effects = Map.singleton (Qualified main (EffName "Weird"))
        { params, operations: Map.fromFoldable (map (\op -> Tuple op.name op) operations) }
    }

weirdEff :: Qualified EffName
weirdEff = Qualified main (EffName "Weird")

-- | An effect entry whose operation table keys one name to a declaration
-- | carrying another, which no declaration produces.
keyedAs :: OpName -> OpDecl -> Signature -> Signature
keyedAs key op sig =
  sig
    { effects = Map.insert weirdEff
        { params: [], operations: Map.singleton key op }
        sig.effects
    }

-- | `op : Unit ->* Unit`, the shape the entry tests vary one part of.
plainOp :: OpDecl
plainOp = { name: OpName "op", tyBinders: [], argument: unitTy', resumesWith: unitTy' }

spec :: Spec Unit
spec = describe "TypedCore.Declare" do
  describe "the signature a compiler builds" do
    it "accepts the entries of Prim" do
      sigOk primSignature `shouldEqual` Right unit

    it "assembles the signature a module is checked under" do
      map (\sig -> Map.member (tyCon "Weird") sig.types) (initialSignature [])
        `shouldEqual` Right false

    it "checks the table where it is assembled" do
      map (const unit) (initialSignature [ withEntry (entry (KVar ghost) []) ])
        `shouldEqual` Left (SignatureIllFormed (TyConEntryError (tyCon "Weird") (UnboundKindVar ghost)))

    it "refuses an entry that produces a row at some instantiation" do
      -- `forall k. k` passes every use site that instantiates it at `Type`
      let k = KindVar "k"
      sigOk (withEntry (entry (KVar k) [ k ]))
        `shouldEqual` Left (TyConEntryError (tyCon "Weird") (ResultNotType (KVar k)))

    it "refuses an entry whose kind variable nothing binds" do
      -- the result is `Type`, so checking only the result admits it
      sigOk (withEntry (entry (KFun (KVar ghost) KType) []))
        `shouldEqual` Left (TyConEntryError (tyCon "Weird") (UnboundKindVar ghost))

    it "refuses an entry taking an argument that cannot be quantified" do
      sigOk (withEntry (entry (KFun KEffect KType) []))
        `shouldEqual` Left (TyConEntryError (tyCon "Weird") (NotQuantifiable KEffect))

    it "absorbs an entry arriving through two import paths" do
      -- a name belongs to the module that declares it, so the two are one entry
      let part = withEntry (entry KType [])
      map (\sig -> Map.member (tyCon "Weird") sig.types) (initialSignature [ part, part ])
        `shouldEqual` Right true

    it "refuses two different entries under one name" do
      let
        parts = [ withEntry (entry KType []), withEntry (entry (KFun KType KType) []) ]
      map (const unit) (initialSignature parts)
        `shouldEqual` Left (ConflictingTyCon (tyCon "Weird"))

    it "keeps constructors and values in one namespace across parts" do
      let
        ctorPart = emptySignature
          { ctors = Map.singleton (value "T")
              { owner: tyCon "T", tag: 0, params: [], fields: [], scheme: monoScheme int }
          }
        valuePart = emptySignature
          { values = Map.singleton (value "T") { scheme: monoScheme int, isForeign: false } }
      map (const unit) (initialSignature [ ctorPart, valuePart ])
        `shouldEqual` Left (ConflictingValue (value "T"))

  describe "the effect entries a compiler assembles" do
    it "accepts an entry a declaration would have produced" do
      sigOk (withEffectEntry [] [ plainOp ]) `shouldEqual` Right unit

    it "checks the table where it is assembled" do
      map (const unit) (initialSignature [ withEffectEntry [ { name: TyVar "a", kind: KEffect } ] [] ])
        `shouldEqual` Left (SignatureIllFormed (EffectEntryError weirdEff (NotQuantifiable KEffect)))

    it "refuses an operation keyed under a name other than the one it declares" do
      -- the table is keyed by the declared name, so a lookup of `foo` would
      -- otherwise answer with the signature of something else
      let mismatched = withEffectEntry [] [] # keyedAs (OpName "foo") plainOp
      sigOk mismatched
        `shouldEqual` Left (OperationNameMismatch weirdEff (OpName "foo") (OpName "op"))

    it "refuses a parameter at a kind that cannot be quantified" do
      sigOk (withEffectEntry [ { name: TyVar "a", kind: KEffect } ] [])
        `shouldEqual` Left (EffectEntryError weirdEff (NotQuantifiable KEffect))

    it "refuses an operation binder at a kind that cannot be quantified" do
      let op = plainOp { tyBinders = [ { name: TyVar "b", kind: KEffect } ] }
      sigOk (withEffectEntry [] [ op ])
        `shouldEqual` Left (EffectEntryError weirdEff (NotQuantifiable KEffect))

    it "refuses an argument that is not a type" do
      let op = plainOp { argument = TRowEmpty }
      sigOk (withEffectEntry [] [ op ])
        `shouldEqual` Left (EffectEntryError weirdEff (ExpectedKind TRowEmpty KType AnyRow))

    it "refuses a resumption type that is not a type" do
      let op = plainOp { resumesWith = TRowEmpty }
      sigOk (withEffectEntry [] [ op ])
        `shouldEqual` Left (EffectEntryError weirdEff (ExpectedKind TRowEmpty KType AnyRow))

    it "refuses a type variable the entry does not bind" do
      let op = plainOp { argument = TVar (TyVar "ghost") }
      sigOk (withEffectEntry [] [ op ])
        `shouldEqual` Left (EffectEntryError weirdEff (UnboundTyVar (TyVar "ghost")))

    it "admits a type variable the parameters bind" do
      let op = plainOp { argument = TVar (TyVar "a") }
      sigOk (withEffectEntry [ { name: TyVar "a", kind: KType } ] [ op ])
        `shouldEqual` Right unit

    it "admits one the operation binds for itself" do
      let
        op = plainOp
          { tyBinders = [ { name: TyVar "b", kind: KType } ], argument = TVar (TyVar "b") }
      sigOk (withEffectEntry [] [ op ]) `shouldEqual` Right unit

  describe "data declarations" do
    it "derives the type of a constructor" do
      let
        m = moduleOf
          [ DeclData unit
              { name: TyName "Box"
              , kindVars: []
              , params: [ { name: TyVar "a", kind: KType } ]
              , constructors: [ { name: Ident "Box", tag: 0, fields: [ TVar (TyVar "a") ] } ]
              , isNewtype: false
              , attributes: []
              }
          ]
      ctorScheme m (value "Box")
        `shouldEqual` Just
          ( monoScheme
              ( TForall (TyVar "a") KType
                  (pureFn (TVar (TyVar "a")) (TApp (TCon (tyCon "Box") []) (TVar (TyVar "a"))))
              )
          )

    it "carries the kind scheme into the constructor's type" do
      -- `Proxy : forall k. forall (a : k). Proxy [[k]] a`
      let
        k = KindVar "k"
        m = moduleOf
          [ DeclData unit
              { name: TyName "Proxy"
              , kindVars: [ k ]
              , params: [ { name: TyVar "a", kind: KVar k } ]
              , constructors: [ { name: Ident "Proxy", tag: 0, fields: [] } ]
              , isNewtype: false
              , attributes: []
              }
          ]
      ctorScheme m (value "Proxy")
        `shouldEqual` Just
          { kindVars: [ k ]
          , body:
              TForall (TyVar "a") (KVar k)
                (TApp (TCon (tyCon "Proxy") [ KVar k ]) (TVar (TyVar "a")))
          }

    it "refuses a field that is not a type" do
      let
        m = moduleOf
          [ DeclData unit
              { name: TyName "Bad"
              , kindVars: []
              , params: []
              , constructors: [ { name: Ident "Bad", tag: 0, fields: [ TRowEmpty ] } ]
              , isNewtype: false
              , attributes: []
              }
          ]
      verdict m `shouldEqual` Left (IllKinded (ExpectedKind TRowEmpty KType AnyRow))

    it "refuses a tag used twice" do
      let
        m = moduleOf
          [ DeclData unit
              { name: TyName "Two"
              , kindVars: []
              , params: []
              , constructors:
                  [ { name: Ident "A", tag: 0, fields: [] }
                  , { name: Ident "B", tag: 0, fields: [] }
                  ]
              , isNewtype: false
              , attributes: []
              }
          ]
      verdict m `shouldEqual` Left (DuplicateTag (tyCon "Two") 0)

    it "accepts a newtype of one constructor with one field" do
      verdict (moduleOf [ newtypeOf [ { name: Ident "N", tag: 0, fields: [ int ] } ] ])
        `shouldEqual` Right unit

    it "refuses a newtype with two constructors" do
      verdict
        ( moduleOf
            [ newtypeOf
                [ { name: Ident "N", tag: 0, fields: [ int ] }
                , { name: Ident "M", tag: 1, fields: [ int ] }
                ]
            ]
        )
        `shouldEqual` Left (NewtypeShape (tyCon "N"))

    it "refuses a newtype whose constructor has two fields" do
      verdict (moduleOf [ newtypeOf [ { name: Ident "N", tag: 0, fields: [ int, int ] } ] ])
        `shouldEqual` Left (NewtypeShape (tyCon "N"))

  describe "effect declarations" do
    it "checks an operation signature" do
      verdict (moduleOf [ consoleDecl ]) `shouldEqual` Right unit

    it "refuses a parameter at a kind that is not quantifiable" do
      let
        m = moduleOf
          [ DeclEffect unit
              { name: EffName "Bad"
              , params: [ { name: TyVar "e", kind: KEffect } ]
              , operations: []
              , attributes: []
              }
          ]
      verdict m `shouldEqual` Left (IllKinded (NotQuantifiable KEffect))

    it "accepts an operation admitting an arbitrary IO" do
      -- a lift hands an opaque `IO` to the handler and executes nothing, so
      -- what it costs is the granularity of the capability
      let
        a = TyVar "a"
        m = moduleOf
          [ DeclEffect unit
              { name: EffName "LiftIO"
              , params: []
              , operations:
                  [ { name: OpName "liftIO"
                    , tyBinders: [ { name: a, kind: KType } ]
                    , argument: io (TVar a)
                    , resumesWith: TVar a
                    }
                  ]
              , attributes: []
              }
          ]
      verdict m `shouldEqual` Right unit

    it "refuses one operation name twice" do
      let
        op = { name: OpName "log", tyBinders: [], argument: string, resumesWith: unitTy' }
        m = moduleOf
          [ DeclEffect unit
              { name: EffName "Console", params: [], operations: [ op, op ], attributes: [] }
          ]
      verdict m `shouldEqual` Left (DuplicateOperation consoleEff (OpName "log"))

  describe "foreign declarations" do
    it "accepts the shape every leaf takes" do
      verdict (moduleOf [ foreignDecl "primLog" (monoScheme (pureFn string (io unitTy'))) ])
        `shouldEqual` Right unit

    it "refuses an effectful result arrow" do
      -- the type would remove the effect from the row while the output never
      -- reaches a handler's clause
      verdict (moduleOf [ consoleDecl, foreignDecl "log" (monoScheme (fn string consoleRow unitTy')) ])
        `shouldEqual` Left (EffectfulForeign (value "log") consoleRow)

    it "refuses an effectful argument arrow" do
      -- the calling convention of the lowering would leak across the boundary
      let
        e = TyVar "e"
        a = TyVar "a"
        scheme = monoScheme
          ( TForall e (KRow RowEffect)
              (TForall a KType (pureFn (fn (TVar a) (TVar e) (TVar a)) (TVar a)))
          )
      verdict (moduleOf [ foreignDecl "mapImpl" scheme ])
        `shouldEqual` Left (EffectfulForeign (value "mapImpl") (TVar e))

    it "refuses an effectful arrow in the payload of a row" do
      -- a callback reaches the boundary through a record as readily as through
      -- an argument
      let
        row = TRowExtend (RowTypeEntry (SymbolKey (Symbol "cb")) (fn int consoleRow int)) TRowEmpty
        scheme = monoScheme (pureFn (TApp (TCon recordTy []) row) unitTy')
      verdict (moduleOf [ consoleDecl, foreignDecl "use" scheme ])
        `shouldEqual` Left (EffectfulForeign (value "use") consoleRow)

    it "does not traverse a constraint, which carries no value across" do
      -- a constraint is an erased proposition, so neither handler bypass nor a
      -- leaking calling convention can arise inside one
      let
        row = TRowExtend (RowTypeEntry (SymbolKey (Symbol "x")) (fn int consoleRow int)) TRowEmpty
        scheme = monoScheme (TConstrained (Lacks (SymbolKey (Symbol "cb")) row) (pureFn int int))
      verdict (moduleOf [ consoleDecl, foreignDecl "f" scheme ])
        `shouldEqual` Right unit

  describe "value declarations" do
    it "accepts a reference to a foreign declared later" do
      -- foreigns are collected before any value declaration is checked
      let
        m = moduleOf
          [ nonrec "x" (monoScheme (pureFn string (io unitTy'))) (globalRef "primLog")
          , foreignDecl "primLog" (monoScheme (pureFn string (io unitTy')))
          ]
      verdict m `shouldEqual` Right unit

    it "refuses a reference to a later value declaration" do
      let
        m = moduleOf
          [ nonrec "x" (monoScheme int) (globalRef "y")
          , nonrec "y" (monoScheme int) (Lit unit (LitInt 1))
          ]
      verdict m `shouldEqual` Left (ForwardReference (value "y"))

    it "refuses a nonrec referring to itself" do
      let m = moduleOf [ nonrec "x" (monoScheme int) (globalRef "x") ]
      verdict m `shouldEqual` Left (ForwardReference (value "x"))

    it "accepts a rec group whose members refer to each other" do
      let
        m = moduleOf
          [ DeclRec unit
              [ { name: Ident "f"
                , scheme: monoScheme (pureFn int int)
                , value: lam "n" int (App unit (globalRef "g") (Var unit (Ident "n")))
                , attributes: []
                }
              , { name: Ident "g"
                , scheme: monoScheme (pureFn int int)
                , value: lam "n" int (Var unit (Ident "n"))
                , attributes: []
                }
              ]
          ]
      verdict m `shouldEqual` Right unit

    it "admits a recursive right-hand side that is no function value and reads nothing too early" do
      let
        m = moduleOf
          [ DeclRec unit
              [ { name: Ident "f", scheme: monoScheme int, value: Lit unit (LitInt 1), attributes: [] } ]
          ]
      verdict m `shouldEqual` Right unit

    it "refuses a recursive right-hand side reading itself, or a member written after it" do
      let
        self = moduleOf
          [ DeclRec unit
              [ { name: Ident "f", scheme: monoScheme int, value: globalRef "f", attributes: [] } ]
          ]
        group first second = moduleOf [ DeclRec unit [ first, second ] ]
        f = { name: Ident "f", scheme: monoScheme (pureFn int int), value: globalRef "g", attributes: [] }
        g = { name: Ident "g", scheme: monoScheme (pureFn int int), value: lam "n" int (App unit (globalRef "f") (Var unit (Ident "n"))), attributes: [] }
      verdict self `shouldEqual` Left (ReadBeforeInitialized (value "f") (value "f"))
      verdict (group f g) `shouldEqual` Left (ReadBeforeInitialized (value "f") (value "g"))
      verdict (group g f) `shouldEqual` Right unit

    it "accepts a rec group whose members have different kind schemes" do
      -- every scheme is registered before any right-hand side is checked
      let
        k = KindVar "k"
        m = moduleOf
          [ DeclRec unit
              [ { name: Ident "f"
                , scheme:
                    { kindVars: [ k ]
                    , body: TForall (TyVar "a") (KVar k) (pureFn int int)
                    }
                , value: TyLam unit (TyVar "a") (KVar k) (lam "n" int (Var unit (Ident "n")))
                , attributes: []
                }
              , { name: Ident "g"
                , scheme: monoScheme (pureFn int int)
                , value:
                    lam "n" int
                      ( App unit
                          (TyApp unit (Global unit (value "f") [ KType ]) int)
                          (Var unit (Ident "n"))
                      )
                , attributes: []
                }
              ]
          ]
      verdict m `shouldEqual` Right unit

  describe "module well-formedness" do
    it "refuses a module named Prim" do
      let m = (moduleOf []) { name = ModuleName "Prim" }
      verdict m `shouldEqual` Left (ReservedModuleName (ModuleName "Prim"))

    it "refuses one effect name twice" do
      verdict (moduleOf [ consoleDecl, consoleDecl ])
        `shouldEqual` Left (DuplicateEffect consoleEff)

    it "refuses two different effect entries under one name" do
      let
        parts =
          [ withEffectEntry [] [ plainOp ]
          , withEffectEntry [ { name: TyVar "a", kind: KType } ] [ plainOp ]
          ]
      map (const unit) (initialSignature parts)
        `shouldEqual` Left (ConflictingEffect weirdEff)

    it "refuses one type name twice" do
      let
        decl = DeclData unit
          { name: TyName "T"
          , kindVars: []
          , params: []
          , constructors: []
          , isNewtype: false
          , attributes: []
          }
      verdict (moduleOf [ decl, decl ]) `shouldEqual` Left (DuplicateTyCon (tyCon "T"))

    it "refuses a constructor and a value of one name" do
      -- a constructor is an ordinary global name, so the two share a namespace
      let
        m = moduleOf
          [ DeclData unit
              { name: TyName "T"
              , kindVars: []
              , params: []
              , constructors: [ { name: Ident "T", tag: 0, fields: [] } ]
              , isNewtype: false
              , attributes: []
              }
          , nonrec "T" (monoScheme int) (Lit unit (LitInt 1))
          ]
      verdict m `shouldEqual` Left (DuplicateName (value "T"))

    it "refuses an export of a name the module does not declare" do
      verdict (exporting [ ExportValue (Ident "absent") ] [])
        `shouldEqual` Left (MissingExport (ExportValue (Ident "absent")))
