-- | `Stella.Syntax`: what a macro is written against
-- | ([Syntax Extensions and Parsers](../../../../docs/proposals/09-Syntax-Extensions-and-Parsers.md)).
-- |
-- | **A macro is a parser**, a value of type `Parser (Syntax c)`: it reads the
-- | token tree of its call and produces syntax of the category `c`. The types
-- | here mirror the host's ([Tree](Tree.purs)) constructor for constructor, and
-- | the parser combinators are guest code the host runs; nothing a parser does
-- | reaches the host but what it returns.
-- |
-- | **A parser is a function of its state**, which is the trees left at the
-- | level it reads, how many it has read there, and where that level ends. It
-- | succeeds with a value and the state after it, or fails with the farthest
-- | position reached, what was expected there, and the labels of the contexts
-- | it was in. What was expected may name one thing more than once, the host
-- | taking it as a set. `orElse` tries its second parser from the state the first began
-- | at, and keeps the farther failure of the two, joining what each expected
-- | where both stopped at one position.
-- |
-- | **`layout` reads a block by the trivia**: the column of the first item's
-- | first token is the block's, a token beginning a line at it begins the next
-- | item, one to its left ends the block, and one to its right continues the
-- | item. A token begins a line where a line break stands in its trivia, a
-- | block comment spanning lines among them.
-- |
-- | **An origin says where a token or a node came from, for diagnostics
-- | alone**: the input of the call, by a reference the host issued for it,
-- | `InputOrigin`, which nothing a parser writes can make; or a quotation,
-- | `$QuotedOrigin`, by the module and the range it declares. `OriginRef` is
-- | exported abstract. `$QuotedOrigin` and `$spliced`, which a quotation is
-- | written with, are elaboration-only entries: their names are no identifier,
-- | and they are in no export of the module's interface, so neither source nor
-- | a synthesizer reaches them.
-- |
-- | The module has lists and optional values of its own, as the protocol's
-- | types, and depends on `Base.Int` alone, for the columns and counts it
-- | compares.
module Stella.Compiler.Macro.Bundle
  ( Bundle
  , bundle
  , syntaxModule
  , syntaxModuleName
  , originRefTy
  , issuedOriginTy
  , withSyntax
  ) where

import Prelude hiding (ap, one, zero)

import Prim as P

import Data.Array as Array
import Data.Either (Either)
import Data.Foldable (foldl, foldr)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Stella.Compiler.Elaborate.Protocol.Guest.Shape (Descriptor, describe)
import Stella.Compiler.TypedCore (CanonicalClass(..), DecisionTree(..), Decl(..), Export(..), Expr(..), Ident(..), Kind(..), Literal(..), Module, ModuleName(..), Occurrence(..), Qualified(..), Signature, TyConInfo(..), TyName(..), TyVar(..), Type(..), monoScheme, scalarString)
import Stella.Compiler.TypedCore.Prim (booleanTy, intTy, pureFn, stringTy, unitCtor, unitTy)

syntaxModuleName :: ModuleName
syntaxModuleName = ModuleName "Stella.Syntax"

-- | `Stella.Syntax.OriginRef`: where a token or a node came from.
originRefTy :: Qualified TyName
originRefTy = Qualified syntaxModuleName (TyName "OriginRef")

-- | `Stella.Syntax.IssuedOrigin`, an intrinsic opaque type: a reference the
-- | host issues for a token of a call's input, which nothing a parser writes can
-- | make.
issuedOriginTy :: Qualified TyName
issuedOriginTy = Qualified syntaxModuleName (TyName "IssuedOrigin")

-- | A signature with `Stella.Syntax.IssuedOrigin` in it, which checking the
-- | module, and a parser over it, needs.
withSyntax :: Signature -> Signature
withSyntax sig = sig
  { types = Map.insert issuedOriginTy (IntrinsicTyCon (monoScheme KType) CanonicalOpaque) sig.types }

-- | The module, the signature fragment that gives `IssuedOrigin` its type, the
-- | entries its interface exports none of, and the shape descriptor of the
-- | types a value crossing to the host has: the token tree a parser reads, the
-- | syntax it builds, and how it came out. A parser itself is a function, and
-- | never crosses.
type Bundle =
  { module :: Module Unit
  , withSignature :: Signature -> Signature
  , unexported :: P.Array Ident
  , descriptor :: Descriptor
  }

bundle :: Either P.String Bundle
bundle = describe issuedOriginTy syntaxModule { decls = Array.filter crossing syntaxModule.decls } <#> \descriptor ->
  { module: syntaxModule, withSignature: withSyntax, unexported: map Ident [ "InputOrigin", "$QuotedOrigin", "$spliced" ], descriptor }
  where
  crossing = case _ of
    DeclData _ d -> not (Array.elem d.name (map TyName [ "State", "Reply", "Parser", "LayoutItem", "Block", "ItemRun" ]))
    _ -> false

intModule :: ModuleName
intModule = ModuleName "Base.Int"

syntaxModule :: Module Unit
syntaxModule =
  { annotation: unit
  , name: syntaxModuleName
  , imports: [ intModule ]
  , exports:
      map (ExportType <<< TyName) (map _.name types)
        <> map (ExportCtor <<< Ident) (Array.concatMap (map (\(Tuple c _) -> c) <<< _.ctors) types)
        <> map ExportValue (Array.concatMap declared values)
  , decls: map dataDecl types <> values
  }
  where
  declared = case _ of
    DeclNonRec _ b -> [ b.name ]
    DeclRec _ bs -> map _.name bs
    _ -> []

-- The data types ---------------------------------------------------------------------

type DataType = { name :: P.String, params :: P.Array P.String, ctors :: P.Array (Tuple P.String (P.Array Type)) }

dataDecl :: DataType -> Decl Unit
dataDecl d = DeclData unit
  { name: TyName d.name
  , kindVars: []
  , params: map (\p -> { name: TyVar p, kind: KType }) d.params
  , constructors: Array.mapWithIndex (\tag (Tuple c fields) -> { name: Ident c, tag, fields }) d.ctors
  , isNewtype: false
  , attributes: []
  }

types :: P.Array DataType
types =
  [ { name: "List", params: [ "a" ], ctors: [ Tuple "Nil" [], Tuple "Cons" [ va, list va ] ] }
  , { name: "Maybe", params: [ "a" ], ctors: [ Tuple "Nothing" [], Tuple "Just" [ va ] ] }
  , simple "Position" [ Tuple "Position" [ int, int ] ]
  , simple "Range" [ Tuple "Range" [ con "Position", con "Position" ] ]
  , simple "Trivia"
      [ Tuple "Spaces" [ string, con "Range" ]
      , Tuple "Newline" [ string, con "Range" ]
      , Tuple "LineComment" [ string, con "Range" ]
      , Tuple "BlockComment" [ string, con "Range" ]
      ]
  , simple "TokenKind"
      [ Tuple "GroupBracket" []
      , Tuple "Comma" []
      , Tuple "Backslash" []
      , Tuple "Underscore" []
      , Tuple "LowerName" [ maybe string, string ]
      , Tuple "UpperName" [ maybe string, string ]
      , Tuple "DiscriminatorName" [ maybe string, string ]
      , Tuple "OperatorName" [ maybe string, string ]
      , Tuple "OperatorValue" [ maybe string, string ]
      , Tuple "InfixName" [ maybe string, string ]
      , Tuple "HoleName" [ string ]
      , Tuple "TagName" [ string ]
      , Tuple "DirectiveName" [ string ]
      , Tuple "MacroName" [ maybe string, string ]
      , Tuple "IntLiteral" [ int ]
      , Tuple "NumberLiteral" [ TCon (Qualified (ModuleName "Prim") (TyName "Number")) [] ]
      , Tuple "CharLiteral" [ string ]
      , Tuple "StringLiteral" [ string ]
      ]
  , simple "OriginRef"
      [ Tuple "InputOrigin" [ TCon issuedOriginTy [] ]
      , Tuple "$QuotedOrigin" [ string, con "Position", con "Position" ]
      ]
  , simple "Token" [ Tuple "Token" [ con "TokenKind", string, con "Range", list (con "Trivia"), originRef ] ]
  , simple "Delimiter"
      [ Tuple "Paren" []
      , Tuple "Bracket" []
      , Tuple "Brace" []
      , Tuple "EffectRow" []
      , Tuple "Synthesized" []
      , Tuple "AttributeBracket" []
      , Tuple "LocalOpen" [ string ]
      ]
  , simple "TokenTree"
      [ Tuple "Leaf" [ token ]
      , Tuple "Group" [ con "Delimiter", token, list tree, list token ]
      ]
  , simple "SyntaxNode"
      [ Tuple "SyntaxToken" [ token ]
      , Tuple "SyntaxGroup" [ originRef, con "Delimiter", token, list node, list token ]
      , Tuple "SyntaxLayout" [ originRef, list (con "SyntaxItem") ]
      ]
  , simple "SyntaxItem" [ Tuple "SyntaxItem" [ originRef, list node ] ]
  , { name: "Syntax", params: [ "c" ], ctors: [ Tuple "Syntax" [ list node ] ] }
  , simple "Term" []
  , simple "Failure" [ Tuple "Failure" [ con "Position", list string, list string ] ]
  , simple "State" [ Tuple "State" [ list tree, int, con "Position" ] ]
  , { name: "Reply", params: [ "a" ], ctors: [ Tuple "Ok" [ va, state ], Tuple "Err" [ con "Failure" ] ] }
  , { name: "Parser", params: [ "a" ], ctors: [ Tuple "Parser" [ pureFn state (reply va) ] ] }
  , { name: "Result", params: [ "a" ], ctors: [ Tuple "Parsed" [ va ], Tuple "Failed" [ con "Failure" ] ] }
  , simple "LayoutItem" [ Tuple "LayoutItem" [ list tree, con "Position" ] ]
  , simple "Block" [ Tuple "Block" [ list (con "LayoutItem"), list tree ] ]
  , simple "ItemRun" [ Tuple "ItemRun" [ list tree, list tree ] ]
  ]
  where
  simple name ctors = { name, params: [], ctors }

-- Type shorthands ----------------------------------------------------------------------

con :: P.String -> Type
con n = TCon (Qualified syntaxModuleName (TyName n)) []

app :: P.String -> Type -> Type
app n = TApp (con n)

list :: Type -> Type
list = app "List"

maybe :: Type -> Type
maybe = app "Maybe"

parser :: Type -> Type
parser = app "Parser"

reply :: Type -> Type
reply = app "Reply"

result :: Type -> Type
result = app "Result"

tv :: P.String -> Type
tv = TVar <<< TyVar

va :: Type
va = tv "a"

vb :: Type
vb = tv "b"

int :: Type
int = TCon intTy []

string :: Type
string = TCon stringTy []

boolean :: Type
boolean = TCon booleanTy []

unitType :: Type
unitType = TCon unitTy []

originRef :: Type
originRef = TCon originRefTy []

token :: Type
token = con "Token"

tree :: Type
tree = con "TokenTree"

node :: Type
node = con "SyntaxNode"

state :: Type
state = con "State"

position :: Type
position = con "Position"

failure :: Type
failure = con "Failure"

quantified :: P.Array P.String -> Type -> Type
quantified names body = foldr (\x t -> TForall (TyVar x) KType t) body names

fns :: P.Array Type -> Type -> Type
fns args r = foldr pureFn r args

-- Term shorthands ----------------------------------------------------------------------

syn :: P.String -> Qualified Ident
syn = Qualified syntaxModuleName <<< Ident

v :: P.String -> Expr Unit
v = Var unit <<< Ident

-- | A global of the module at the type arguments given.
g :: P.String -> P.Array Type -> Expr Unit
g n = foldl (TyApp unit) (Global unit (syn n) [])

ap :: Expr Unit -> P.Array (Expr Unit) -> Expr Unit
ap = foldl (App unit)

call :: P.String -> P.Array Type -> P.Array (Expr Unit) -> Expr Unit
call n tys = ap (g n tys)

lam :: P.Array (Tuple P.String Type) -> Expr Unit -> Expr Unit
lam ps body = foldr (\(Tuple x t) e -> Lam unit (Ident x) t e) body ps

tylam :: P.Array P.String -> Expr Unit -> Expr Unit
tylam names body = foldr (\x e -> TyLam unit (TyVar x) KType e) body names

intOp :: P.String -> Expr Unit -> Expr Unit -> Expr Unit
intOp op a b = ap (Global unit (Qualified intModule (Ident op)) []) [ a, b ]

text :: P.String -> Expr Unit
text s = case scalarString s of
  Just str -> Lit unit (LitString str)
  Nothing -> Lit unit (LitInt 0)

true_ :: Expr Unit
true_ = Lit unit (LitBoolean true)

false_ :: Expr Unit
false_ = Lit unit (LitBoolean false)

zero :: Expr Unit
zero = Lit unit (LitInt 0)

one :: Expr Unit
one = Lit unit (LitInt 1)

unitValue :: Expr Unit
unitValue = Global unit unitCtor []

-- | A branch on a constructor: its name, a variable for each field (`_` binding
-- | none), and the body.
type Branch = { ctor :: P.String, fields :: P.Array P.String, body :: Expr Unit }

branch :: P.String -> P.Array P.String -> Expr Unit -> Branch
branch ctor fields body = { ctor, fields, body }

match :: Expr Unit -> P.Array Branch -> Maybe (Expr Unit) -> Expr Unit
match e branches fallback = Case unit [ e ] (SwitchCtor scrutinee (map tree' branches) (map Leaf fallback))
  where
  tree' b = { ctor: syn b.ctor, tree: foldr (bind b.ctor) (Leaf b.body) (Array.mapWithIndex Tuple b.fields) }
  bind c (Tuple i x) inner
    | x == "_" = inner
    | otherwise = Bind (Ident x) (OccField scrutinee (syn c) i) inner

ifThenElse :: Expr Unit -> Expr Unit -> Expr Unit -> Expr Unit
ifThenElse cond yes no = Case unit [ cond ] (SwitchLit scrutinee [ { lit: LitBoolean true, tree: Leaf yes } ] (Leaf no))

scrutinee :: Occurrence
scrutinee = OccScrutinee 0

-- `Parser (\s -> body)`.
parserOf :: Type -> Expr Unit -> Expr Unit
parserOf a body = call "Parser" [ a ] [ lam [ Tuple "s" state ] body ]

-- `run p s`.
runP :: Type -> Expr Unit -> Expr Unit -> Expr Unit
runP a p s = call "run" [ a ] [ p, s ]

ok :: Type -> Expr Unit -> Expr Unit -> Expr Unit
ok a x s = call "Ok" [ a ] [ x, s ]

err :: Type -> Expr Unit -> Expr Unit
err a f = call "Err" [ a ] [ f ]

cons :: Type -> Expr Unit -> Expr Unit -> Expr Unit
cons a x xs = call "Cons" [ a ] [ x, xs ]

nil :: Type -> Expr Unit
nil a = g "Nil" [ a ]

-- `Failure at [ expected ] []`.
expecting :: Expr Unit -> Expr Unit -> Expr Unit
expecting at what = call "Failure" [] [ at, cons string what (nil string), nil string ]

-- The values ------------------------------------------------------------------------------

value :: P.String -> Type -> Expr Unit -> Decl Unit
value n t e = DeclNonRec unit { name: Ident n, scheme: monoScheme t, value: e, attributes: [] }

recursive :: P.Array { name :: P.String, type :: Type, value :: Expr Unit } -> Decl Unit
recursive bs = DeclRec unit (map (\b -> { name: Ident b.name, scheme: monoScheme b.type, value: b.value, attributes: [] }) bs)

values :: P.Array (Decl Unit)
values =
  [ recursive
      [ { name: "append"
        , type: quantified [ "a" ] (fns [ list va, list va ] (list va))
        , value: tylam [ "a" ] $ lam [ Tuple "xs" (list va), Tuple "ys" (list va) ] $
            match (v "xs")
              [ branch "Nil" [] (v "ys")
              , branch "Cons" [ "x", "rest" ] (cons va (v "x") (call "append" [ va ] [ v "rest", v "ys" ]))
              ]
              Nothing
        }
      ]
  -- whether a range ends on a later line than it begins, as a block comment
  -- holding a line break does
  , value "spansLines" (pureFn (con "Range") boolean) $ lam [ Tuple "range" (con "Range") ] $
      match (v "range")
        [ branch "Range" [ "start", "end" ] $
            match (v "start")
              [ branch "Position" [ "from", "_" ] $
                  match (v "end") [ branch "Position" [ "to", "_" ] (ifThenElse (intOp "eq" (v "from") (v "to")) false_ true_) ] Nothing
              ]
              Nothing
        ]
        Nothing
  , recursive
      [ { name: "hasNewline"
        , type: pureFn (list (con "Trivia")) boolean
        , value: lam [ Tuple "trivia" (list (con "Trivia")) ] $
            match (v "trivia")
              [ branch "Nil" [] false_
              , branch "Cons" [ "t", "rest" ] $
                  match (v "t")
                    [ branch "Newline" [ "_", "_" ] true_
                    , branch "BlockComment" [ "_", "range" ] $
                        ifThenElse (call "spansLines" [] [ v "range" ]) true_ (call "hasNewline" [] [ v "rest" ])
                    ]
                    (Just (call "hasNewline" [] [ v "rest" ]))
              ]
              Nothing
        }
      ]
  -- the first token of a tree: a leaf's, or a group's opening one
  , value "firstToken" (pureFn tree token) $ lam [ Tuple "t" tree ] $
      match (v "t") [ branch "Leaf" [ "tok" ] (v "tok"), branch "Group" [ "_", "open", "_", "_" ] (v "open") ] Nothing
  , value "startOf" (pureFn token position) $ lam [ Tuple "tok" token ] $
      match (v "tok")
        [ branch "Token" [ "_", "_", "range", "_", "_" ] (match (v "range") [ branch "Range" [ "start", "_" ] (v "start") ] Nothing) ]
        Nothing
  , value "originOf" (pureFn token originRef) $ lam [ Tuple "tok" token ] $
      match (v "tok") [ branch "Token" [ "_", "_", "_", "_", "origin" ] (v "origin") ] Nothing
  , value "columnOf" (pureFn tree int) $ lam [ Tuple "t" tree ] $
      match (call "startOf" [] [ call "firstToken" [] [ v "t" ] ]) [ branch "Position" [ "_", "column" ] (v "column") ] Nothing
  -- whether a tree's first token begins a line
  , value "beginsLine" (pureFn tree boolean) $ lam [ Tuple "t" tree ] $
      match (call "firstToken" [] [ v "t" ])
        [ branch "Token" [ "_", "_", "_", "leading", "_" ] (call "hasNewline" [] [ v "leading" ]) ]
        Nothing
  -- where the next token stands, or the end of the level where none is left
  , value "positionAt" (pureFn state position) $ lam [ Tuple "s" state ] $
      match (v "s")
        [ branch "State" [ "trees", "_", "end" ] $
            match (v "trees")
              [ branch "Nil" [] (v "end")
              , branch "Cons" [ "t", "_" ] (call "startOf" [] [ call "firstToken" [] [ v "t" ] ])
              ]
              Nothing
        ]
        Nothing
  -- whether one position stands before another
  , value "before" (fns [ position, position ] boolean) $ lam [ Tuple "p" position, Tuple "q" position ] $
      match (v "p")
        [ branch "Position" [ "pl", "pc" ] $
            match (v "q")
              [ branch "Position" [ "ql", "qc" ] $
                  ifThenElse (intOp "lt" (v "pl") (v "ql")) true_
                    (ifThenElse (intOp "eq" (v "pl") (v "ql")) (intOp "lt" (v "pc") (v "qc")) false_)
              ]
              Nothing
        ]
        Nothing
  -- the farther of two failures, and where both stopped at one position, what
  -- each expected and the labels of each
  , value "merge" (fns [ failure, failure ] failure) $ lam [ Tuple "f" failure, Tuple "h" failure ] $
      match (v "f")
        [ branch "Failure" [ "fp", "fe", "fl" ] $
            match (v "h")
              [ branch "Failure" [ "hp", "he", "hl" ] $
                  ifThenElse (call "before" [] [ v "fp", v "hp" ]) (v "h")
                    ( ifThenElse (call "before" [] [ v "hp", v "fp" ]) (v "f")
                        ( call "Failure" []
                            [ v "fp", call "append" [ string ] [ v "fe", v "he" ], call "append" [ string ] [ v "fl", v "hl" ] ]
                        )
                    )
              ]
              Nothing
        ]
        Nothing
  , value "consumed" (pureFn state int) $ lam [ Tuple "s" state ] $
      match (v "s") [ branch "State" [ "_", "n", "_" ] (v "n") ] Nothing
  , value "run" (quantified [ "a" ] (fns [ parser va, state ] (reply va))) $ tylam [ "a" ] $ lam [ Tuple "p" (parser va), Tuple "s" state ] $
      match (v "p") [ branch "Parser" [ "f" ] (ap (v "f") [ v "s" ]) ] Nothing
  , value "pure" (quantified [ "a" ] (pureFn va (parser va))) $ tylam [ "a" ] $ lam [ Tuple "x" va ] $
      parserOf va (ok va (v "x") (v "s"))
  , value "bind" (quantified [ "a", "b" ] (fns [ parser va, pureFn va (parser vb) ] (parser vb)))
      $ tylam [ "a", "b" ]
      $ lam [ Tuple "p" (parser va), Tuple "k" (pureFn va (parser vb)) ]
      $ parserOf vb
      $
        match (runP va (v "p") (v "s"))
          [ branch "Ok" [ "x", "next" ] (runP vb (ap (v "k") [ v "x" ]) (v "next"))
          , branch "Err" [ "f" ] (err vb (v "f"))
          ]
          Nothing
  , value "map" (quantified [ "a", "b" ] (fns [ pureFn va vb, parser va ] (parser vb)))
      $ tylam [ "a", "b" ]
      $ lam [ Tuple "f" (pureFn va vb), Tuple "p" (parser va) ]
      $
        call "bind" [ va, vb ] [ v "p", lam [ Tuple "x" va ] (call "pure" [ vb ] [ ap (v "f") [ v "x" ] ]) ]
  , value "orElse" (quantified [ "a" ] (fns [ parser va, parser va ] (parser va)))
      $ tylam [ "a" ]
      $ lam [ Tuple "p" (parser va), Tuple "q" (parser va) ]
      $ parserOf va
      $
        match (runP va (v "p") (v "s"))
          [ branch "Ok" [ "x", "next" ] (ok va (v "x") (v "next"))
          , branch "Err" [ "f" ] $
              match (runP va (v "q") (v "s"))
                [ branch "Ok" [ "y", "after" ] (ok va (v "y") (v "after"))
                , branch "Err" [ "h" ] (err va (call "merge" [] [ v "f", v "h" ]))
                ]
                Nothing
          ]
          Nothing
  , value "fail" (quantified [ "a" ] (pureFn string (parser va))) $ tylam [ "a" ] $ lam [ Tuple "what" string ] $
      parserOf va (err va (expecting (call "positionAt" [] [ v "s" ]) (v "what")))
  , value "label" (quantified [ "a" ] (fns [ string, parser va ] (parser va)))
      $ tylam [ "a" ]
      $ lam [ Tuple "context" string, Tuple "p" (parser va) ]
      $ parserOf va
      $
        match (runP va (v "p") (v "s"))
          [ branch "Ok" [ "x", "next" ] (ok va (v "x") (v "next"))
          , branch "Err" [ "f" ] $
              match (v "f")
                [ branch "Failure" [ "at", "expected", "labels" ] $
                    err va (call "Failure" [] [ v "at", v "expected", cons string (v "context") (v "labels") ])
                ]
                Nothing
          ]
          Nothing
  -- the next tree, where it is one the predicate admits
  , value "satisfy" (fns [ string, pureFn tree boolean ] (parser tree))
      $ lam [ Tuple "what" string, Tuple "admits" (pureFn tree boolean) ]
      $ parserOf tree
      $
        match (v "s")
          [ branch "State" [ "trees", "n", "end" ] $
              match (v "trees")
                [ branch "Cons" [ "t", "rest" ] $
                    ifThenElse (ap (v "admits") [ v "t" ])
                      (ok tree (v "t") (call "State" [] [ v "rest", intOp "add" (v "n") one, v "end" ]))
                      (err tree (expecting (call "positionAt" [] [ v "s" ]) (v "what")))
                ]
                (Just (err tree (expecting (v "end") (v "what"))))
          ]
          Nothing
  , value "anyTree" (pureFn tree boolean) $ lam [ Tuple "t" tree ] true_
  , value "isLeaf" (pureFn tree boolean) $ lam [ Tuple "t" tree ] $
      match (v "t") [ branch "Leaf" [ "_" ] true_ ] (Just false_)
  , value "isComma" (pureFn tree boolean) $ lam [ Tuple "t" tree ] $
      match (v "t")
        [ branch "Leaf" [ "tok" ] $
            match (v "tok") [ branch "Token" [ "kind", "_", "_", "_", "_" ] (match (v "kind") [ branch "Comma" [] true_ ] (Just false_)) ] Nothing
        ]
        (Just false_)
  , value "notComma" (pureFn tree boolean) $ lam [ Tuple "t" tree ] $
      ifThenElse (call "isComma" [] [ v "t" ]) false_ true_
  , value "token" (parser token) $
      call "bind" [ tree, token ]
        [ call "satisfy" [] [ text "a token", g "isLeaf" [] ]
        , lam [ Tuple "t" tree ] $
            match (v "t") [ branch "Leaf" [ "tok" ] (call "pure" [ token ] [ v "tok" ]) ] (Just (call "fail" [ token ] [ text "a token" ]))
        ]
  , value "tree" (parser tree) (call "satisfy" [] [ text "a token", g "anyTree" [] ])
  , value "comma" (parser tree) (call "satisfy" [] [ text "`,`", g "isComma" [] ])
  , value "end" (parser unitType)
      $ parserOf unitType
      $
        match (v "s")
          [ branch "State" [ "trees", "_", "_" ] $
              match (v "trees")
                [ branch "Nil" [] (ok unitType unitValue (v "s")) ]
                (Just (err unitType (expecting (call "positionAt" [] [ v "s" ]) (text "the end"))))
          ]
          Nothing
  -- a parser that reads the whole of its level
  , value "complete" (quantified [ "a" ] (pureFn (parser va) (parser va))) $ tylam [ "a" ] $ lam [ Tuple "p" (parser va) ] $
      call "bind" [ va, va ]
        [ v "p", lam [ Tuple "x" va ] (call "map" [ unitType, va ] [ lam [ Tuple "u" unitType ] (v "x"), g "end" [] ]) ]
  -- a parser run on the trees given, to the end of the position given
  , value "within" (quantified [ "a" ] (fns [ parser va, list tree, position ] (reply va)))
      $ tylam [ "a" ]
      $ lam [ Tuple "p" (parser va), Tuple "trees" (list tree), Tuple "end" position ]
      $
        runP va (call "complete" [ va ] [ v "p" ]) (call "State" [] [ v "trees", zero, v "end" ])
  -- the next tree where it is a group the predicate admits, its contents read
  -- whole by the parser given
  , value "group" (quantified [ "a" ] (fns [ string, pureFn (con "Delimiter") boolean, parser va ] (parser va)))
      $ tylam [ "a" ]
      $ lam [ Tuple "what" string, Tuple "admits" (pureFn (con "Delimiter") boolean), Tuple "p" (parser va) ]
      $ parserOf va
      $
        match (v "s")
          [ branch "State" [ "trees", "n", "end" ] $
              match (v "trees")
                [ branch "Cons" [ "t", "rest" ] $
                    match (v "t")
                      [ branch "Group" [ "d", "_", "inner", "closes" ] $
                          ifThenElse (ap (v "admits") [ v "d" ])
                            ( match (call "within" [ va ] [ v "p", v "inner", closingAt (v "closes") (v "end") ])
                                [ branch "Ok" [ "x", "_" ] (ok va (v "x") (call "State" [] [ v "rest", intOp "add" (v "n") one, v "end" ]))
                                , branch "Err" [ "f" ] (err va (v "f"))
                                ]
                                Nothing
                            )
                            (err va (expecting (call "positionAt" [] [ v "s" ]) (v "what")))
                      ]
                      (Just (err va (expecting (call "positionAt" [] [ v "s" ]) (v "what"))))
                ]
                (Just (err va (expecting (v "end") (v "what"))))
          ]
          Nothing
  , delimiterIs "isParen" "Paren"
  , delimiterIs "isBracket" "Bracket"
  , delimiterIs "isBrace" "Brace"
  , around "parens" "`(`" "isParen"
  , around "brackets" "`[`" "isBracket"
  , around "braces" "`{`" "isBrace"
  , recursive
      [ { name: "many"
        , type: quantified [ "a" ] (pureFn (parser va) (parser (list va)))
        , value: tylam [ "a" ] $ lam [ Tuple "p" (parser va) ]
            $ parserOf (list va)
            $
              match (runP va (v "p") (v "s"))
                [ branch "Err" [ "_" ] (ok (list va) (nil va) (v "s"))
                , branch "Ok" [ "x", "next" ] $
                    ifThenElse (intOp "eq" (call "consumed" [] [ v "next" ]) (call "consumed" [] [ v "s" ]))
                      ( err (list va)
                          (expecting (call "positionAt" [] [ v "s" ]) (text "progress: `many` repeats a parser that read nothing"))
                      )
                      ( match (runP (list va) (call "many" [ va ] [ v "p" ]) (v "next"))
                          [ branch "Ok" [ "xs", "after" ] (ok (list va) (cons va (v "x") (v "xs")) (v "after"))
                          , branch "Err" [ "f" ] (err (list va) (v "f"))
                          ]
                          Nothing
                      )
                ]
                Nothing
        }
      ]
  , value "sepBy" (quantified [ "a", "b" ] (fns [ parser va, parser vb ] (parser (list va))))
      $ tylam [ "a", "b" ]
      $ lam [ Tuple "p" (parser va), Tuple "sep" (parser vb) ]
      $
        call "orElse" [ list va ]
          [ call "bind" [ va, list va ]
              [ v "p"
              , lam [ Tuple "x" va ] $
                  call "map" [ list va, list va ]
                    [ lam [ Tuple "xs" (list va) ] (cons va (v "x") (v "xs"))
                    , call "many" [ va ] [ call "bind" [ vb, va ] [ v "sep", lam [ Tuple "u" vb ] (v "p") ] ]
                    ]
              ]
          , call "pure" [ list va ] [ nil va ]
          ]
  -- the trees continuing an item: up to a tree beginning a line at or left of
  -- the block's column
  , recursive
      [ { name: "itemRun"
        , type: fns [ int, list tree ] (con "ItemRun")
        , value: lam [ Tuple "column" int, Tuple "trees" (list tree) ] $
            match (v "trees")
              [ branch "Nil" [] (call "ItemRun" [] [ nil tree, nil tree ])
              , branch "Cons" [ "t", "rest" ] $
                  ifThenElse
                    ( ifThenElse (call "beginsLine" [] [ v "t" ])
                        (ifThenElse (intOp "lt" (v "column") (call "columnOf" [] [ v "t" ])) false_ true_)
                        false_
                    )
                    (call "ItemRun" [] [ nil tree, v "trees" ])
                    ( match (call "itemRun" [] [ v "column", v "rest" ])
                        [ branch "ItemRun" [ "more", "after" ] (call "ItemRun" [] [ cons tree (v "t") (v "more"), v "after" ]) ]
                        Nothing
                    )
              ]
              Nothing
        }
      ]
  -- the items of a block at a column, each with where it ends, and the trees
  -- after the block
  , recursive
      [ { name: "blockAt"
        , type: fns [ int, position, list tree ] (con "Block")
        , value: lam [ Tuple "column" int, Tuple "end" position, Tuple "trees" (list tree) ] $
            match (v "trees")
              [ branch "Nil" [] (call "Block" [] [ nil (con "LayoutItem"), nil tree ])
              , branch "Cons" [ "t", "rest" ] $
                  ifThenElse
                    ( ifThenElse (call "beginsLine" [] [ v "t" ])
                        (intOp "lt" (call "columnOf" [] [ v "t" ]) (v "column"))
                        false_
                    )
                    (call "Block" [] [ nil (con "LayoutItem"), v "trees" ])
                    ( match (call "itemRun" [] [ v "column", v "rest" ])
                        [ branch "ItemRun" [ "more", "after" ] $
                            match (call "blockAt" [] [ v "column", v "end", v "after" ])
                              [ branch "Block" [ "items", "left" ] $
                                  call "Block" []
                                    [ cons (con "LayoutItem")
                                        ( call "LayoutItem" []
                                            [ cons tree (v "t") (v "more")
                                            , call "positionAt" [] [ call "State" [] [ v "after", zero, v "end" ] ]
                                            ]
                                        )
                                        (v "items")
                                    , v "left"
                                    ]
                              ]
                              Nothing
                        ]
                        Nothing
                    )
              ]
              Nothing
        }
      ]
  -- each item read whole by the parser given
  , recursive
      [ { name: "items"
        , type: quantified [ "a" ] (fns [ parser va, list (con "LayoutItem") ] (result (list va)))
        , value: tylam [ "a" ] $ lam [ Tuple "p" (parser va), Tuple "pending" (list (con "LayoutItem")) ] $
            match (v "pending")
              [ branch "Nil" [] (call "Parsed" [ list va ] [ nil va ])
              , branch "Cons" [ "item", "rest" ] $
                  match (v "item")
                    [ branch "LayoutItem" [ "trees", "end" ] $
                        match (call "within" [ va ] [ v "p", v "trees", v "end" ])
                          [ branch "Err" [ "f" ] (call "Failed" [ list va ] [ v "f" ])
                          , branch "Ok" [ "x", "_" ] $
                              match (call "items" [ va ] [ v "p", v "rest" ])
                                [ branch "Parsed" [ "xs" ] (call "Parsed" [ list va ] [ cons va (v "x") (v "xs") ])
                                , branch "Failed" [ "f" ] (call "Failed" [ list va ] [ v "f" ])
                                ]
                                Nothing
                          ]
                          Nothing
                    ]
                    Nothing
              ]
              Nothing
        }
      ]
  , value "layout" (quantified [ "a" ] (pureFn (parser va) (parser (list va)))) $ tylam [ "a" ] $ lam [ Tuple "p" (parser va) ]
      $ parserOf (list va)
      $
        match (v "s")
          [ branch "State" [ "trees", "n", "end" ] $
              match (v "trees")
                [ branch "Nil" [] (ok (list va) (nil va) (v "s"))
                , branch "Cons" [ "t", "_" ] $
                    match (call "blockAt" [] [ call "columnOf" [] [ v "t" ], v "end", v "trees" ])
                      [ branch "Block" [ "block", "left" ] $
                          match (call "items" [ va ] [ v "p", v "block" ])
                            [ branch "Parsed" [ "xs" ] (ok (list va) (v "xs") (call "State" [] [ v "left", intOp "add" (v "n") one, v "end" ]))
                            , branch "Failed" [ "f" ] (err (list va) (v "f"))
                            ]
                            Nothing
                      ]
                      Nothing
                ]
                Nothing
          ]
          Nothing
  -- what the host calls: a parser run on a call's trees, to the position its
  -- input ends at
  , value "runParser" (quantified [ "a" ] (fns [ parser va, list tree, position ] (result va)))
      $ tylam [ "a" ]
      $ lam [ Tuple "p" (parser va), Tuple "trees" (list tree), Tuple "end" position ]
      $
        match (call "within" [ va ] [ v "p", v "trees", v "end" ])
          [ branch "Ok" [ "x", "_" ] (call "Parsed" [ va ] [ v "x" ])
          , branch "Err" [ "f" ] (call "Failed" [ va ] [ v "f" ])
          ]
          Nothing
  -- a tree as syntax, its tokens and origins kept
  , recursive
      [ { name: "nodeOf"
        , type: pureFn tree node
        , value: lam [ Tuple "t" tree ] $
            match (v "t")
              [ branch "Leaf" [ "tok" ] (call "SyntaxToken" [] [ v "tok" ])
              , branch "Group" [ "d", "open", "inner", "closes" ] $
                  call "SyntaxGroup" [] [ call "originOf" [] [ v "open" ], v "d", v "open", call "nodesOf" [] [ v "inner" ], v "closes" ]
              ]
              Nothing
        }
      , { name: "nodesOf"
        , type: pureFn (list tree) (list node)
        , value: lam [ Tuple "ts" (list tree) ] $
            match (v "ts")
              [ branch "Nil" [] (nil node)
              , branch "Cons" [ "t", "rest" ] (cons node (call "nodeOf" [] [ v "t" ]) (call "nodesOf" [] [ v "rest" ]))
              ]
              Nothing
        }
      ]
  , recursive
      [ { name: "foldr"
        , type: quantified [ "a", "b" ] (fns [ fns [ va, vb ] vb, vb, list va ] vb)
        , value: tylam [ "a", "b" ] $ lam [ Tuple "f" (fns [ va, vb ] vb), Tuple "z" vb, Tuple "xs" (list va) ] $
            match (v "xs")
              [ branch "Nil" [] (v "z")
              , branch "Cons" [ "x", "rest" ] (ap (v "f") [ v "x", call "foldr" [ va, vb ] [ v "f", v "z", v "rest" ] ])
              ]
              Nothing
        }
      ]
  , recursive
      [ { name: "foldl"
        , type: quantified [ "a", "b" ] (fns [ fns [ vb, va ] vb, vb, list va ] vb)
        , value: tylam [ "a", "b" ] $ lam [ Tuple "f" (fns [ vb, va ] vb), Tuple "z" vb, Tuple "xs" (list va) ] $
            match (v "xs")
              [ branch "Nil" [] (v "z")
              , branch "Cons" [ "x", "rest" ] (call "foldl" [ va, vb ] [ v "f", ap (v "f") [ v "z", v "x" ], v "rest" ])
              ]
              Nothing
        }
      ]
  -- syntax spliced into a quotation, in parentheses standing where the origin
  -- given does
  , value "$spliced" (quantified [ "c" ] (fns [ originRef, TApp (con "Syntax") (TVar (TyVar "c")) ] node))
      $ tylam [ "c" ]
      $ lam [ Tuple "o" originRef, Tuple "s" (TApp (con "Syntax") (TVar (TyVar "c"))) ]
      $ match (v "s")
          [ branch "Syntax" [ "nodes" ] $
              call "SyntaxGroup" [] [ v "o", g "Paren" [], bracket "(", v "nodes", cons token (bracket ")") (nil token) ]
          ]
          Nothing
  ]
  where
  bracket t = call "Token" [] [ g "GroupBracket" [], text t, nowhere, nil (con "Trivia"), v "o" ]
  nowhere = call "Range" [] [ call "Position" [] [ zero, zero ], call "Position" [] [ zero, zero ] ]

  closingAt closes end = match closes [ branch "Cons" [ "close", "_" ] (call "startOf" [] [ v "close" ]) ] (Just end)

  delimiterIs n c = value n (pureFn (con "Delimiter") boolean) $ lam [ Tuple "d" (con "Delimiter") ] $
    match (v "d") [ branch c [] true_ ] (Just false_)

  around n what predicate = value n (quantified [ "a" ] (pureFn (parser va) (parser va))) $ tylam [ "a" ] $ lam [ Tuple "p" (parser va) ] $
    call "group" [ va ] [ text what, g predicate [], v "p" ]
