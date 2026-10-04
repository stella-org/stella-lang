-- | The reference policy, written in Typed Core against `Stella.Elab`: the guest the
-- | host and guest runners are compared by, branch for branch the host's reference
-- | synthesizer of the E5 tests.
-- |
-- | **It answers a goal from what the goal's site binds, then from the globals it is
-- | given, then from the monomorphic declarations carrying the attribute it is
-- | given**, the first that fits. A goal whose type is an unsolved metavariable it
-- | waits on. What the site binds and the globals given are compared with the goal's
-- | type as constructor views only — a type constructor applied to kinds — which is a
-- | candidate test and not type equality; names are compared by `Base.String.eq`. A
-- | declaration carrying the attribute is tried inside a transaction of its own:
-- | where it has no kind variable to instantiate, the hook given runs, and the
-- | candidate is referred to and its claim unified with the goal's type; one with
-- | kind variables is passed over with nothing done for it. Where nothing fits, it
-- | throws.
-- |
-- | `referenceWith globals attribute hook` is the policy; `workingOn candidate` is the
-- | hook that, where that candidate is tried, first creates a row metavariable,
-- | requires that it lacks `trying`, and warns `trying`. The synthesizers the module
-- | declares are the policy over `Main`'s names.
module Test.Steam.Reference
  ( policyModuleName
  , stringModule
  , policyModule
  , synthesizerNamed
  , spec
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl, foldr)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect.Class (liftEffect)
import Node.Buffer as Buffer
import Node.FS.Aff as FS
import Node.FS.Perms as Perms
import Stella.CLI.Session.Client as Client
import Stella.CLI.Session.Value (WireValue(..))
import Stella.Compiler.Bytecode (Dmo, encode)
import Stella.Compiler.Bytecode.Module (Key(..))
import Stella.Compiler.Elaborate.Protocol.Guest (elabModule, kernelEffect)
import Stella.Compiler.TypedCore (DecisionTree(..), Decl(..), Export(..), Expr(..), Ident(..), Literal(..), Module, ModuleName(..), Occurrence(..), Qualified(..), RowEntry(..), RowKey(..), Symbol(..), Type(..), ValueBinding, monoScheme)
import Stella.Compiler.TypedCore.Prim (booleanTy, fn, pureFn, recordTy, stringTy, unitTy)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Steam.Command (dir, pathOf)
import Test.Steam.Guest (Ran(..), call, compileGuests, construct, elab, elabRow, elabT, global, goalToken, handleT, machineWith, runGuest, text, token, unitValue, widened, wire, wireList, wireText)
import Test.Steam.Session (close', draining, hello, node, opened, streams)

-- Names and types ------------------------------------------------------------------------------

policyModuleName :: ModuleName
policyModuleName = ModuleName "Policy"

stringModuleName :: ModuleName
stringModuleName = ModuleName "Base.String"

-- | A synthesizer the module declares, by its name.
synthesizerNamed :: P.String -> Qualified Ident
synthesizerNamed = Qualified policyModuleName <<< Ident

own :: P.String -> Expr Unit
own n = Global unit (Qualified policyModuleName (Ident n)) []

var :: P.String -> Expr Unit
var n = Var unit (Ident n)

maybeOf :: Type -> Type
maybeOf = TApp (elabT "Maybe")

listT :: Type -> Type
listT = TApp (elabT "List")

unitT :: Type
unitT = TCon unitTy []

stringT :: Type
stringT = TCon stringTy []

booleanT :: Type
booleanT = TCon booleanTy []

nameT :: Type
nameT = elabT "Name"

viewT :: Type
viewT = elabT "TypeView"

kindT :: Type
kindT = elabT "KindView"

-- | What a site binds, as `localContext` lists it.
entryT :: Type
entryT = TApp (TCon recordTy [])
  (TRowExtend (RowTypeEntry (SymbolKey (Symbol "name")) stringT) (TRowExtend (RowTypeEntry (SymbolKey (Symbol "type")) handleT) TRowEmpty))

-- | What runs before a candidate is referred to: given the root scope, the goal's
-- | type, and the candidate.
hookT :: Type
hookT = pureFn handleT (pureFn handleT (fn nameT elabRow unitT))

-- Terms ----------------------------------------------------------------------------------------

occ0 :: Occurrence
occ0 = OccScrutinee 0

occ1 :: Occurrence
occ1 = OccScrutinee 1

field :: Occurrence -> P.String -> P.Int -> Occurrence
field o c i = OccField o (elab c) i

-- | A pure function applied where the ambient row is the one given.
applyAt :: Type -> Expr Unit -> P.Array (Expr Unit) -> Expr Unit
applyAt row = foldl (\f x -> App unit (widened row f) x)

-- | `Base.String.eq a b` where the ambient row is the one given.
sameText :: Type -> Expr Unit -> Expr Unit -> Expr Unit
sameText row a b = applyAt row (Global unit (Qualified stringModuleName (Ident "eq")) []) [ a, b ]

bool :: P.Boolean -> Expr Unit
bool = Lit unit <<< LitBoolean

-- | `if cond then yes else no`.
ifThen :: Expr Unit -> Expr Unit -> Expr Unit -> Expr Unit
ifThen cond yes no = Case unit [ cond ]
  (SwitchLit occ0 [ { lit: LitBoolean true, tree: Leaf yes } ] (Leaf no))

nothingOf :: Type -> Expr Unit
nothingOf = TyApp unit (global "Nothing")

justOf :: Type -> Expr Unit -> Expr Unit
justOf t x = construct elabRow "Just" [ t ] [ x ]

-- | A `List` of the type given, where the ambient row is the one given.
listAt :: Type -> Type -> P.Array (Expr Unit) -> Expr Unit
listAt row t = foldr (\x rest -> construct row "Cons" [ t ] [ x, rest ]) (TyApp unit (global "Nil") t)

-- | A `Name` of `Main`, where the ambient row is the one given.
mainName :: Type -> P.String -> Expr Unit
mainName row x = construct row "Name" [] [ text "Main", text x ]

-- | Whether the second scrutinee is the constructor given, which binds nothing.
secondIs :: P.String -> DecisionTree Unit
secondIs c = SwitchCtor occ1 [ { ctor: elab c, tree: Leaf (bool true) } ] (Just (Leaf (bool false)))

binding :: P.String -> Type -> Expr Unit -> ValueBinding Unit
binding name ty value = { name: Ident name, scheme: monoScheme ty, value, attributes: [] }

pureDecl :: P.String -> Type -> Expr Unit -> Decl Unit
pureDecl name ty value = DeclNonRec unit (binding name ty value)

lambdas :: P.Array (Tuple P.String Type) -> Expr Unit -> Expr Unit
lambdas params body = foldr (\(Tuple x t) inner -> Lam unit (Ident x) t inner) body params

-- Comparing views ------------------------------------------------------------------------------

-- | `sameName : Name -> Name -> Boolean`.
sameName :: Decl Unit
sameName = pureDecl "sameName" (pureFn nameT (pureFn nameT booleanT))
  $ lambdas [ Tuple "left" nameT, Tuple "right" nameT ]
  $
    Case unit [ var "left", var "right" ]
      ( SwitchCtor occ0
          [ { ctor: elab "Name"
            , tree: SwitchCtor occ1
                [ { ctor: elab "Name"
                  , tree: Bind (Ident "lm") (field occ0 "Name" 0) $ Bind (Ident "lx") (field occ0 "Name" 1)
                      $ Bind (Ident "rm") (field occ1 "Name" 0)
                      $ Bind (Ident "rx") (field occ1 "Name" 1)
                      $
                        Leaf (ifThen (sameText TRowEmpty (var "lm") (var "rm")) (sameText TRowEmpty (var "lx") (var "rx")) (bool false))
                  }
                ]
                Nothing
            }
          ]
          Nothing
      )

-- | `sameKind : KindView -> KindView -> Boolean`, and `sameKinds` over lists of them.
sameKinds :: Decl Unit
sameKinds = DeclRec unit
  [ binding "sameKind" (pureFn kindT (pureFn kindT booleanT))
      $ lambdas [ Tuple "a" kindT, Tuple "b" kindT ]
      $
        Case unit [ var "a", var "b" ]
          ( SwitchCtor occ0
              [ { ctor: elab "KindType", tree: secondIs "KindType" }
              , { ctor: elab "KindEffect", tree: secondIs "KindEffect" }
              , { ctor: elab "KindRow"
                , tree: SwitchCtor occ1
                    [ { ctor: elab "KindRow"
                      , tree: Bind (Ident "ea") (field occ0 "KindRow" 0) $ Bind (Ident "eb") (field occ1 "KindRow" 0) $
                          Leaf
                            ( Case unit [ var "ea", var "eb" ]
                                ( SwitchCtor occ0
                                    [ { ctor: elab "RowType", tree: secondIs "RowType" }
                                    , { ctor: elab "RowEffect", tree: secondIs "RowEffect" }
                                    ]
                                    Nothing
                                )
                            )
                      }
                    ]
                    (Just (Leaf (bool false)))
                }
              , { ctor: elab "KindFun"
                , tree: SwitchCtor occ1
                    [ { ctor: elab "KindFun"
                      , tree: Bind (Ident "a1") (field occ0 "KindFun" 0) $ Bind (Ident "a2") (field occ0 "KindFun" 1)
                          $ Bind (Ident "b1") (field occ1 "KindFun" 0)
                          $ Bind (Ident "b2") (field occ1 "KindFun" 1)
                          $
                            Leaf
                              ( ifThen (applyAt TRowEmpty (own "sameKind") [ var "a1", var "b1" ])
                                  (applyAt TRowEmpty (own "sameKind") [ var "a2", var "b2" ])
                                  (bool false)
                              )
                      }
                    ]
                    (Just (Leaf (bool false)))
                }
              , { ctor: elab "KindVar"
                , tree: SwitchCtor occ1
                    [ { ctor: elab "KindVar"
                      , tree: Bind (Ident "va") (field occ0 "KindVar" 0) $ Bind (Ident "vb") (field occ1 "KindVar" 0) $
                          Leaf (sameText TRowEmpty (var "va") (var "vb"))
                      }
                    ]
                    (Just (Leaf (bool false)))
                }
              , { ctor: elab "KindAnyRow", tree: secondIs "KindAnyRow" }
              ]
              Nothing
          )
  , binding "sameKinds" (pureFn (listT kindT) (pureFn (listT kindT) booleanT))
      $ lambdas [ Tuple "as" (listT kindT), Tuple "bs" (listT kindT) ]
      $
        Case unit [ var "as", var "bs" ]
          ( SwitchCtor occ0
              [ { ctor: elab "Nil", tree: secondIs "Nil" }
              , { ctor: elab "Cons"
                , tree: SwitchCtor occ1
                    [ { ctor: elab "Cons"
                      , tree: Bind (Ident "ka") (field occ0 "Cons" 0) $ Bind (Ident "restA") (field occ0 "Cons" 1)
                          $ Bind (Ident "kb") (field occ1 "Cons" 0)
                          $ Bind (Ident "restB") (field occ1 "Cons" 1)
                          $
                            Leaf
                              ( ifThen (applyAt TRowEmpty (own "sameKind") [ var "ka", var "kb" ])
                                  (applyAt TRowEmpty (own "sameKinds") [ var "restA", var "restB" ])
                                  (bool false)
                              )
                      }
                    ]
                    (Just (Leaf (bool false)))
                }
              ]
              Nothing
          )
  ]

-- | `sameConstructorView : TypeView -> TypeView -> Boolean`: two views that are the
-- | same type constructor applied to the same kinds. Any other view is not compared.
sameConstructorView :: Decl Unit
sameConstructorView = pureDecl "sameConstructorView" (pureFn viewT (pureFn viewT booleanT))
  $ lambdas [ Tuple "left" viewT, Tuple "right" viewT ]
  $
    Case unit [ var "left", var "right" ]
      ( SwitchCtor occ0
          [ { ctor: elab "ConType"
            , tree: SwitchCtor occ1
                [ { ctor: elab "ConType"
                  , tree: Bind (Ident "ln") (field occ0 "ConType" 0) $ Bind (Ident "lk") (field occ0 "ConType" 1)
                      $ Bind (Ident "rn") (field occ1 "ConType" 0)
                      $ Bind (Ident "rk") (field occ1 "ConType" 1)
                      $
                        Leaf
                          ( ifThen (applyAt TRowEmpty (own "sameName") [ var "ln", var "rn" ])
                              (applyAt TRowEmpty (own "sameKinds") [ var "lk", var "rk" ])
                              (bool false)
                          )
                  }
                ]
                (Just (Leaf (bool false)))
            }
          ]
          (Just (Leaf (bool false)))
      )

-- Hooks ----------------------------------------------------------------------------------------

-- | `leaveBehind : Handle -> String -{ ρ }-> Unit`: a row metavariable, a Lacks on it
-- | that stays open, and a warning, all named by the word given.
leaveBehind :: Decl Unit
leaveBehind = pureDecl "leaveBehind" (pureFn handleT (fn stringT elabRow unitT))
  $ lambdas [ Tuple "root" handleT, Tuple "word" stringT ]
  $ Let unit (Ident "row") handleT (call (global "freshMetaType") [ var "root", construct elabRow "KindRow" [] [ global "RowType" ] ])
  $ Let unit (Ident "required") unitT
      ( call (global "require")
          [ var "root", construct elabRow "LacksView" [] [ construct elabRow "SymbolKey" [] [ var "word" ], var "row" ] ]
      )
  $ call (global "warn") [ listAt elabRow (elabT "MessagePart") [ construct elabRow "TextPart" [] [ var "word" ] ] ]

-- | `nothingBefore`, the hook that does nothing.
nothingBefore :: Decl Unit
nothingBefore = pureDecl "nothingBefore" hookT $
  lambdas [ Tuple "root" handleT, Tuple "wanted" handleT, Tuple "name" nameT ] unitValue

-- | `workingOn candidate`, the hook that leaves behind what a candidate can where the
-- | candidate named is tried.
workingOn :: Decl Unit
workingOn = pureDecl "workingOn" (pureFn nameT hookT)
  $ lambdas [ Tuple "candidate" nameT, Tuple "root" handleT, Tuple "wanted" handleT, Tuple "name" nameT ]
  $
    ifThen (applyAt elabRow (own "sameName") [ var "name", var "candidate" ])
      (call (own "leaveBehind") [ var "root", text "trying" ])
      unitValue

-- The policy -----------------------------------------------------------------------------------

-- | `findLocal : TypeView -> List { name, type } -{ ρ }-> Maybe String`: the first
-- | binding of the site whose type's view is the one wanted.
findLocal :: Decl Unit
findLocal = DeclRec unit
  [ binding "findLocal" (pureFn viewT (fn (listT entryT) elabRow (maybeOf stringT)))
      $ lambdas [ Tuple "wanted" viewT, Tuple "entries" (listT entryT) ]
      $
        Case unit [ var "entries" ]
          ( SwitchCtor occ0
              [ { ctor: elab "Nil", tree: Leaf (nothingOf stringT) }
              , { ctor: elab "Cons"
                , tree: Bind (Ident "entry") (field occ0 "Cons" 0) $ Bind (Ident "rest") (field occ0 "Cons" 1) $
                    Leaf
                      ( Let unit (Ident "viewed") viewT (call (global "viewType") [ RecordSelect unit (SymbolKey (Symbol "type")) (var "entry") ])
                          ( ifThen (applyAt elabRow (own "sameConstructorView") [ var "wanted", var "viewed" ])
                              (justOf stringT (RecordSelect unit (SymbolKey (Symbol "name")) (var "entry")))
                              (call (own "findLocal") [ var "wanted", var "rest" ])
                          )
                      )
                }
              ]
              Nothing
          )
  ]

-- | `findGlobal : TypeView -> List Name -{ ρ }-> Maybe Name`: the first of the
-- | globals given that the catalog holds with no kind variable, at the view wanted.
findGlobal :: Decl Unit
findGlobal = DeclRec unit
  [ binding "findGlobal" (pureFn viewT (fn (listT nameT) elabRow (maybeOf nameT)))
      $ lambdas [ Tuple "wanted" viewT, Tuple "names" (listT nameT) ]
      $
        Case unit [ var "names" ]
          ( SwitchCtor occ0
              [ { ctor: elab "Nil", tree: Leaf (nothingOf nameT) }
              , { ctor: elab "Cons"
                , tree: Bind (Ident "name") (field occ0 "Cons" 0) $ Bind (Ident "rest") (field occ0 "Cons" 1) $
                    Leaf
                      ( Case unit [ call (global "lookupGlobal") [ var "name" ] ]
                          ( SwitchCtor occ0
                              [ { ctor: elab "Just"
                                , tree: SwitchCtor (OccRecordField declared (SymbolKey (Symbol "kindVars")))
                                    [ { ctor: elab "Nil"
                                      , tree: Bind (Ident "scheme") (OccRecordField declared (SymbolKey (Symbol "scheme"))) $
                                          Leaf
                                            ( Let unit (Ident "viewed") viewT (call (global "viewType") [ var "scheme" ])
                                                ( ifThen (applyAt elabRow (own "sameConstructorView") [ var "wanted", var "viewed" ])
                                                    (justOf nameT (var "name"))
                                                    next
                                                )
                                            )
                                      }
                                    ]
                                    (Just (Leaf next))
                                }
                              ]
                              (Just (Leaf next))
                          )
                      )
                }
              ]
              Nothing
          )
  ]
  where
  declared = field occ0 "Just" 0
  next = call (own "findGlobal") [ var "wanted", var "rest" ]

-- | `trying : Hook -> Handle -> Handle -> Name -{ ρ }-> Maybe Handle`, given the
-- | hook, the root scope, the goal's type, and the candidate.
trying :: Decl Unit
trying = pureDecl "trying" (pureFn hookT (pureFn handleT (pureFn handleT (fn nameT elabRow (maybeOf handleT)))))
  $ lambdas [ Tuple "hook" hookT, Tuple "root" handleT, Tuple "wanted" handleT, Tuple "name" nameT ]
  $
    Case unit [ call (global "lookupGlobal") [ var "name" ] ]
      ( SwitchCtor occ0
          [ { ctor: elab "Just"
            , tree: SwitchCtor (OccRecordField (field occ0 "Just" 0) (SymbolKey (Symbol "kindVars")))
                [ { ctor: elab "Nil", tree: Leaf fitting } ]
                (Just (Leaf (nothingOf handleT)))
            }
          ]
          (Just (Leaf (nothingOf handleT)))
      )
  where
  fitting =
    Let unit (Ident "hooked") unitT (call (var "hook") [ var "root", var "wanted", var "name" ])
      $ Let unit (Ident "referred") handleT (call (global "globalRef") [ var "root", var "name", TyApp unit (global "Nil") kindT ])
      $ Let unit (Ident "claimed") handleT (call (global "typeOf") [ var "referred" ])
      $ Let unit (Ident "unified") unitT (call (global "unify") [ var "root", var "claimed", var "wanted" ])
      $ justOf handleT (var "referred")

-- | `search : Hook -> Handle -> Handle -> List Name -{ ρ }-> Maybe Handle`: each
-- | candidate tried in a transaction of its own, in order, the first that fits taken.
search :: Decl Unit
search = DeclRec unit
  [ binding "search" (pureFn hookT (pureFn handleT (pureFn handleT (fn (listT nameT) elabRow (maybeOf handleT)))))
      $ lambdas [ Tuple "hook" hookT, Tuple "root" handleT, Tuple "wanted" handleT, Tuple "names" (listT nameT) ]
      $
        Case unit [ var "names" ]
          ( SwitchCtor occ0
              [ { ctor: elab "Nil", tree: Leaf (nothingOf handleT) }
              , { ctor: elab "Cons"
                , tree: Bind (Ident "candidate") (field occ0 "Cons" 0) $ Bind (Ident "rest") (field occ0 "Cons" 1) $
                    Leaf tried
                }
              ]
              Nothing
          )
  ]
  where
  tried = Case unit
    [ call (TyApp unit (global "transact") (maybeOf handleT))
        [ Lam unit (Ident "u") unitT (call (own "trying") [ var "hook", var "root", var "wanted", var "candidate" ]) ]
    ]
    ( SwitchCtor occ0
        [ { ctor: elab "Just"
          , tree: SwitchCtor inner
              [ { ctor: elab "Just", tree: Bind (Ident "found") (field inner "Just" 0) (Leaf (justOf handleT (var "found"))) } ]
              (Just (Leaf next))
          }
        ]
        (Just (Leaf next))
    )

  inner = field occ0 "Just" 0
  next = call (own "search") [ var "hook", var "root", var "wanted", var "rest" ]

-- | `referenceWith : List Name -> Name -> Hook -> Handle -{ ρ }-> Handle`, the
-- | policy.
referenceWith :: Decl Unit
referenceWith = pureDecl "referenceWith" (pureFn (listT nameT) (pureFn nameT (pureFn hookT (fn handleT elabRow handleT))))
  $ lambdas [ Tuple "globals" (listT nameT), Tuple "attribute" nameT, Tuple "hook" hookT, Tuple "goal" handleT ]
  $ Let unit (Ident "root") handleT (call (global "rootScope") [ unitValue ])
  $ Let unit (Ident "goalType") handleT (call (global "goalType") [ var "goal" ])
  $ Case unit [ call (global "viewType") [ var "goalType" ] ]
      ( SwitchCtor occ0
          [ { ctor: elab "MetaType"
            , tree: Bind (Ident "waited") (field occ0 "MetaType" 0)
                (Leaf (call (TyApp unit (global "postpone") handleT) [ listAt elabRow handleT [ var "waited" ] ]))
            }
          ]
          (Just (Bind (Ident "view") occ0 (Leaf fromSite)))
      )
  where
  fromSite = Case unit [ call (own "findLocal") [ var "view", call (global "localContext") [ unitValue ] ] ]
    ( SwitchCtor occ0
        [ { ctor: elab "Just", tree: Bind (Ident "local") (field occ0 "Just" 0) (Leaf (call (global "localVariable") [ var "root", var "local" ])) } ]
        (Just (Leaf fromGlobals))
    )

  fromGlobals = Case unit [ call (own "findGlobal") [ var "view", var "globals" ] ]
    ( SwitchCtor occ0
        [ { ctor: elab "Just"
          , tree: Bind (Ident "found") (field occ0 "Just" 0)
              (Leaf (call (global "globalRef") [ var "root", var "found", TyApp unit (global "Nil") kindT ]))
          }
        ]
        (Just (Leaf fromAttribute))
    )

  fromAttribute = Case unit
    [ call (own "search") [ var "hook", var "root", var "goalType", call (global "declsWithAttr") [ var "attribute" ] ] ]
    ( SwitchCtor occ0
        [ { ctor: elab "Just", tree: Bind (Ident "answer") (field occ0 "Just" 0) (Leaf (var "answer")) } ]
        (Just (Leaf thrown))
    )

  thrown = call (TyApp unit (global "throw") handleT)
    [ listAt elabRow (elabT "MessagePart")
        [ construct elabRow "TextPart" [] [ text "nothing the site binds, no global given, and no monomorphic declaration carrying the attribute" ]
        , construct elabRow "NamePart" [] [ var "attribute" ]
        , construct elabRow "TextPart" [] [ text "fits the type" ]
        , construct elabRow "TypePart" [] [ var "goalType" ]
        ]
    ]

-- The synthesizers ---------------------------------------------------------------------------

-- | `synthesizer (referenceWith globals Main.candidate hook)`, under the name given, the
-- | globals named in `Main`.
synthesizing :: P.String -> P.Array P.String -> Expr Unit -> Decl Unit
synthesizing name globals hook = pureDecl name (fn handleT (TRowExtend (RowEffectEntry kernelEffect []) TRowEmpty) handleT) $
  App unit (global "synthesizer")
    (applyAt TRowEmpty (own "referenceWith") [ listAt TRowEmpty nameT (map (mainName TRowEmpty) globals), mainName TRowEmpty "candidate", hook ])

-- | Answering from `Main.one`, then from the candidates.
answering :: Decl Unit
answering = synthesizing "answering" [ "one" ] (own "nothingBefore")

-- | Answering from the candidates alone, `Main.cand1` leaving behind what a
-- | candidate can where it is tried.
searching :: Decl Unit
searching = synthesizing "searching" [] (App unit (own "workingOn") (mainName TRowEmpty "cand1"))

-- The modules ----------------------------------------------------------------------------------

-- | `module Base.String where foreign eq`, which the interpreter carries out.
stringModule :: Module Unit
stringModule =
  { annotation: unit
  , name: stringModuleName
  , imports: []
  , exports: [ ExportValue (Ident "eq") ]
  , decls:
      [ DeclForeign unit
          { name: Ident "eq"
          , scheme: monoScheme (pureFn stringT (pureFn stringT booleanT))
          , attributes: []
          }
      ]
  }

policyModule :: Module Unit
policyModule =
  { annotation: unit
  , name: policyModuleName
  , imports: [ elabModule, stringModuleName ]
  , exports: []
  , decls:
      [ sameName
      , sameKinds
      , sameConstructorView
      , leaveBehind
      , nothingBefore
      , workingOn
      , findLocal
      , findGlobal
      , trying
      , search
      , referenceWith
      , answering
      , searching
      ]
  }

-- The cases ----------------------------------------------------------------------------------

compiled :: Either P.String (P.Array Dmo)
compiled = compileGuests [ stringModule, policyModule ]

spec :: Spec Unit
spec = describe "the reference policy, a guest" do
  it "compiles against Stella.Elab and Base.String, and a session loads it" do
    case compiled of
      Left err -> fail ("the policy did not compile: " <> err)
      Right [ string, policy ] -> do
        FS.mkdir' dir { recursive: true, mode: Perms.mkPerms Perms.all Perms.all Perms.all }
        write "BaseStringEq" string
        write "Policy" policy
        s <- streams
        opened
          { command: "node"
          , args: [ "steam/index.dev.js", "session" ]
          , output: draining s
          , hello: hello { offers = [ "modules", "invoke", "kernel" ] }
          }
          \session -> do
            node (Client.load session (pathOf "BaseStringEq")) >>= shouldEqual (Right (Right "Base.String"))
            node (Client.load session (pathOf "Policy")) >>= shouldEqual (Right (Right "Policy"))
            close' session >>= shouldEqual (Right unit)
      Right other -> fail ("expected two modules, got " <> show (Array.length other))

  it "waits on its goal's type while that is a metavariable" do
    withPolicy \machine -> do
      ran <- runGuest machine (synthesizerNamed "answering") [ goalToken ]
        [ handleAnswer "root", handleAnswer "goalType", viewAnswer (wire "MetaType" [ tokenValue "meta" ]) ]
      ran `shouldEqual` Unanswered
        [ rootScope
        , goalTypeOfGoal
        , viewTypeOf "goalType"
        , kernel "ReportRequest" (wire "Postpone" [ wireList [ tokenValue "meta" ] ])
        ]

  it "answers from what the site binds, comparing names and kinds" do
    withPolicy \machine -> do
      ran <- runGuest machine (synthesizerNamed "answering") [ goalToken ]
        [ handleAnswer "root"
        , handleAnswer "goalType"
        , viewAnswer (int [ wire "KindRow" [ wire "RowType" [] ] ])
        , returned (wire "ContextAnswer" [ wireList [ entry "y" "ty", entry "x" "tx" ] ])
        , viewAnswer (int [ wire "KindRow" [ wire "RowEffect" [] ] ])
        , viewAnswer (int [ wire "KindRow" [ wire "RowType" [] ] ])
        , handleAnswer "local"
        ]
      ran `shouldEqual` Returned
        [ rootScope
        , goalTypeOfGoal
        , viewTypeOf "goalType"
        , kernel "ObserveRequest" (wire "LocalContext" [])
        , viewTypeOf "ty"
        , viewTypeOf "tx"
        , kernel "TermRequest" (wire "LocalVariable" [ tokenValue "root", wireText "x" ])
        ]
        (tokenValue "local")

  it "answers from the globals given where nothing the site binds fits" do
    withPolicy \machine -> do
      ran <- runGuest machine (synthesizerNamed "answering") [ goalToken ]
        [ handleAnswer "root"
        , handleAnswer "goalType"
        , viewAnswer (int [])
        , returned (wire "ContextAnswer" [ wireList [ entry "x" "tx" ] ])
        , viewAnswer (wire "ConType" [ wire "Name" [ wireText "Prim", wireText "Boolean" ], wireList [] ])
        , returned (wire "DeclAnswer" [ wire "Just" [ declared "one" [] ] ])
        , viewAnswer (int [])
        , handleAnswer "global"
        ]
      ran `shouldEqual` Returned
        [ rootScope
        , goalTypeOfGoal
        , viewTypeOf "goalType"
        , kernel "ObserveRequest" (wire "LocalContext" [])
        , viewTypeOf "tx"
        , kernel "ObserveRequest" (wire "LookupGlobal" [ mainWire "one" ])
        , viewTypeOf "scheme"
        , kernel "TermRequest" (wire "GlobalRef" [ tokenValue "root", mainWire "one", wireList [] ])
        ]
        (tokenValue "global")

  it "passes over a candidate with kind variables in a transaction of its own, and throws where none is left" do
    withPolicy \machine -> do
      ran <- runGuest machine (synthesizerNamed "searching") [ goalToken ]
        [ handleAnswer "root"
        , handleAnswer "goalType"
        , viewAnswer (int [])
        , returned (wire "ContextAnswer" [ wireList [] ])
        , returned (wire "NamesAnswer" [ wireList [ mainWire "cand0" ] ])
        , wire "TransactionBegun" []
        , returned (wire "DeclAnswer" [ wire "Just" [ declared "cand0" [ wireText "k" ] ] ])
        , wire "TransactionCommitted" []
        ]
      ran `shouldEqual` Unanswered
        [ rootScope
        , goalTypeOfGoal
        , viewTypeOf "goalType"
        , kernel "ObserveRequest" (wire "LocalContext" [])
        , kernel "ObserveRequest" (wire "DeclsWithAttr" [ mainWire "candidate" ])
        , wire "BeginTransaction" []
        , kernel "ObserveRequest" (wire "LookupGlobal" [ mainWire "cand0" ])
        , wire "CommitTransaction" []
        , kernel "ReportRequest"
            ( wire "Throw"
                [ wireList
                    [ wire "TextPart" [ wireText "nothing the site binds, no global given, and no monomorphic declaration carrying the attribute" ]
                    , wire "NamePart" [ mainWire "candidate" ]
                    , wire "TextPart" [ wireText "fits the type" ]
                    , wire "TypePart" [ tokenValue "goalType" ]
                    ]
                ]
            )
        ]

  it "leaves behind what a candidate can only where the candidate named is tried" do
    withPolicy \machine -> do
      ran <- runGuest machine (synthesizerNamed "searching") [ goalToken ]
        [ handleAnswer "root"
        , handleAnswer "goalType"
        , viewAnswer (int [])
        , returned (wire "ContextAnswer" [ wireList [] ])
        , returned (wire "NamesAnswer" [ wireList [ mainWire "cand2", mainWire "cand1" ] ])
        , wire "TransactionBegun" []
        , returned (wire "DeclAnswer" [ wire "Just" [ declared "cand2" [] ] ])
        , handleAnswer "ref2"
        , handleAnswer "claim2"
        , wire "CandidateFailed" []
        , wire "TransactionBegun" []
        , returned (wire "DeclAnswer" [ wire "Just" [ declared "cand1" [] ] ])
        , handleAnswer "row"
        , unitAnswer
        , unitAnswer
        , handleAnswer "ref1"
        , handleAnswer "claim1"
        , unitAnswer
        , wire "TransactionCommitted" []
        ]
      ran `shouldEqual` Returned
        [ rootScope
        , goalTypeOfGoal
        , viewTypeOf "goalType"
        , kernel "ObserveRequest" (wire "LocalContext" [])
        , kernel "ObserveRequest" (wire "DeclsWithAttr" [ mainWire "candidate" ])
        , wire "BeginTransaction" []
        , kernel "ObserveRequest" (wire "LookupGlobal" [ mainWire "cand2" ])
        , kernel "TermRequest" (wire "GlobalRef" [ tokenValue "root", mainWire "cand2", wireList [] ])
        , kernel "ObserveRequest" (wire "TypeOf" [ tokenValue "ref2" ])
        , kernel "SolveRequest" (wire "Unify" [ tokenValue "root", tokenValue "claim2", tokenValue "goalType" ])
        , wire "BeginTransaction" []
        , kernel "ObserveRequest" (wire "LookupGlobal" [ mainWire "cand1" ])
        , kernel "SolveRequest" (wire "FreshMetaType" [ tokenValue "root", wire "KindRow" [ wire "RowType" [] ] ])
        , kernel "SolveRequest" (wire "Require" [ tokenValue "root", wire "LacksView" [ wire "SymbolKey" [ wireText "trying" ], tokenValue "row" ] ])
        , kernel "ReportRequest" (wire "Warn" [ wireList [ wire "TextPart" [ wireText "trying" ] ] ])
        , kernel "TermRequest" (wire "GlobalRef" [ tokenValue "root", mainWire "cand1", wireList [] ])
        , kernel "ObserveRequest" (wire "TypeOf" [ tokenValue "ref1" ])
        , kernel "SolveRequest" (wire "Unify" [ tokenValue "root", tokenValue "claim1", tokenValue "goalType" ])
        , wire "CommitTransaction" []
        ]
        (tokenValue "ref1")
  where
  write name dmo = case encode dmo of
    Left err -> fail ("could not encode " <> name <> ": " <> show err)
    Right bytes -> liftEffect (Buffer.fromArray bytes) >>= FS.writeFile (pathOf name)

  withPolicy k = case compiled of
    Left err -> fail ("the policy did not compile: " <> err)
    Right dmos -> machineWith dmos >>= k

  tokenValue t = WToken (token t)
  returned answer = wire "Returned" [ answer ]
  unitAnswer = returned (wire "UnitAnswer" [])
  handleAnswer t = returned (wire "HandleAnswer" [ tokenValue t ])
  viewAnswer view = returned (wire "TypeViewAnswer" [ view ])
  kernel family request = wire "Kernel" [ wire family [ request ] ]
  rootScope = kernel "BuildRequest" (wire "RootScope" [])
  goalTypeOfGoal = kernel "ObserveRequest" (wire "GoalType" [ WToken goalToken ])
  viewTypeOf t = kernel "ObserveRequest" (wire "ViewType" [ tokenValue t ])
  mainWire x = wire "Name" [ wireText "Main", wireText x ]
  int kinds = wire "ConType" [ wire "Name" [ wireText "Prim", wireText "Int" ], wireList kinds ]
  entry name t = WRecord [ recordField "name" (wireText name), recordField "type" (tokenValue t) ]
  recordField k v = { key: KSymbol (Symbol k), value: v }
  declared name kindVars = WRecord
    [ recordField "attributes" (wireList [])
    , recordField "kindVars" (wireList kindVars)
    , recordField "name" (mainWire name)
    , recordField "scheme" (tokenValue "scheme")
    , recordField "sort" (wire "ValueEntry" [])
    ]
