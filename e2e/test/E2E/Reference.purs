-- | The reference policy, built from `fixtures/source/guests/policy` against
-- | `Stella.Elab`: the guest the host and guest runners are compared by, branch for
-- | branch the host's reference synthesizer of the E5 tests.
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
module Test.E2E.Reference
  ( policyModules
  , synthesizerNamed
  , spec
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Effect.Class (liftEffect)
import Node.Buffer as Buffer
import Node.FS.Aff as FS
import Node.FS.Perms as Perms
import Stella.CLI.Session.Client as Client
import Stella.CLI.Session.Value (WireValue(..))
import Stella.Compiler.Bytecode (Dmo, encode)
import Stella.Compiler.Bytecode.Module (Key(..))
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..), Symbol(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import E2E.Build (Sources, builtFrom)
import Test.E2E.Command (dir, pathOf)
import Test.E2E.Guest (Ran(..), goalToken, machineWith, runGuest, token, wire, wireList, wireText)
import Test.E2E.Session (close', draining, hello, node, opened, streams)

-- Names and types ------------------------------------------------------------------------------

policyModuleName :: ModuleName
policyModuleName = ModuleName "Policy"

-- | A synthesizer the module declares, by its name.
synthesizerNamed :: P.String -> Qualified Ident
synthesizerNamed = Qualified policyModuleName <<< Ident

-- | `Base.String` and `Policy`, built, in the order built: what `machineWith` is
-- | given, `Stella.Elab` being what it installs.
policyModules :: Sources -> Either P.String (P.Array Dmo)
policyModules sources = builtFrom sources [ "guests/policy" ]

-- The cases ----------------------------------------------------------------------------------

spec :: Sources -> Spec Unit
spec sources = describe "the reference policy, a guest" do
  it "compiles against Stella.Elab and Base.String, and a session loads it" do
    case policyModules sources of
      Left err -> fail ("the policy did not compile: " <> err)
      Right [ string, policy ] -> do
        FS.mkdir' dir { recursive: true, mode: Perms.mkPerms Perms.all Perms.all Perms.all }
        write "Base.String" string
        write "Policy" policy
        s <- streams
        opened
          { command: "node"
          , args: [ "steam/index.dev.js", "session" ]
          , output: draining s
          , hello: hello { offers = [ "modules", "invoke", "kernel" ] }
          }
          \session -> do
            node (Client.load session (pathOf "Base.String")) >>= shouldEqual (Right (Right "Base.String"))
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

  withPolicy k = case policyModules sources of
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
