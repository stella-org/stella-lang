-- | The kernel's vocabulary as generic values: what a guest's command reads as,
-- | and what an answer is written as.
-- |
-- | **The correspondence is one rule, read off the types.** A mirrored type of the
-- | compiler is its twin in `Stella.Elab`, constructor for constructor and field
-- | for field; a name is text; a qualified name is a `Name`; an array is a `List`;
-- | an optional value is a `Maybe`; a record keeps its field names; and a `Handle`
-- | is a token. Every mirrored type takes its conversion from its generic
-- | representation by that rule, so no constructor is written twice.
-- |
-- | **A token is read for its shape and nothing else.** Which session issued a
-- | handle, whether its class is the one a request wants, and whether it is stale
-- | are what resolving it settles, where the compiler holds the arena.
-- |
-- | **No conversion recurses on the host's stack.** A value is as deep as it is —
-- | a `List` as long as it is, a `KindFun` as nested — and each field is converted
-- | as a step of a trampoline rather than by a nested call, so the frame's size is
-- | the only bound.
module Stella.CLI.Session.Broker.Codec
  ( Codec
  , runCodec
  , class Guest
  , toGuest
  , fromGuest
  , tokenOfHandle
  , handleOfToken
  , decodeCommand
  , encodeAnswer
  ) where

import Prelude

import Prim as P

import Control.Alt ((<|>))
import Control.Monad.Except (ExceptT(..), runExceptT, throwError)
import Control.Monad.Rec.Class as Rec
import Control.Monad.Trampoline (Trampoline, delay, runTrampoline)
import Data.Argonaut.Core (Json, caseJsonNumber, caseJsonString, fromNumber, fromString)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic, Argument(..), Constructor(..), NoArguments(..), Product(..), Sum(..), from, to)
import Data.Int as Int
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Foreign.Object as Object
import Prim.Row as Row
import Prim.RowList (class RowToList, Cons, Nil, RowList)
import Record as Record
import Record.Builder (Builder)
import Record.Builder as Builder
import Stella.CLI.Session.Guest (Token)
import Stella.CLI.Session.Value (Step(..), WireField, WireValue(..), compareKeys, renderPath)
import Stella.CLI.Session.Value.Shape (conforms)
import Stella.Compiler.Bytecode.Module (Key(..))
import Stella.Compiler.Elaborate.Driver.Attempt (Response(..))
import Stella.Compiler.Elaborate.Environment.Catalog (EntrySort)
import Stella.Compiler.Elaborate.Protocol.Guest (elabModule, guestCommandTy)
import Stella.Compiler.Elaborate.Protocol.Guest.Shape (Descriptor)
import Stella.Compiler.Elaborate.Vocabulary.Handle (Handle(..), HandleClass(..), SessionId(..))
import Stella.Compiler.Elaborate.Vocabulary.Message (MessagePart)
import Stella.Compiler.Elaborate.Vocabulary.Request (BuildRequest, Command(..), CommandAnswer(..), HandlerRequest, KernelAnswer, KernelRequest, ObserveRequest, RecordRequest, ReportRequest, SolveRequest, TermRequest, TreeRequest)
import Stella.Compiler.Elaborate.Vocabulary.View (ConstraintView, KindView, PayloadView, TypeView)
import Stella.Compiler.TypedCore (Constant, EffName(..), Ident(..), KindVar(..), Literal, ModuleName(..), OpName(..), Qualified(..), RegionName(..), RowElemKind, RowKey, Symbol(..), Tag(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Domain (ScalarString, ScalarValue, scalarString, textOf)
import Type.Proxy (Proxy(..))

-- | A conversion: stepped on a trampoline, and failing with where and why.
type Codec a = ExceptT P.String Trampoline a

runCodec :: forall a. Codec a -> Either P.String a
runCodec c = runTrampoline (runExceptT c)

-- | A conversion left for a later step of the trampoline, so a nested one is not a
-- | nested call.
later :: forall a. (Unit -> Codec a) -> Codec a
later f = ExceptT (join (delay \_ -> runExceptT (f unit)))

refuse :: forall a. List Step -> P.String -> Codec a
refuse path problem = throwError (renderPath (Array.reverse (Array.fromFoldable path)) <> ": " <> problem)

elab :: P.String -> Qualified Ident
elab c = Qualified elabModule (Ident c)

-- | A type a guest's values stand for.
class Guest a where
  toGuest :: a -> Codec WireValue
  fromGuest :: List Step -> WireValue -> Codec a

-- Literals and names ----------------------------------------------------------------------

instance Guest P.Int where
  toGuest n = pure (WInt n)
  fromGuest path = case _ of
    WInt n -> pure n
    _ -> refuse path "an int"

instance Guest P.Number where
  toGuest n = pure (WNumber n)
  fromGuest path = case _ of
    WNumber n -> pure n
    _ -> refuse path "a number"

instance Guest P.Boolean where
  toGuest b = pure (WBoolean b)
  fromGuest path = case _ of
    WBoolean b -> pure b
    _ -> refuse path "a boolean"

instance Guest ScalarString where
  toGuest s = pure (WString s)
  fromGuest path = case _ of
    WString s -> pure s
    _ -> refuse path "a string"

instance Guest ScalarValue where
  toGuest c = pure (WChar c)
  fromGuest path = case _ of
    WChar c -> pure c
    _ -> refuse path "a char"

-- | Text the host holds. One holding an unpaired surrogate has no guest form.
instance Guest P.String where
  toGuest s = case scalarString s of
    Just text -> pure (WString text)
    Nothing -> throwError "a text holding an unpaired surrogate has no guest form"
  fromGuest path = case _ of
    WString s -> pure (textOf s)
    _ -> refuse path "a string"

instance Guest Ident where
  toGuest (Ident s) = toGuest s
  fromGuest path w = Ident <$> fromGuest path w

instance Guest TyVar where
  toGuest (TyVar s) = toGuest s
  fromGuest path w = TyVar <$> fromGuest path w

instance Guest KindVar where
  toGuest (KindVar s) = toGuest s
  fromGuest path w = KindVar <$> fromGuest path w

instance Guest OpName where
  toGuest (OpName s) = toGuest s
  fromGuest path w = OpName <$> fromGuest path w

instance Guest Symbol where
  toGuest (Symbol s) = toGuest s
  fromGuest path w = Symbol <$> fromGuest path w

instance Guest Tag where
  toGuest (Tag s) = toGuest s
  fromGuest path w = Tag <$> fromGuest path w

instance Guest RegionName where
  toGuest (RegionName s) = toGuest s
  fromGuest path w = RegionName <$> fromGuest path w

-- | What a qualified name qualifies.
class Named a where
  nameText :: a -> P.String
  named :: P.String -> a

instance Named Ident where
  nameText (Ident s) = s
  named = Ident

instance Named TyName where
  nameText (TyName s) = s
  named = TyName

instance Named EffName where
  nameText (EffName s) = s
  named = EffName

instance Named a => Guest (Qualified a) where
  toGuest (Qualified (ModuleName m) x) = do
    mw <- toGuest m
    nw <- toGuest (nameText x)
    pure (WData (elab "Name") [ mw, nw ])
  fromGuest path = case _ of
    WData ctor [ m, n ] | ctor == elab "Name" -> do
      ms <- fromGuest (Index 0 : Member "fields" : path) m
      ns <- fromGuest (Index 1 : Member "fields" : path) n
      pure (Qualified (ModuleName ms) (named ns))
    _ -> refuse path "a Name"

-- Handles ----------------------------------------------------------------------------------

instance Guest Handle where
  toGuest h = pure (WToken (tokenOfHandle h))
  fromGuest path = case _ of
    WToken token -> case handleOfToken token of
      Right h -> pure h
      Left why -> refuse (Member "token" : path) why
    _ -> refuse path "a token"

-- | `{ session, class, slot, generation }`.
tokenOfHandle :: Handle -> Token
tokenOfHandle (Handle h) = Object.fromFoldable
  [ Tuple "session" (int (sessionNumber h.session))
  , Tuple "class" (fromString (classCode h.handleClass))
  , Tuple "slot" (int h.slot)
  , Tuple "generation" (int h.generation)
  ]
  where
  int = fromNumber <<< Int.toNumber
  sessionNumber (SessionId n) = n

-- | A handle, where the token has exactly its four fields, each of its type. **What
-- | is said of one that does not is its shape, never its content.**
handleOfToken :: Token -> Either P.String Handle
handleOfToken token
  | Array.sort (Object.keys token) /= [ "class", "generation", "session", "slot" ] =
      Left "a handle's token has exactly the fields session, class, slot, and generation"
  | otherwise =
      case field "session" intOf, field "class" classOf, field "slot" intOf, field "generation" intOf of
        Just session, Just handleClass, Just slot, Just generation ->
          Right (Handle { session: SessionId session, handleClass, slot, generation })
        _, _, _, _ ->
          Left "a handle's token holds integers in the 32-bit range and one of the classes of handle"
      where
      field :: forall a. P.String -> (Json -> Maybe a) -> Maybe a
      field name read = Object.lookup name token >>= read

      intOf json = caseJsonNumber Nothing Just json >>= Int.fromNumber

      classOf json = caseJsonString Nothing Just json >>= \code -> Array.find (\c -> classCode c == code) classes

classCode :: HandleClass -> P.String
classCode = case _ of
  GoalClass -> "goal"
  TypeClass -> "type"
  ExprClass -> "expr"
  MetaClass -> "meta"
  ScopeClass -> "scope"
  BinderClass -> "binder"
  JoinClass -> "join"
  TreeClass -> "tree"
  OccurrenceClass -> "occurrence"

classes :: P.Array HandleClass
classes = [ GoalClass, TypeClass, ExprClass, MetaClass, ScopeClass, BinderClass, JoinClass, TreeClass, OccurrenceClass ]

-- Lists, options, and records ----------------------------------------------------------------

instance Guest a => Guest (Maybe a) where
  toGuest = case _ of
    Nothing -> pure (WData (elab "Nothing") [])
    Just x -> (\w -> WData (elab "Just") [ w ]) <$> later \_ -> toGuest x
  fromGuest path = case _ of
    WData ctor [] | ctor == elab "Nothing" -> pure Nothing
    WData ctor [ w ] | ctor == elab "Just" -> Just <$> later \_ -> fromGuest (Index 0 : Member "fields" : path) w
    _ -> refuse path "a Maybe"

-- | An array is a `List`: a chain of `Cons` ending in `Nil`, built and walked by a
-- | loop rather than by recursion.
instance Guest a => Guest (P.Array a) where
  toGuest xs = do
    elements <- traverse (\x -> later \_ -> toGuest x) xs
    pure (Array.foldr (\w rest -> WData (elab "Cons") [ w, rest ]) (WData (elab "Nil") []) elements)
  fromGuest path whole = do
    elements <- either' (Rec.tailRec walk { at: path, rest: whole, found: Nil })
    traverse (\(Tuple at w) -> later \_ -> fromGuest at w) elements
    where
    walk { at, rest, found } = case rest of
      WData ctor [] | ctor == elab "Nil" ->
        Rec.Done (Right (Array.reverse (Array.fromFoldable found)))
      WData ctor [ w, next ] | ctor == elab "Cons" ->
        Rec.Loop
          { at: Index 1 : Member "fields" : at
          , rest: next
          , found: Tuple (Index 0 : Member "fields" : at) w : found
          }
      _ -> Rec.Done (Left at)

    either' = case _ of
      Right elements -> pure elements
      Left at -> refuse at "a List"

instance (RowToList r rl, ToFields rl r, FromFields rl () r) => Guest (P.Record r) where
  toGuest record = do
    fields <- toFields (Proxy :: Proxy rl) record
    pure (WRecord (Array.sortBy (\a b -> compareKeys a.key b.key) fields))
  fromGuest path = case _ of
    WRecord entries -> do
      builder <- fromFields (Proxy :: Proxy rl) path entries
      pure (Builder.build builder {})
    _ -> refuse path "a record"

class ToFields :: RowList P.Type -> P.Row P.Type -> P.Constraint
class ToFields rl r where
  toFields :: Proxy rl -> P.Record r -> Codec (P.Array WireField)

instance ToFields Nil r where
  toFields _ _ = pure []

instance (IsSymbol k, Guest a, Row.Cons k a other r, ToFields rest r) => ToFields (Cons k a rest) r where
  toFields _ record = do
    value <- later \_ -> toGuest (Record.get key record)
    others <- toFields (Proxy :: Proxy rest) record
    pure (Array.cons { key: KSymbol (Symbol (reflectSymbol key)), value } others)
    where
    key = Proxy :: Proxy k

class FromFields :: RowList P.Type -> P.Row P.Type -> P.Row P.Type -> P.Constraint
class FromFields rl from to | rl -> from to where
  fromFields :: Proxy rl -> List Step -> P.Array WireField -> Codec (Builder (P.Record from) (P.Record to))

instance FromFields Nil () () where
  fromFields _ _ _ = pure identity

instance
  ( IsSymbol k
  , Guest a
  , FromFields rest from middle
  , Row.Lacks k middle
  , Row.Cons k a middle to
  ) =>
  FromFields (Cons k a rest) from to where
  fromFields _ path entries = do
    let name = reflectSymbol key
    value <- case Array.findIndex (\e -> e.key == KSymbol (Symbol name)) entries of
      Just i | Just entry <- Array.index entries i ->
        later \_ -> fromGuest (Member "value" : Index i : Member "record" : path) entry.value
      _ -> refuse (Member "record" : path) ("a record with the field " <> name)
    others <- fromFields (Proxy :: Proxy rest) path entries
    pure (Builder.insert key value <<< others)
    where
    key = Proxy :: Proxy k

-- Data types, by their generic representation ------------------------------------------------

class GuestSum rep where
  sumTo :: rep -> Codec (Tuple P.String (P.Array WireValue))
  sumFrom :: List Step -> P.String -> P.Array WireValue -> Maybe (Codec rep)

instance (GuestSum a, GuestSum b) => GuestSum (Sum a b) where
  sumTo = case _ of
    Inl a -> sumTo a
    Inr b -> sumTo b
  sumFrom path name fields =
    map (map Inl) (sumFrom path name fields) <|> map (map Inr) (sumFrom path name fields)

instance (IsSymbol name, GuestArgs a) => GuestSum (Constructor name a) where
  sumTo (Constructor a) = Tuple (reflectSymbol (Proxy :: Proxy name)) <$> argsTo a
  sumFrom path name fields
    | name == reflectSymbol (Proxy :: Proxy name) = Just do
        Tuple args taken <- argsFrom path fields 0
        if taken == Array.length fields then pure (Constructor args)
        else refuse (Member "fields" : path) (name <> " with " <> show taken <> " fields")
    | otherwise = Nothing

class GuestArgs rep where
  argsTo :: rep -> Codec (P.Array WireValue)
  argsFrom :: List Step -> P.Array WireValue -> P.Int -> Codec (Tuple rep P.Int)

instance GuestArgs NoArguments where
  argsTo _ = pure []
  argsFrom _ _ i = pure (Tuple NoArguments i)

instance Guest a => GuestArgs (Argument a) where
  argsTo (Argument a) = Array.singleton <$> later \_ -> toGuest a
  argsFrom path fields i = case Array.index fields i of
    Just w -> (\a -> Tuple (Argument a) (i + 1)) <$> later \_ -> fromGuest (Index i : Member "fields" : path) w
    Nothing -> refuse (Member "fields" : path) "a field fewer than the constructor has"

instance (GuestArgs a, GuestArgs b) => GuestArgs (Product a b) where
  argsTo (Product a b) = (<>) <$> argsTo a <*> argsTo b
  argsFrom path fields i = do
    Tuple a j <- argsFrom path fields i
    Tuple b k <- argsFrom path fields j
    pure (Tuple (Product a b) k)

genericToGuest :: forall a rep. Generic a rep => GuestSum rep => a -> Codec WireValue
genericToGuest x = do
  Tuple name fields <- sumTo (from x)
  pure (WData (elab name) fields)

genericFromGuest :: forall a rep. Generic a rep => GuestSum rep => List Step -> WireValue -> Codec a
genericFromGuest path = case _ of
  WData (Qualified m (Ident name)) fields | m == elabModule -> case sumFrom path name fields of
    Just decoded -> to <$> decoded
    Nothing -> refuse (Member "data" : path) (name <> " is no constructor of the type this place holds")
  _ -> refuse path "a constructor of Stella.Elab"

instance Guest KernelRequest where
  toGuest x = genericToGuest x
  fromGuest path w = genericFromGuest path w

instance Guest BuildRequest where
  toGuest x = genericToGuest x
  fromGuest path w = genericFromGuest path w

instance Guest TermRequest where
  toGuest x = genericToGuest x
  fromGuest path w = genericFromGuest path w

instance Guest TreeRequest where
  toGuest x = genericToGuest x
  fromGuest path w = genericFromGuest path w

instance Guest RecordRequest where
  toGuest x = genericToGuest x
  fromGuest path w = genericFromGuest path w

instance Guest HandlerRequest where
  toGuest x = genericToGuest x
  fromGuest path w = genericFromGuest path w

instance Guest SolveRequest where
  toGuest x = genericToGuest x
  fromGuest path w = genericFromGuest path w

instance Guest ObserveRequest where
  toGuest x = genericToGuest x
  fromGuest path w = genericFromGuest path w

instance Guest ReportRequest where
  toGuest x = genericToGuest x
  fromGuest path w = genericFromGuest path w

instance Guest KernelAnswer where
  toGuest x = genericToGuest x
  fromGuest path w = genericFromGuest path w

instance Guest TypeView where
  toGuest x = genericToGuest x
  fromGuest path w = genericFromGuest path w

instance Guest PayloadView where
  toGuest x = genericToGuest x
  fromGuest path w = genericFromGuest path w

instance Guest KindView where
  toGuest x = genericToGuest x
  fromGuest path w = genericFromGuest path w

instance Guest ConstraintView where
  toGuest x = genericToGuest x
  fromGuest path w = genericFromGuest path w

instance Guest RowElemKind where
  toGuest x = genericToGuest x
  fromGuest path w = genericFromGuest path w

instance Guest RowKey where
  toGuest x = genericToGuest x
  fromGuest path w = genericFromGuest path w

instance Guest Literal where
  toGuest x = genericToGuest x
  fromGuest path w = genericFromGuest path w

instance Guest MessagePart where
  toGuest x = genericToGuest x
  fromGuest path w = genericFromGuest path w

instance Guest EntrySort where
  toGuest x = genericToGuest x
  fromGuest path w = genericFromGuest path w

instance Guest Constant where
  toGuest x = genericToGuest x
  fromGuest path w = genericFromGuest path w

-- The guest's own command and answer ---------------------------------------------------------

-- | The command a guest's value reads as. **It is held to the shape of
-- | `GuestCommand` first**, by the descriptor, so a constructor of another type or
-- | a field of another shape is refused where the shape says; what is left to fail
-- | is a token that does not read as a handle.
decodeCommand :: Descriptor -> WireValue -> Either P.String Command
decodeCommand descriptor w = case conforms descriptor guestCommandTy w of
  Left problem -> Left ("command" <> renderPath problem.path <> ": " <> problem.problem)
  Right _ -> runCodec case w of
    WData ctor [ request ] | ctor == elab "Kernel" ->
      Kernel <$> fromGuest (Index 0 : Member "fields" : Nil) request
    WData ctor [] | ctor == elab "BeginTransaction" -> pure BeginTransaction
    WData ctor [] | ctor == elab "CommitTransaction" -> pure CommitTransaction
    _ -> refuse Nil "a GuestCommand"

-- | The `GuestAnswer` a command's answer is written as. **The guest holds no
-- | transaction token**: a transaction begun is answered without one, and a
-- | candidate that failed is answered as that alone.
encodeAnswer :: Response CommandAnswer -> Either P.String WireValue
encodeAnswer = case _ of
  Returned (KernelAnswered answer) ->
    runCodec ((\w -> WData (elab "Returned") [ w ]) <$> toGuest answer)
  Returned (TransactionBegun _) -> Right (WData (elab "TransactionBegun") [])
  Returned TransactionCommitted -> Right (WData (elab "TransactionCommitted") [])
  CandidateFailed _ _ -> Right (WData (elab "CandidateFailed") [])
