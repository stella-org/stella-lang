# Examples

## A vertical slice

The surface program:

```purescript
module Main where

import Base.Int

data List a = Nil | Cons a (List a)

sum :: List Int -> Int
sum = case _ of
  Nil       -> 0
  Cons x xs -> Base.Int.add x (sum xs)

result :: Int
result = sum (Cons 1 (Cons 2 (Cons 3 Nil)))
```

The corresponding Core:

```text
module Main where

import Base.Int

data List (a : Type) = Nil | Cons a (List a)
  -- Main.Nil  : forall (a : Type). List a                    tag 0, arity 0
  -- Main.Cons : forall (a : Type). a -> List a -> List a     tag 1, arity 2

rec {
  Main.sum : List Int -{()}-> Int
    = λ (xs : List Int).
        case (xs) of
          switchCtor s0 {
            Main.Nil  -> leaf 0
            Main.Cons -> bind x  = s0 ! Main.Cons . 0 in
                         bind ys = s0 ! Main.Cons . 1 in
                         leaf (Base.Int.add x (Main.sum ys))
          }
}

nonrec Main.result : Int
  = Main.sum ( Main.Cons [Int] 1
                 ( Main.Cons [Int] 2
                     ( Main.Cons [Int] 3 ( Main.Nil [Int] ) ) ) )
```

Points to observe.

- **No type class appears.** The addition is a direct call to `Base.Int.add : Int -> Int -> Int`, which is why the surface writes it out and imports `Base.Int` to reach it. `+` becomes available once `Prelude` provides a `Semiring` class and an operator alias for its method; this position then holds `select add` applied to a dictionary, and the shape of Core is unchanged.
- Every effect row is `()`. Since `switchCtor` exhausts the constructors there is no `fail τ`, and no `Partial` effect.
- The right-hand side of the `rec` group is a `λ`, which reads nothing as it is initialized, so the group is initialization-safe ([Initialization Safety](10-Initialization.md)).
- Type abstraction and application appear in `Main.Cons [Int]`. CoreFn has no counterpart.
- The decision tree makes the order explicit: dispatch on the tag, bind the fields, then the body. CoreFn's `Case` does not carry that order.
- Kind schemes are empty everywhere, so no `[[κ̄]]` appears.
- **`Main.result` is not an entry point.** A module is executable only when it provides `main : IO Unit`. This slice has no effects, so its top-level value is an ordinary pure value that a test harness evaluates.

## A recursive record

A record of closures referring to itself, the shape a dictionary takes:

```text
rec {
  Main.dict : Record ( twice : Int -> Int, once : Int -> Int )
    = extend twice (λ (n : Int). (select once Main.dict) ((select once Main.dict) n))
        (extend once (λ (n : Int). Base.Int.add n 1) {})
}

nonrec Main.twice : Int
  = (select twice Main.dict) 5
```

Points to observe.

- **`Main.dict` is no `FunVal`**, and the group is admitted all the same: it reads `Main.dict` only under its λs, which nothing applies while the group is initialized ([Initialization Safety](10-Initialization.md)).
- It is installed as a `run`, evaluated at its place in the order written, and `Main.twice` is 7 ([Translation](../04-MiddleEnd/02-Translation.md)).
- `rec { Main.xs = Main.Cons [Int] 1 Main.xs }` is refused: the constructor's field reads `Main.xs` as it is built.

## Rows

A row-polymorphic merge. `merge` is a term constructor, so this is the shape of its rule rather than a declaration ([Prim and Base](../06-Modules/02-Prim-and-Base.md)):

```text
merge : forall (r : Row Type). forall (s : Row Type).
        r # s => Record r -> Record s -> Record ( r ⊎ s )
```

In surface syntax:

```purescript
merge   :: { ...r } -> { ...s } -> { ...r, ...s }
withAge :: { ... } -> Int -> { age :: Int, ... }
getName :: { name :: String, ... } -> String
```

`merge` names its variables because `r` and `s` are independent. The two anonymous spreads of `withAge` denote the same variable, so "add `age` while preserving the other fields" needs no name. Neither `Disjoint` nor `Lacks` is written, yet both are present after desugaring.

The Core of `withAge`:

```text
nonrec Example.withAge
  : forall (r : Row Type). age ∉ r => Record r -> Int -> Record ( age : Int | r )
  = Λ (r : Row Type). Λ (_ : age ∉ r).
      λ (rec : Record r). λ (n : Int).
        extend age n rec
```

At a call site passing a `Record ( name : String )`, the elaborator decides `age ∉ ( name : String )` and emits `[•]`.

```text
Example.withAge [ ( name : String ) ] [•]
  ( extend name "stella" {} )
  30
  : Record ( age : Int, name : String )
```

`r` need not be closed. If `r` is a universally quantified variable of some other function, the same call succeeds provided the context assumes `age ∉ r`. No instance search occurs.

## A kind-polymorphic data type

The representative case in which a kind scheme is non-empty:

```text
data Proxy forall k. (a : k) = Proxy

nonrec Example.tyProxy
  : Proxy [[Type]] Int
  = Proxy [[Type]] [Int]

nonrec Example.rowProxy
  : Proxy [[Row Type]] ( x : Int )
  = Proxy [[Row Type]] [( x : Int )]
```

`[[…]]` instantiates kinds and `[…]` instantiates types. Type constructors and data constructors carry independent kind schemes, so both positions are instantiated.

Surface syntax writes neither. Writing `Proxy` leaves the kind to the elaborator; Core makes it explicit so that the type checker does not have to infer it.

A kind-polymorphic **function** is not expressible, since that would require a kind quantifier in the type of a value. In v0.1 `Proxy` serves only to carry a type argument.

## Effects

Surface syntax:

```purescript
effect Console where
  log :: String ->* Unit

effect State s where
  get :: Unit ->* s
  put :: s ->* Unit

-- no labels; Lacks constraints are supplied implicitly
tick   :: Unit -> Int / {| State Int, ... |}
report :: Int -> Unit / {| Console, State Int, ... |}
pure2  :: Int -> Int                            -- the same as {||}
```

The Core of `tick`, with everything implicit made explicit:

```text
effect State (s : Type) where
  get : Unit ->* s
  put : s ->* Unit

nonrec Example.tick
  : forall (e : Row Effect). State ∉ e =>
    Unit -{ ( State Int | e ) }-> Int
  = Λ (e : Row Effect). Λ (_ : State ∉ e).
      λ (_ : Unit).
        let n : Int  = perform State.get [] Prim.Unit in
        let _ : Unit = perform State.put []
                         ( ( openEff [( State Int | e )]
                               ( ( openEff [( State Int | e )] Base.Int.add ) n ) ) 1 ) in
        n
```

**The arithmetic is widened before it is applied.** `Base.Int.add` has pure
arrows while the ambient row here is `( State Int | e )`, and an application
requires the two to agree; containment is never inserted (D8). Currying is what
makes it two `openEff`s rather than one, since each argument consumes an arrow
of its own. An author writes none of this, the elaborator inserting it ([Typing
Rules](05-Typing-Rules.md)).

A handler for `Partial`, interpreting abortion into `Maybe`:

```text
-- Prelude declares `Maybe`, whose identity it owns
data Maybe (a : Type) = Nothing | Just a
  -- Prelude.Nothing : forall (a : Type). Maybe a            tag 0, arity 0
  -- Prelude.Just    : forall (a : Type). a -> Maybe a       tag 1, arity 1

nonrec Example.toMaybe
  : forall (e : Row Effect). Partial ∉ e => forall (a : Type).
    ( Unit -{ ( Partial | e ) }-> a ) -{e}-> Maybe a
  = Λ (e : Row Effect). Λ (_ : Partial ∉ e). Λ (a : Type).
      λ (thunk : Unit -{ ( Partial | e ) }-> a).
        handle ( thunk Prim.Unit ) with
          { handles Partial
          ; return (x : a) -> ( openEff [e] ( Prelude.Just [a] ) ) x
          ; full abort [b] (_ : Unit, k : b -{e}-> Maybe a) ->
              Prelude.Nothing [a]
          }
```

Abandoning `k` and returning `Nothing` realizes the abortion. The effect of PureScript's `Partial` class is obtained with no class mechanism at all.

The clause is `full` because it supplies the answer (D28). This handler returns `Maybe a` where the computation it handles returns `a`, and only a `full` clause names that answer. `abort`'s polymorphic resume type is no obstacle in itself: a `fast` clause for it can translate the abortion into another effect, which is not available here, the target being a pure type rather than another capability ([Effects](03-Effects.md)).

A data constructor has pure arrows by declaration, so `Prelude.Just` is widened
in the return clause for the same reason the arithmetic is above: the clause is
typed at `e`, the row outside the handle. `Prelude.Nothing [a]` needs no
widening, being an instantiation rather than an application.

In surface syntax:

```purescript
toMaybe :: (Unit -> a / {| Partial, ... |}) -> Maybe a / {| ... |}
toMaybe thunk = handle thunk () with
  Partial -> | abort _ = Nothing
             | return x = Just x
```

Both anonymous spreads denote the same variable, so "remove `Partial`, leave the rest" reads directly. Neither `forall` nor `∉` is written, though the Core above has both.

This handler stays effect-polymorphic because it abandons the continuation rather than sequencing a native action before it. A terminal interpreter producing `IO` takes a closed row instead, and keeps the continuation beyond its clause, handing it to `Base.IO.bind`, so its clause is `reifiable full` ([Effect Handlers](../02-Surface-Language/02-Effect-Handlers.md#clause-forms)):

```purescript
import Base.Continuation as Continuation

runConsoleIO :: forall a. (Unit -> a / {| Console |}) -> IO a
runConsoleIO thunk = handle thunk () with
  Console ->
    | reifiable full log s k = Base.IO.bind (Js.Console.log s) (Continuation.continue k)
    | return x = Base.IO.pure x
```
