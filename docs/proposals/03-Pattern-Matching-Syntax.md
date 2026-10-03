# Surface Syntax for Pattern Matching, or `case` expressions

Status: Accepted

## What is this?

### Background

The syntax basically follows PureScript's case expressions. It departs from PureScript in where
matching may be written, and adds two things of its own: or-patterns and guard blocks.

### Proposal

#### 1. Matching is written with `case`, and only there

A function is defined by **a single equation**. Definitions by several pattern-matching equations
are not part of the language; a function that dispatches on its arguments is written with an
anonymous `case`, whose `_` scrutinees become the lambda's parameters from left to right.

```stella
fromMaybe :: forall a. a -> Maybe a -> a
fromMaybe = case _, _ of
  _, Just a -> a
  a, _ -> a
```

A `_` may stand among ordinary scrutinees (`case _, x of`), and becomes a parameter all the same.

**A binding position takes only an irrefutable pattern.** The rule is uniform across the parameters
of a function definition, the parameters of a lambda, the bindings of a `let`, and the operation
arguments of a handler clause. An irrefutable pattern is one of

- a variable or `_`;
- a record pattern whose fields are all irrefutable;
- a tuple pattern whose components are all irrefutable;
- a constructor pattern of a data type with exactly one constructor, whose arguments are all
  irrefutable, nested to any depth;
- an as-pattern `x@p` or an annotated pattern `(p :: τ)` whose `p` is irrefutable.

```stella
data Foo = Foo Int

unFoo :: Foo -> Int
unFoo (Foo n) = n          -- unFoo = \x -> case x of Foo n -> n
```

A literal, a constructor of a type with several constructors, and a variant tag can fail, and are
a compile error in a binding position, with a diagnostic pointing to `case`. So can an or-pattern,
even one whose choices cover every constructor of a type, such as `(True | False)`: the table says
which constructors a type has, and nothing in this list reads it for what a set of choices covers.
Whether a pattern is irrefutable is decided by the constructor table alone, at name resolution,
without type inference. No `Partial` is inferred: a function that is meant to be partial fails
explicitly inside a `case`.

**A `Number` is matched by no literal.** Two `Number` literals are one where their bits are (D37):
every NaN is one literal, and `+0.0` and `-0.0` are two. That identity is not numeric equality, so
a pattern would choose one of the two without saying which; a guard writes the comparison it means.

A function defined piecewise, in the manner of mathematical notation, is a library macro rather
than a syntax of the language:

```stella
abs' n = cases%{
  n          where n >= 0
  negate n   otherwise
}
```

#### 2. Or-patterns

Several patterns can be listed with `|` (OCaml-style), and the alternative is taken when any of them
matches.

```stella
data Role = SuperUser | Admin | Guest

level :: Role -> Int
level role =
  case role of
    SuperUser | Admin -> 1
    Guest -> 0

digit :: Int -> Boolean
digit = case _ of
  0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 -> true
  _ -> false
```

Rules:

1. **An or-pattern binds no variables.** Each choice is built from constructors, literals, tags,
   and `_` only. Binding or-patterns are left for later: admitting them only accepts more programs.
2. **At the top of an alternative, `|` binds more loosely than `,`**: `A, B | C, D` is `(A, B)` or
   `(C, D)`. An or inside one column is parenthesized, `A, (B | C)`; so is one inside a
   tuple where `,` and `|` would mix, and one inside a constructor's arguments, `Just (A | B)`.
3. An alternative split over several lines continues its pattern with a leading `| …`, by the
   layout rule. A `case` alternative never starts with `|`, which keeps it apart from a handler
   clause.
4. It desugars either by duplicating the right-hand side or by a `jump` to a join point without
   parameters. Core gains no construct.

When binding or-patterns are admitted, three things are to be settled: every choice binds the same
variables at the same types; a guard block that fails does not retry the other choices, the
leftmost matching choice fixing the bindings; and a warning where a guard uses a variable bound at
different positions by different choices.

#### 3. Guard blocks

Instead of using the vertical bar `|` like PureScript, a guard block is opened by `where` after an
alternative's pattern. The block holds bindings and guards together.

```stella
fizzbuzz :: Int -> String
fizzbuzz = case _ of
  n where
      mul3 = n `rem` 3 == 0       -- bind name
      mul5 = n `rem` 5 == 0
      mul3 && mul5 -> "FizzBuzz"  -- guarded branches
      mul3 -> "Fizz"
      mul5 -> "Buzz"
  n -> format%"{n}"
```

Rules:

1. Each line of the block is a binding (`x = e`) or a guard (`e -> body`). They are evaluated from
   the top; a binding below the guard that succeeds is not evaluated.
2. When every guard fails, matching falls through to the next alternative. In Core this is a
   `Guard` and a `jump` to a join point. The effects of the bindings already evaluated remain.
3. `where` is told apart by position: a guard block's `where` stands right after an alternative's
   pattern, before any `->`, and a declaration's `where` always follows the right-hand side of `=`.
   Function definitions having neither patterns nor guards, the two never meet.

#### 4. `otherwise` is a keyword

`otherwise` is a keyword with a meaning at a guard's position only. **Exhaustiveness treats a guard
that is `otherwise` or the literal `true` as always succeeding**, and every other guard as one that
may fail.

```stella
sign :: Int -> Int
sign = case _ of
  n where
      n > 0 -> 1
      n < 0 -> -1
      otherwise -> 0        -- the block is exhaustive
```

It is not a library definition such as `otherwise = true` that the checker then recognizes by name,
as PureScript's exhaustiveness checking recognizes `Data.Boolean.otherwise`. A feature belonging to
the language core is placed in the core: a keyword in the semantics rather than a library
identifier treated specially. The expansion of `cases%{…}` writes `otherwise` as it stands.

#### 5. No pattern guards, and `<-` is reserved

A pattern guard — `p <- e` inside a guard block, matching the value of `e` and falling through when it
does not match — is not included for now. What it buys arises now and then; its cost is moderate: a
third kind of line in a guard block, the treatment of a line that fails, an exception to the rule
that binding positions are irrefutable, and a desugaring to join points.

```stella
fizzbuzz :: Int -> String
fizzbuzz n = case n of
  _ where
      0 <- n -> "Zero"      -- not admitted
      otherwise -> format%"{n}"
```

**`<-` is a reserved symbol and not a user operator**, as in PureScript. Were it admitted as an
operator, with a warning, then `Just h <- lookup … -> …` in a guard block would be accepted today as
a Boolean guard, and adding pattern guards later would change its meaning without an error. Inside a
macro's token tree (`do%{ x <- … }`), the reserved symbol may be used freely.

If pattern guards are added, a pattern guard line that fails makes its whole alternative fall
through to the next one.
