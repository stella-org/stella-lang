# Surface Syntax for Pattern Matching, or `case` expressions

Status: Proposed

## What is this?

### Background

The syntax basically follows PureScript's case expressions, but with the following two custom additions specific to Stella.

### Proposal

#### 1. Or-patterns

Multiple patterns can be listed using the | operator (OCaml-style).

```stella
data Role = SuperUser | Admin | Guest

level :: Role -> Int
level role =
  case role of
    SuperUser | Admin -> 1
    Guest -> 0
```

Constraint: All alternatives combined in an or-pattern must have the same type and bind the same set of variables (with identical types).

#### 2. Case Guards

Instead of using the vertical bar `|` like PureScript, we propose to repurpose the `where` clause.
Furthermore, variable bindings are allowed within the `where` block.

```stella
fizzbuzz :: Int -> String
fizzbuzz = case _ of
  n where
      mul3 = n % 3 == 0           -- bind name
      mul5 = n % 5 == 0 
      mul3 && mul5 -> "FizzBuzz"  -- guarded branches
      mul3 -> "Fizz"
      mul5 -> "Buzz"
  n -> format!"{n}"
```

## Discussion

- Should otherwise be a built-in language keyword, or should it be defined in the standard library like this?

  ```stella
  otherwise :: Boolean
  otherwise = true
  ```

- Should we allow the following syntax?

  ```stella
  fizzbuzz :: Int -> String
  fizzbuzz n = case n of
    _ where
        0 <- n -> "Zero"      -- Guarded pattern
        ...
        otherwise -> format!"{n}"
  ```
