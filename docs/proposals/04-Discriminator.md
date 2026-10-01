# Discriminator

Status: Accepted

## What is this?

### Background

Testing which constructor a value was built with is common enough — as a predicate passed to
`filter`, or in a condition — that writing out a `case` each time is noise:

```stella
filter (\x -> case x of
  Just _ -> true
  _ -> false) xs
```

### Proposal

For every constructor `C`, the name **`C?`** is its **discriminator**: a predicate that holds of a
value built with `C`.

```stella
data Maybe a = Just a | Nothing

filter Just? xs
```

Here `Just? :: forall a. Maybe a -> Boolean` and `Nothing? :: forall a. Maybe a -> Boolean`.

#### Rules

1. **A discriminator is syntax derived from a constructor.** It is neither a construct of Core nor
   a declaration generated beside the data type. Elaboration desugars `C?` to

   ```text
   \x -> case x of C _ … _ -> true; _ -> false
   ```

   and passing it as a function (`filter Just? xs`) passes that lambda.

2. **It is visible exactly where its constructor is.** `import M (Maybe(..))` brings `Just?` and
   `Nothing?` together with `Just` and `Nothing`, and `M.Just?` is available wherever `M.Just` is.
   No export or import rule of its own is needed.

3. **It is lexical.** `?` may appear in an identifier only as the last character of one beginning
   with an uppercase letter. At a value position, a name beginning with an uppercase letter is
   therefore a constructor or, ending in `?`, a discriminator. `empty?`, `isn't_it?`, and `is?valid`
   are not identifiers, and a user cannot declare a name of the form `C?`.

4. **It is used at value positions only**, and never in a pattern.

5. A discriminator of a type with a single constructor, always `true`, is admitted; a lint may
   point it out.

#### Consequences

- Nothing is generated per data type, so neither the `.dmo` nor the interface grows. The
  desugaring needs only the constructor table — the data type a constructor belongs to and its
  siblings — which an imported interface already carries.
- Making discriminators a Core construct is not proposed. A `case` already expresses them, so it
  would add no expressiveness, only rules at the trust boundary and work for every backend; and
  unlike `otherwise` ([Pattern Matching](./03-Pattern-Matching-Syntax.md)), it brings no meaning of
  its own to exhaustiveness or to evaluation that would place it in the core.
- `?` otherwise stays available: `?name` and `?_` are typed holes, and `?` elsewhere is an operator
  character, a lone `?` included (`x ? y`).
