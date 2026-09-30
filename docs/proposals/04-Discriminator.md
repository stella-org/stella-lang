# Discriminator

Status: Proposed

## What is this?

Given the following datatype definition:

```stella
data Maybe a = Just a | Nothing
```

the following functions -- **discriminators** -- are introduced in the same module as the datatype definition:

```Stella
Just? :: forall a. Maybe a -> Boolean
Nothing? :: forall a. Maybe a -> Boolean
```

Semantically, these are treated the same as a regular functions.

## Discussions

- Is it permissible to use camelCase identifiers for values other than constructors?
