<p align="center">
<img src="https://stella-lang.org/stella-logo.svg" width="128" height="128" alt="stella-logo" />
</p>

# The Stella Programming Language

An effect-oriented functional programming language with first-class macro

[![CI](https://github.com/katsujukou/stella-lang/actions/workflows/ci.yaml/badge.svg)](https://github.com/katsujukou/stella-lang/actions/workflows/ci.yaml)

> Stella was originally called *Dawn*. However, since several languages
> already use that name and the corresponding domain is already taken,
> I decided to rename it to *Stella*.

## Motivation

Stella is a functional programming language inspired by PureScript.

As you all know, PureScript is an excellent language.
Thanks to its brilliant design, it keeps the language core remarkably minimal
while remaining incredibly expressive. However, after years of writing PureScript,
I've come across a few areas where I couldn't help but think,
*"Man, I wish it did this differently..."*

- Row operations are handled through type class resolution.
- Metaprogramming also relies on resolving type classes (specifically, functional dependencies).
  This can get so complex that people often call it *black magic*.
- The FFI is *too* powerful. Even though the language core is backend-agnostic, this extreme flexibility sometimes hurts code portability.

The first two points really boil down to one observation: *doing too much with type classes.*
I suspect this was a deliberate trade-off to keep the compiler small.
In Stella, we believe that if a feature genuinely belongs in the language core,
that's exactly where it should go. By doing this, Stella scratches those stubborn itches that
PureScript leaves behind.

Specifically, what sets Stella apart from PureScript comes down to three main pillars:

- First-class Row system
- direct-style algebraic effect & handlers ... inspired by Koka
- Metaprogramming with first-class macro ... inspired by Lean and F*

The third pillar is a vital and powerful feature. It ensures we don't over-minimize the core, but it also stops the language from becoming bloated.
Interestingly, Stella's compiler doesn't actually have built-in support for Typeclasses!
Instead, they are just dictionary records passed as arguments with method field access.
The dedicated syntax for them is implemented as macros **at the library level** (planned)!
This particular idea was inspired by F*.

## Roadmap

- The kind-and-type checking around the functional core of the language
- MiddleEnd: IR design and optimization
- Frontend: Surface language syntax, parser
- Typeclasses over syntax macro system
- Core package: `Base` and `Prelude`
- The first backend: JavaScript and WebAssembly
- Standard libraries
- Build system: the Lazuli package manager
- Ecosystem: LSP, ide support, formatter and coding agent plugins
