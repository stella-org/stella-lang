<p align="center">
<img src="https://stella-lang.org/stella-logo.svg" width="128" height="128" alt="stella-logo" />
</p>

# The Stella Programming Language

An effect-oriented functional programming language with first-class macro

[![CI](https://github.com/katsujukou/stella-lang/actions/workflows/ci.yaml/badge.svg)](https://github.com/katsujukou/stella-lang/actions/workflows/ci.yaml)

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
The dedicated syntax for them is implemented as macros **at the library level**!
This particular idea was inspired by F*.

## A Little Taste of Stella

```purs
module Main where

import Prelude

import Effect.Console (Console, log)

-- Define new effect with two operations
-- A weird `->*` arrow indicates that `say` and `listen` are
-- not ordinal functions but effectful operations.
effect Talker where
  say :: String ->* Unit
  listen :: Unit ->* String

-- A program carrying  `Talker` effect.
-- In Stella, performing effect is in direct-style;
-- there is no monadic do-notation or `<-` arrow.
program :: Unit / {| Talker |}
program = 
  say "Hi";
  say "What's your name?";
  let name = listen () in
  say $ fmt%"Nice to meet you, {name}"

-- handling `Talker`-carrying program with handler performing
-- another effect `Console`, which can be implicitly lowered down
-- and reified as `IO`, so we can mark this declaration as `@[entrypoint]`. 
@[entrypoint]
main :: Unit / {| Console |}
main = handle program
  with
    Talker 
      | say msg -> Console.log msg; resume ()
      | listen _ -> resume "Alice"
```

## Roadmap

- ✅️ `TypedCore`, the central representation with explicit types and kinds
- ✅️ Bytecode compiler
- ✅️ STEAM, the bytecode interpreter with multi-shot continuation over explicit stack
- ✅️ Surface Language Concrete Syntax and parser
- ✅️ Surface Language AST, Macro Expander, and `Syntax` API
- ✅️ Elaborator API
- ✅️ Demonstration of macro within minimal sublanguage: list syntax `ls%[1,2,3]`
- ✅️ Hindley-Milner Type Inference
- 🎯 More macro demo: array syntax `ar%[1,2,3]` and format string with `fmt%"..."` *WIP*
- ☑️ Macro at declaration position: `m%{ ... }`
- ☑️ Implicit handlers insertion
- ☑️ E2E testing on whole set of language features
- ☑️ Typeclasses over macro
- ☑️ MiddleEnd: IR design and optimization
- ☑️ The first two backends: JavaScript and WebAssembly ... Prototype JS backend is done
- ☑️ Suspension and concurrent primitives, `Async` effect
- ☑️ The standard library `Prelude`
- ☑️ portable libraries on top of `Prelude`
- ☑️ Build system: [the Lazuli package manager](https://github.com/stella-org/lazuli)
- ☑️ Ecosystem: LSP, IDE support, Formatter and Coding Agent Plugins
- ☑️ New comprehensive language reference ... *WIP*
- ☑️ Official textbook: *Functional and Effect-Oriented Programming in Stella*

Possible future enhancement, but not in the current roadmap (CONTRIBUTIONS ARE HIGHLY WELCOME!!):

- First-class Parser API
- Termination analysis and `Div` effect
- Context refinement with Discriminators
- Scoped effect
- General higher-order effects
- Native backend
