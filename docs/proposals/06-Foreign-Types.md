# Foreign Types

Status: Proposed

## What is This?

### Background

A library binding a host API has to name the host's values in its types: a Node `Buffer`, a
file descriptor, a stream; a web `Window`, `Document`, `Element`, or `Promise`. None of these has
a Stella representation, and none should: they are host objects that Stella code holds, passes,
and hands back, and never takes apart.

Today there is no way to declare such a type. A type constructor with no data constructors — an
intrinsic — has three sources, and the specification states that all three are beyond a user's
reach ([Prim and Base](../technical-references/06-Modules/02-Prim-and-Base.md)):

| Source | Examples | Settled by |
| --- | --- | --- |
| Core intrinsic | `Function`, `Record`, `Variant`, the literal types, `IO` | this specification |
| manifest intrinsic | `Base.Array.Array`; target ones such as `Js.String.JSString` | the versioned ABI specification |
| elaboration intrinsic | `Stella.Elab.Handle` | the compiler |

A binding can therefore only use an opaque type the ABI manifest already supplies. The ABI is a
specification a compiler and its backends implement together, versioned as a whole; growing it by
one entry for every host type a library may want to name does not scale, and it puts the design of
every host binding on the ABI's release cycle.

PureScript's `foreign import data Json :: Type` fills this role, and a large part of its ecosystem
rests on it.

### Proposal

A module may declare a **foreign type**: a type constructor of a given kind, with no data
constructors, whose values are host objects.

```stella
module Web.DOM (Window, Document, window, document) where

foreign type Window :: Type
foreign type Document :: Type
foreign type Promise :: Type -> Type

foreign window :: IO Window
foreign document :: Window -> Document
```

A foreign type is written as a foreign declaration is: the modifier `foreign` before a signature,
here the kind signature of a type. A directive, where one applies, precedes the modifier
(`#observ(none) foreign f :: τ`).

#### Rules

1. **A foreign type is declared with its kind, which is mandatory.** The kind is written as a
   standalone signature of the name, as every declared name's type or kind is: a declared name is
   not a binder, and carries no inline annotation. Its parameters, if any, are phantom as far as
   Stella can tell: nothing Stella does relates a `Promise Int` to the `Int` in it.

2. **In Core, a foreign type is an intrinsic type constructor of the canonical-value class
   `opaque`, declared by its module.** It enters `Σ` under the module's own qualified name, as a
   data type does, and reaches importers through the interface as any declaration does. It has no
   data constructor, so a `switchCtor` over it is ill-formed, exactly as over a manifest intrinsic;
   its values are made only by foreign functions and are otherwise only held and passed on.

3. **It crosses the foreign boundary as `opaque`.** A foreign declaration may range over it — D44's
   list of the types that can cross the boundary counts "an `intrinsic opaque`", and a foreign
   type is one — and the foreign manifest marks the position `opaque`, which passes the host value
   through unconverted. No entry in the ABI manifest, and no marshalling, is needed for the type
   itself.

4. **It is a fourth source of intrinsics, and the reserved namespaces stay closed.** The statement
   that intrinsics are beyond a user's reach exists to keep a user from forging `Prim.Int` or a
   `Base` entry; a foreign type declared under a module's own name forges nothing. A foreign type
   may not be declared in a module under a reserved prefix — `Prim`, `Base`, a target namespace such
   as `Js` or `Wasm`, or `Stella` — which remain the ABI's and the compiler's.

   ```text
   intrinsic
   ├─ Core intrinsic
   ├─ manifest intrinsic      (portable Base.*, target Js.* / Wasm.*)
   ├─ elaboration intrinsic   (Stella.Elab)
   └─ declared foreign type   (any other module)
   ```

5. **Which target it belongs to follows its functions.** A foreign type needs no implementation of
   its own; a module declaring one is usable on the targets its foreign functions are implemented
   for, which the foreign manifest already records. A type declared in a module no target implements
   is harmless and useless.

#### Consequences and Open Points

- **The boundary cannot tell two foreign types apart.** A result marked `opaque` is not validated —
  there is nothing an opaque value is not ([Foreign Manifest](../technical-references/05-Backend/04-Foreign-Manifest.md)) —
  so an implementation declared to return a `Window` that returns a `Document` is not caught where it
  returns. Keeping to the declared type is the implementation's obligation under the conformance of
  the global environment, as it is for a manifest intrinsic today. Whether a backend may, or must,
  brand host values to check this is left open.
- **Equality and other structure are not given.** A foreign type has no `Eq` or `Show` of its own; a
  library supplies them through foreign functions and, once classes exist, instances.
- **Variance and roles of the parameters** (whether `Promise` may be coerced through a newtype of its
  argument) are not addressed, and do not arise until something coerces.
- **What the interpreter holds** for such a value is what it holds for any opaque value today; nothing
  in the `.dmo` or in Steam changes.
- The specification text to revise if accepted: the taxonomy of intrinsics and the phrase "beyond a
  user's reach" in [Prim and Base](../technical-references/06-Modules/02-Prim-and-Base.md), the
  declaration forms in [Modules](../technical-references/06-Modules/01-Modules.md), and the
  corresponding entry in [Open Questions](../technical-references/99-Open-Questions/01-Open-Questions.md).
