# User-defined Namespaces

Status: Proposed for a future version

## What is This?

### Background

Macros can introduce declaration families that do not naturally belong to Stella's built-in
namespaces. A type class is one example: Stella need not have a built-in `Class` namespace merely
because a macro happens to generate dictionary types, methods, and instances. Nevertheless, a
macro-defined declaration family may eventually need its own identity and its own import and export
selectors.

Giving every such family a new compiler-defined namespace would make the compiler the bottleneck for
extending the surface language. Conversely, putting all macro-defined declarations into the value or
type namespace can create avoidable collisions and cannot express visibility rules peculiar to the
declaration family.

### Proposal Sketch

In addition to its built-in namespaces, Stella may allow a package to define a **named namespace**.
The built-in set is provisionally written as `Value`, `Type`, `Operator`, `Module`, `Local` and
`Macro`.

A surface-level global name then has the identity

```text
NamespaceId × ModuleName × Name
```

`NamespaceId` is itself globally owned rather than an unqualified word. For example, a type-class
library might own `Typeclass.Class`; another package defining a namespace called `Class` would have a
different identity.

The namespace is written explicitly only in a module header, where imports and exports must be able
to select entries of a user-defined namespace. The exact syntax is left open; one possible spelling
is:

```stella
import M (Typeclass.Class C)
```

Inside a module body, an author does not prefix every occurrence with its namespace. The syntactic
position that admits the occurrence determines which namespace is consulted. Built-in grammar
positions keep their fixed namespaces, while macro-defined syntax may designate a user-defined
namespace for the names occurring in positions it introduces.

Resolution must **not** search every namespace and accept whichever match happens to be unique. Such
a rule would let importing an unrelated namespace make an existing program ambiguous. Every
occurrence therefore has one predetermined namespace before lookup; if its syntax does not determine
one, resolution rejects it.

### Scope

User-defined namespaces belong to the surface language and its interfaces. A macro may create,
resolve, import, or export their entries, but expansion or elaboration must consume those entries
before Typed Core. They do not add a new class of Core global, `.dmo` identity, or backend linkage.
The ordinary declarations a macro produces still lower to the existing Core forms.

This also means that a user-defined namespace is not a replacement for ordinary generated names. A
type-class macro may still generate a dictionary type in `Type`, methods in `Value`, and instances as
ordinary attributed values; a `Class` namespace is useful only if the macro's surface contract needs
a separately selectable declaration identity.

### Requirements Before Adoption

- The interface format must record namespace ownership, entries, and their visibility.
- Module headers need unambiguous import, export, qualification, re-export, and local-open rules for
  user-defined namespaces.
- The macro API must say which expansion defines an entry and which syntax positions resolve one.
- Hygiene, duplicate declarations, ambiguity, and shadowing must be specified per namespace.
- Namespace definitions must be available before the macro expansion that uses them, without making
  resolution depend on declaration order.
- Package ownership must prevent two packages from defining the same `NamespaceId`; this depends on a
  package model that the compiler does not yet have.

For these reasons this is a future macro-interface proposal, not part of the first surface-language
implementation. The immediately useful rule is only that macros have their own built-in namespace;
general user-defined namespaces can be added if real macro libraries demonstrate the need.
