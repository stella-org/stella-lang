# Correspondence with PureScript's CoreFn

Stella's Typed Core takes PureScript's CoreFn as its starting point. CoreFn's position — a desugared, fully qualified, unoptimized functional IR — and its skeleton of `Abs`, `App`, `Var`, `Let`, `Case`, and `Literal` carry over directly.

**CoreFn is not typed.** The annotation emitted by `purs compile --codegen corefn` is `{ span, meta }` and carries no type. The compiler's internal `Language.PureScript.CoreFn` does put a type in its annotation, but that merely conveys an already-checked type; it is not enough information to support an independent type checker over CoreFn terms. There is no type abstraction and no type application, and the instantiation of a `forall` has disappeared entirely.

What CoreFn therefore lacks:

| Absent from CoreFn | Why Stella needs it |
| --- | --- |
| Type abstraction and application | To make an independent Core type checker possible |
| Row operations as terms | To treat rows as first class rather than through type classes |
| Effect rows and handlers | To avoid redesigning function types later |
| The decision structure of pattern matching | `Case` with `Binder` keeps the source's shape; branch order cannot be read from the term |
| Row constraints | `Prim.Row.Union` and its kin are type classes, outside CoreFn |

Conversely, some things CoreFn has do not appear in Stella's Core.

| Present in CoreFn | How Stella handles it |
| --- | --- |
| `Meta` (`IsConstructor`, `IsNewtype`, `IsTypeClassConstructor`, `IsForeign`, `IsWhere`, `IsSyntheticApp`) | Codegen hints, moved into the declaration table and attributes. `IsTypeClassConstructor` has no counterpart |
| The `Constructor` node | A declaration table exists, so a constructor is an ordinary global name with a declared type |
| `copyFields` of `ObjectUpdate` | Recoverable from the row type, so unnecessary |
| The string label of `Accessor` | Becomes a typed `select` |

## Terms

| CoreFn | Stella Typed Core | Difference |
| --- | --- | --- |
| `Var Ann (Qualified Ident)` | `x` / `M.x` | Carries a type |
| `Abs Ann Ident Expr` | `λ (x : τ). e` | The argument is annotated |
| `App Ann Expr Expr` | `e1 e2` | The same, except that the arrow's effect row must equal the ambient row |
| (absent) | `Λ (a : κ). v` / `e [τ]` | New. Makes independent type checking possible |
| (absent) | `Λ (_ : C). v` / `e [•]` | New. Row constraints, with no run-time content |
| (absent) | `T [[κ̄]]` / `M.x [[κ̄]]` | New. Explicit instantiation of kind schemes |
| `Literal Ann (Literal Expr)` | `c` | No `LitArray` or `LitObject` |
| `Constructor Ann T Ctor [Ident]` | (no term node) | Moved into the declaration table; `M.Ctor` is an ordinary global variable |
| `Accessor Ann String Expr` | `select k e` | Typed, and keyed by a `RowKey` rather than a string |
| `ObjectUpdate Ann Expr (Maybe [String]) [(String, Expr)]` | `update k e1 e2` | No `copyFields` |
| (absent) | `{}`, `extend`, `restrict`, `merge` | New. Row-polymorphic record operations |
| (absent) | `inject`, `weaken`, `absurd` | New. Row-polymorphic variant operations |
| `Case Ann [Expr] [CaseAlternative]` | `case (ē) of dt` | A decision tree rather than a list of alternatives |
| `CaseAlternative { binders, result }` | `switch*`, `bind`, `guard` in the tree | Branch order is readable from the term |
| `Binder` (five constructors) | occurrences `o` and `switch*` | `NullBinder` is "do not bind"; `NamedBinder` is an additional `bind` |
| `Guard { guard, expression }` | `guard e dt1 dt2` | Fall-through is explicit via `jump` |
| `Let Ann [Bind] Expr` | `let` / `letrec` | `Rec` gains an initialization-safety requirement ([Initialization Safety](10-Initialization.md)) |
| `Bind = NonRec \| Rec` | `nonrec` / `rec` | `Rec` gains an initialization-safety requirement ([Initialization Safety](10-Initialization.md)) |
| (absent) | `letjoin` / `jump` | New. Body sharing in decision trees, and the bridge to Mid IR |
| (absent) | `perform` / `handle` / `openEff` | New |
| (absent) | `fail`, derived | New. Non-exhaustiveness surfaced as a `Partial` effect |

## Types and kinds

| PureScript `Type a` | Stella | Difference |
| --- | --- | --- |
| `TypeVar`, `TypeConstructor`, `TypeApp` | `a`, `T [[κ̄]]`, `τ1 τ2` | Kind schemes are instantiated explicitly |
| `ForAll a vis name (Maybe kind) ty scope` | `forall (a : κ). τ` | The kind is mandatory and must be quantifiable. `SkolemScope` is an elaboration concern and absent from Core |
| `Skolem` | (absent) | A constructor for inference; it never appears in Core |
| `TUnknown` | `?α`, in Core⁺ only | Absent from Core |
| `TypeWildcard` | `hole`, in Core⁺ only | The same |
| `ConstrainedType a Constraint ty` | `C => τ` | The content of `Constraint` differs: in Stella it is row constraints only, never type classes |
| `REmpty`, `RCons Label Type Type` | `()`, `( ent \| ρ )` | `RCons` permits duplicates; Stella does not. Stella derives the key for effect rows |
| (absent) | `ρ1 ⊎ ρ2` | New. Replaces the `Prim.Row.Union` class |
| `KindApp` | `T [[κ̄]]` / `M.x [[κ̄]]` | Similar in role, but kind-specific, since kinds and types are separate classes |
| `KindedType` | (absent) | Unnecessary once kinds and types are separate |
| `TypeLevelString`, `TypeLevelInt` | (absent) | Labels are not types |
| `TypeOp`, `BinaryNoParensType`, `ParensInType` | (absent) | Concerns of surface syntax |

## Modules

| CoreFn `Module` | Stella | Difference |
| --- | --- | --- |
| `name`, `path`, `builtWith` | The same | |
| `imports` | The same | No influence on type checking |
| `exports`, `reExports` | The same | |
| `foreignNames` | `foreign f : σ` | The type is mandatory; every arrow is pure and external effects return `IO` (D23) |
| `decls :: Array Bind` | `decl` (data, effect, foreign, binding group, with attributes) | Data and effect declarations appear in the module |
| `Meta.IsConstructor` | The tag and arity of a data declaration | |
| `Meta.IsNewtype` | The `newtype` flag | The checker verifies the shape: one constructor, one field |
| `Meta.IsTypeClassConstructor` | (does not exist) | Core has no type classes |
| `Meta.IsForeign` | A `foreign` declaration | |
| `Meta.IsWhere`, `IsSyntheticApp` | (do not exist) | Provenance from the surface; spans suffice |
| (absent) | An attribute table | New. Queried by elaborators |
