# Attributes, Modifiers, and Directives

Three kinds of thing stand with a declaration or inside a construct and say something about it, and they differ in who gives them meaning.

| | Attribute | Modifier | Directive |
| --- | --- | --- | --- |
| What it is | metadata classifying a declaration, which something may look for | a word of the language qualifying the construct it stands in | an instruction to a fixed stage of the compiler |
| Vocabulary | open: declared by libraries | closed: fixed by the language | closed: fixed by the compiler |
| Who reads it | whatever looks for it: a synthesizer, a macro, a tool, and the compiler for the attributes of `Prim` and `Base` | name resolution and elaboration | the stage each directive names |
| Written | `@[name args]` | a word: `implicit`, `reifiable` | `#name`, `#name(args)` |

**What tells them apart is who gives the meaning, not the spelling or a prefix of the name.** Each is held apart from the others from the concrete syntax tree on, so no consumer can read one as another.

## Attributes

**An attribute is declared, and has no definition.** It says nothing and does nothing of its own: it is there to be found. A synthesizer finds it through `declsWithAttr`, a macro reads it off the declaration it expands over, a tool such as a test runner reads it off an interface, and the compiler acts on the few that `Prim` and `Base` declare for it, as it does on the types `Prim` declares. **Attaching one starts nothing**: no macro runs and no synthesizer is invoked because a declaration carries it.

### Declaring an attribute

```stella
attribute instance
attribute priority Int
attribute pair Int String
attribute json (name :: String) (omitEmpty :: Boolean = false)
```

- **Positional parameters are types, keyword parameters `(label :: τ)`**, and the positional ones come first. A keyword parameter is declared once.
- **A keyword parameter may have a default**, `(label :: τ = c)`, a constant. A positional one may not, which would leave it unclear which position was left out.
- **A parameter's type is closed.** An attribute declaration binds no type variable, and none stands free in a parameter's type, so an attribute's use needs no instantiation. A type quantifying inside itself, a closed higher-rank one, is admitted.
- **Positional and keyword parameters, and defaults, belong to attributes alone.** A function takes its arguments one way, curried and positional.

### Attaching an attribute

```stella
@[instance]
@[priority 10]
@[json name="user_name"]
@[json omitEmpty=true name="user_name"]
eqInt = …
```

- **Positional arguments are exactly as many as the declaration has.**
- **Keyword arguments stand in any order.** One the declaration does not have, one given twice, and one without a default that is left out are errors.
- **What is recorded is normalized**: the attribute, its positional arguments, and every keyword argument, a default standing for one left out. A reader cannot tell a default from a value written.
- **An argument is a constant**: a literal, a global value, a constructor applied to constants, or a record of constants. A computation and an operation are no constant. A name in one is a reference, resolved through the module's scope and held qualified by the module defining it, which the imports reach directly or through a re-export; the reference is what later stages carry, and the module's dependencies are its imports, unchanged by it. A sequence is written as a value of a data type that holds one, such as a list, and a macro the module imports may build it, its expansion running before the attribute is read ([Name Resolution](06-Name-Resolution.md)). There is no array constant: `Array` is an intrinsic of the ABI, which no surface form builds ([Prim and Base](../06-Modules/02-Prim-and-Base.md)).

**An attribute is attached to a declaration**, and to no other place in this version: not to an expression, and not to a position inside a declaration such as a record type's field, a constructor, or an operation ([Open Questions](../99-Open-Questions/01-Open-Questions.md)). A type is not where one could be held: an attribute standing in a type would have to be decided by type equality, unification, and row normalization, and none of those has anything to do with it.

| Declaration | Attributes |
| --- | --- |
| a value, a computation, a handler, a foreign | attached |
| a `data`, a `newtype`, a type synonym, a foreign type, an effect | attached |
| a fixity, an attribute declaration | an error |
| a macro called at a declaration's position | not attached: the prefix before the call is the macro's input, uninterpreted, and which declarations of its expansion carry what is the macro's to decide |

**An attribute a library declares may stand on one declaration any number of times**, each recorded in the order written, and what a repetition means is its reader's. The attributes the compiler acts on stand at most once (below).

### From source to output

| Stage | Holds |
| --- | --- |
| concrete syntax tree | the prefix items as written |
| declarations grouped | on each declaration, its prefix; on a macro call at a declaration's position, the prefix before it, which is the macro's input and is not read as attributes |
| Surface AST | on each declaration, its attributes resolved and their arguments normalized. Expansion is done, so no macro call remains: a declaration an expansion produced carries what the macro gave it |
| Core | on each declaration, its attributes; and the attribute declarations |
| Mid IR, `.dmo` | nothing |
| interface | the attribute declarations a module exports, and the attributes of the entries it publishes, which the catalog is built from |

### Names and identity

**An attribute has a namespace of its own**, as a macro has: its name is written at the head of `@[ … ]` and nowhere else, so a value and an attribute of one spelling stand together. It is imported and exported as any name is, an item `attribute a` naming one in a list ([Name Resolution](06-Name-Resolution.md)), and qualified through an alias: `@[TC.instance]`.

**An attribute's identity is its qualified name**, which is what `declsWithAttr` looks for. Two libraries declaring an `instance` declare two attributes.

### In Core

**An attribute declaration is a declaration of Core**, carrying its name, its positional parameter types, and its keyword parameters with their defaults. It is not a value: no term refers to it, and nothing of it reaches a `.dmo`. An interface carries it, as it carries the attributes a module's declarations bear.

**Every declaration carries the attributes attached to it**, each the attribute's qualified name and its normalized arguments. **Checking an attribute is checking its arguments**: each has the type its parameter declares, which the Core type checker confirms. Nothing about the declaration the attribute is attached to depends on it, and nothing is evaluated.

### The attributes the compiler acts on

| Attribute | Declared in | Stands on | What the compiler does |
| --- | --- | --- | --- |
| `attribute macro` | `Prim` | a value declaration | the declaration is a macro, and its name goes to the macro namespace ([Name Resolution](06-Name-Resolution.md)) |
| `attribute entrypoint` | `Prim` | a value or a computation declaration | the declaration is the program's entry point: a value of type `IO Unit` as it is, and a computation `Unit / ρ` whose `ρ` lowers to `{\| LiftIO \|}` by implicit handlers, run by the standard runner ([Implicit Effect Runner](../../proposals/01-Implicit-Effect-Runner.md)) |
| `attribute elaborationOnly` | `Prim` | a `data` or `newtype` declaration | the constructor takes the internal identity the compiler lists, in the modules it lists ([Modules](../06-Modules/01-Modules.md)) |
| `attribute synthesizedBy Synthesizer` | `Stella.Elab` | a `data`, a `newtype`, a type synonym, or a foreign type declaration | a constraint `C τ̄ =>` on the type `C` desugars to a synthesized argument `{{ _ :: C τ̄ by f }}`, `f` the synthesizer named. The attribute is looked for on the head of the constraint as written, before a synonym there is expanded |

**These are attributes like any other** in how they are declared, attached, imported, and recorded; what sets them apart is that the compiler is one of their readers. Each stands at most once on a declaration of the kind the table gives, which the compiler checks, being their reader: a use on another declaration, and a second use, are rejected, a use whose arguments do not match counting as one. **Two of them change the declaration's place in the module's scope**, `macro` its namespace and `elaborationOnly` its constructor's identity, and each does so only through its first use, written with no argument on a declaration it is for, which is the use the rest of the declaration's resolution keeps. `synthesizedBy` is declared beside the synthesizer types it names, which `Prim`, beneath every other layer, cannot mention; an expansion writing it, as a class macro does, names it where the macro is defined ([Prim and Base](../06-Modules/02-Prim-and-Base.md)). `entrypoint` takes no parameter in this version: a runner other than the standard one, chosen per entry point, is the proposal's later step.

## Modifiers

**A modifier is a word of the language that qualifies the construct it stands in.** Which constructs it may qualify and what it changes are the language's, and fixed. What one says is held as a field of the construct it qualifies, typed as that construct needs, and not as an annotation every node could carry: so no stage depends on a node's annotations to decide what the node is.

| Modifier | Qualifies | Means |
| --- | --- | --- |
| `implicit` | a handler declaration | the elaborator may supply the handler where the author wrote none ([Effect Handlers](02-Effect-Handlers.md)) |
| `reifiable` | the marker `full` of a handler clause | the clause takes its continuation as a parameter, a value it may keep ([Effect Handlers](02-Effect-Handlers.md)) |

**`full` and `fast` are not modifiers.** Each chooses the form a clause takes — what becomes of the continuation, and what its body is — and one of them, written or implied, every clause has. A modifier adds a property to a construct whose form is already chosen.

## Directives

**A directive tells a fixed stage of the compiler how to treat what it stands with.** The vocabulary is the compiler's, and a directive the compiler does not know is an error. Whether one may be ignored, and what it changes, is the contract of that directive and not a property of directives at large: one may only inform an optimization, and another, choosing what source is compiled, changes the program.

```stella
#observ(none) foreign sqrt :: Number -> Number
```

**Its arguments are the parenthesis after it**, written with no space, positional or keyed by `label=value` ([Syntax](05-Syntax.md)).

**Every directive's contract says**

1. the stage that reads it
2. what it may stand with, or the range it acts over
3. the arguments it takes
4. what is rejected, and when
5. what holds where it is absent
6. what of it is kept past the stage that reads it, in an interface or a later representation
7. whether it changes what a build is keyed by

### The directives of this version

**This version has one directive.**

| | `#observ(none)` |
| --- | --- |
| Read by | declaration checking, which records it; an optimizer, which acts on it |
| Stands with | a `foreign` declaration, once |
| Arguments | `none`, the one there is |
| Rejected | with another argument, by the check of the tree; before anything but a `foreign` declaration, or twice, where declarations are grouped |
| Absent | the entry may observe |
| Kept | in `Σ`, and in the interface as the foreign's observation, which its effect summary is derived from ([Interface](../05-Backend/03-Interface.md)); a `.dmo` carries none |
| Build key | through the interface, as any change to a declaration is |

What it asserts is what [Modules](../06-Modules/01-Modules.md) gives it to assert, and a breach of it is the implementation's.

**`#inline` and `#unbox` are read and rejected.** The grammar has room for them, `#inline(arity=2)` before a declaration and `(#unbox Int)` in a type, and both are refused as unsupported until their contracts are written with the optimizer that reads them: what an arity means and what is inlined across a module, and whether unboxing is a request or a requirement on a representation other modules and backends rely on. Admitting one as a hint now would settle the second question by default.

**Conditional compilation is a directive too**, choosing what source is compiled, and its contract is not yet fixed ([Open Questions](../99-Open-Questions/01-Open-Questions.md)).
