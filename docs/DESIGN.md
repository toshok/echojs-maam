# Design notes

A TypeScript transliteration of David Darais's [`maam`](https://github.com/davdar/maam),
the artifact for **"Galois Transformers and Modular Abstract Interpreters"**
(Darais, Might, Van Horn — [arXiv:1411.3962](https://arxiv.org/abs/1411.3962)).

The goal is a library a **self-hosted TypeScript compiler** can import to run
sound static analyses (k-CFA and friends) over a restricted JS dialect.

## Why dictionary-passing instead of HKT

MAAM is written in Haskell and is *polymorphic over the monad*: one definitional
interpreter, instantiated at different monad-transformer stacks, yields analyses
of different precision. TypeScript has no higher-kinded types, so we cannot write
`forall m. Monad m => …` directly.

Rather than fight for HKT with the fp-ts `URItoKind` defunctionalization trick
(verbose, terrible error messages — a poor fit inside a compiler codebase), we
use **explicit dictionary passing**, which is exactly how a Haskell compiler
desugars type classes:

- A type class becomes an `interface` of operations.
- An instance becomes a value of that interface, passed explicitly.
- The interpreter is written once against a single **opaque** computation type
  `Comp<A>` and an `AnalysisMonad` dictionary; each concrete monad reinterprets
  `Comp` as its own representation. The interpreter stays fully typed; the small
  amount of unsafe casting is confined to each monad implementation.

## The three orthogonal knobs

The paper's key separation of concerns (§4, §8) gives three independent axes.
Fixing all three picks a concrete analysis.

| Knob | Values | Where it lives |
|------|--------|----------------|
| **Value domain** | concrete `CVal` · abstract `AVal` | `Val` domain dictionary |
| **Time / context** | `Cτ` (concrete, unbounded) · `Kτ k` (k-CFA) · `Zτ` (0-CFA) | `Time` dictionary |
| **Sensitivity** | path- · flow- · flow-insensitive | the monad stack |

`concrete eval = CVal × Cτ`; `k-CFA = AVal × Kτ k`. Precision of the *store
relation* (path/flow sensitivity) is orthogonal, chosen purely by the monad.

## Stack order → sensitivity (the central result, §8)

Let `St[s]` be the state transformer and `Pt` the nondeterminism transformer.

- **`St[s] ∘ Pt`** — state *outside* nondeterminism ⟹ `s` is **path-sensitive**.
  A computation is `s → ℘(A × s)`: every branch keeps its own store.
  Implemented by `pathSensitiveMonad`.
- **`Pt ∘ St[s]`** — state *inside* nondeterminism ⟹ `s` is **flow-insensitive**.
  A computation is `s → (℘(A) × s)`: one store threads through and is joined at
  every branch. Implemented by `flowInsensitiveMonad`.
- **`Ft[s]`** — the fused flow transformer `s → m([A ↦ s])` ⟹ **flow-sensitive**
  (one store per control point). The public Haskell realizes this not as a
  distinct transformer but as a *collecting-set widening*: reuse the
  path-sensitive monad, then merge stores per control point in the fixpoint.
  We follow the code: `exploreFlowSensitive` in the driver.

The induced state spaces:

```
path-sensitive     Σ(Exp) := ℘(Exp × Ψ × Store)      -- a relation
flow-sensitive     Σ(Exp) := [(Exp × Ψ) ↦ Store]      -- one store per point
flow-insensitive   Σ(Exp) := ℘(Exp × Ψ) × Store       -- one global store
```

## Execution: monad ⇄ transition system

A monadic action `Exp → m(Exp)` is not directly iterable. Each monad comes with a
Galois connection to a transition system (`mstepγ : (a → m b) → (ς a → ς b)`), and
the analysis is the least fixed point

```
analysis := μX. X ⊔ ς₀ ⊔ γ(step)(X)
```

We realize `γ(step)` + the lfp as the reachable-states drivers in `src/driver.ts`,
one per collecting shape (`exploreConfigs`, `exploreFlowSensitive`,
`exploreGlobal`). Because every layer carries a Galois connection and the
connections **compose**, soundness of the whole analysis follows from soundness
of each layer — "soundness for free" (Theorems 1–2).

## Interpreter interface (what `step` is written against)

Exactly the effects the paper's `stepm` needs:

- `Monad` — `unit`, `bind`
- Nondeterminism (`MonadBot` + `MonadPlus`) — `mzero`, `mplus` (branch on
  `elimBool`/`elimClo`, i.e. both sides of an `if`, every callee of a call site)
- `MonadState` over the store — `get`, `put` (and derived `modify`)
- CFA hooks — `alloc` (address = `(name, time)`) and `tick` (advance context)
- Value domain — `lit`, `clo`, `binop`, `elimBool`, `elimClo` (a Galois
  connection between `℘(base)` and the value lattice)

Store writes **always join** (`joinAt`), which is what makes finitely-many
abstract addresses sound for infinitely-many concrete allocations.

## The example language

A restricted dialect of JavaScript (`src/lang/`) that **bans dynamic code
generation** — no `eval`, no `new Function(...)`, no `with` — enforced by a
validator (`restrictions.ts`) before analysis. Those bans are what make a
whole-program CFA tractable and sound: the call graph cannot be rewritten at
runtime.

The surface AST is standard **ESTree** (the format the host compiler emits, e.g.
via esprima); the analyzer consumes it directly and does no parsing of its own.
`restrictions.ts` walks the ESTree tree; `normalize.ts` lowers it to a small ANF
core IR (`core.ts`), which the CESK* machine steps. A thin acorn wrapper
(`parse.ts`) exists only for the test suite and demo, and is kept out of the
library's public import graph so consumers never pull in a parser.

### Objects & hidden classes

Object literals, property get/set, and mutation live in a third store component
(`OAddr → AbsObject`), addressed by allocation site `(loc, time)` — so k-CFA
context extends to the heap for free. An `AbsObject` carries a **set of hidden
classes** (`shapes.ts`: interned, ordered `(name, type)` field lists linked by a
transition graph — the V8/Map model) and a field map. Reading a property joins
over every object a value may point to (`elimObj`, mirroring `elimClo`); writing
transitions each object's shape and updates the field, **strong** under concrete
time (`TimeDict.singletonAddrs`) and **weak** under k-CFA. Because objects are
references into the shared store, aliasing is modeled correctly, and per-site
shape sets give monomorphic-vs-polymorphic information for free.

Shapes are **type-aware**: each field carries a representation (`ValDomain.typeSig`,
e.g. `num` / `str` / `num|str` / `obj`), so `{x: number}` and `{x: string}` are
distinct classes and type polymorphism is visible as multiple shapes. This suits
an *ahead-of-time* compiler, which — unlike a runtime JIT that can start with
structural maps and re-specialize representations via deprecate/migrate — must bake
the representation into the class identity before codegen.

**EchoJS object intrinsics, accessors & inlining.** The analyzer consumes EchoJS's
post-class-desugar IR (plain ESTree + object primitives). The normalizer recognizes
`Object.defineProperty`/`defineProperties` (data descriptors → own writes; `{get,set}`
descriptors → a core `defineAccessor` that stores getter/setter closures in the
object's `accessors` map), and `Object.create`/`%objectCreate` + `Object.setPrototypeOf`/
`%setPrototypeOf` for prototype-chain setup. A property access that resolves (over the
chain) to an accessor **dispatches as a call** — `get`/`put` leave the pure
value-producing path and push a frame to enter the getter/setter with `this` = the
receiver. Each such dispatch is recorded per access-site (`accessorGetSites`/
`accessorSetSites`), so `result.accessorSites()` reports monomorphic sites the compiler
can **inline** back to a field load/store.

**Methods & object sensitivity.** `obj.f(args)` reads `f` off `obj` and dispatches
per possible receiver, binding `this` to that receiver (methods are own
function-valued properties, no prototype). This makes a fourth precision knob
possible — the **context strategy** (`ContextStrategy`): the call-context increment
fed to `tick` is the call site (classic k-CFA) or, for a method call, the receiver's
allocation site (**object sensitivity**). `enterClosure` therefore takes a `ctxLoc`
(for `tick`) separate from the `siteLoc` (for the continuation address). Object
sensitivity beats call-site k-CFA on method-heavy code (`npm run bench`).

**Function specialization.** `result.specializations()` reads off, per function,
its `(param types) → return type` table. It needs no extra analysis: each calling
context is already a specialization, so the machine just *records* the observation
— param types at call entry, the return type at each `ret` — keyed on the same
`(owning-lambda, entry-context)` pair (the owner comes from a `ret`-loc → lambda
map built during normalization). Distinct signatures are deduped into rows; a
function with one row is monomorphic. Sharpness tracks `k` and the context
strategy directly.

**Layout & constructors.** `layout.ts` turns the heap into codegen input:
`result.layouts()`/`layoutOf(site)` report, per allocation site, the *terminal*
hidden classes (construction intermediates absorbed by a subset-with-type-compat
filter) laid out as structs (offsets/sizes via a pluggable `SizeOf`). `new`/`this`
are modeled by allocating a fresh object at the `new`-site, binding `this` in the
constructor's environment, and yielding it (or an explicitly-returned object) on
return; the machine records a constructor call graph (`constructorTargets`) so
`result.constructors()` reports each constructor's produced class(es) and
`result.warnings()` flags **polymorphic constructors** (more than one produced
class) — the AOT analogue of a megamorphic allocation site.
