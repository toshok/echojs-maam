# maam-fable

A TypeScript transliteration of David Darais's [**maam**](https://github.com/davdar/maam)
library — the artifact for the paper
[**"Galois Transformers and Modular Abstract Interpreters"**](https://arxiv.org/abs/1411.3962)
(David Darais, Matthew Might, David Van Horn) — packaged for use as a static-analysis
engine inside a **self-hosted TypeScript compiler**.

The whole point of the paper, and of this library: write **one** definitional
interpreter, then recover a whole family of sound program analyses — concrete
evaluation, k-CFA, path/flow/flow-insensitive analyses — by running it under
different monads. The interpreter text never changes; only the monad, the value
domain, and the notion of "time" do.

The analyzer consumes standard **[ESTree](https://github.com/estree/estree)** — the
same AST the host compiler produces — so you feed it your own tree (e.g. from
esprima) directly. `analyze` never parses; parsing is entirely the caller's job.

```
npm install
npm test        # 114 tests: core, analyses, objects, layout, constructors, methods, specialization,
                #             prototypes, EchoJS object intrinsics, and getter/setter accessors
npm run bench   # state-space telemetry + object-sensitivity vs call-site head-to-head
npm run demo    # a guided tour (see below)
```

## What you get

```ts
import { analyze, concreteEval, kCFA } from "maam-fable";
import * as acorn from "acorn"; // any ESTree producer works — acorn, esprima, your compiler

const program = acorn.parse(
  `function fact(n) { if (n < 1) return 1; return n * fact(n - 1); }
   fact(6);`,
  { ecmaVersion: 2022, ranges: true },
) as any; // an ESTree Program

// Concrete evaluation — the interpreter run at the concrete monad:
analyze(program, concreteEval()).result;        // ⇒ { 720 }

// 1-CFA (abstract values + 1 level of call-site context):
analyze(program, kCFA(1)).result;               // ⇒ num:⊤   (sound over-approx)

// Same program, different store-relation precision:
analyze(program, { ...kCFA(2), sensitivity: "path-sensitive" });
analyze(program, { ...kCFA(2), sensitivity: "flow-insensitive" });
```

Programs that could defeat whole-program analysis are **rejected before analysis**:

```ts
analyze(evalProgram, concreteEval());           // throws RestrictionError: no-eval
```

The test suite and demo use a tiny acorn wrapper (`src/lang/parse.ts`) for
convenience; it is the only module that touches acorn, and it is deliberately not
re-exported from the package, so importing `maam-fable` never pulls in a parser.

## The three orthogonal knobs

The paper's central design (§4, §8) factors an abstract interpreter into three
independent choices. Fix all three and you have picked a concrete analysis.

| Knob | Choices | Chosen by |
|------|---------|-----------|
| **Value domain** | concrete `CVal` · abstract `AVal` (constant propagation + closures) | the `ValDomain` dictionary |
| **Time / context** | `Cτ` concrete · `Kτ k` (k-CFA) · `Zτ` (0-CFA) | the `TimeDict` dictionary |
| **Sensitivity** | `path-sensitive` · `flow-sensitive` · `flow-insensitive` | the **monad stack** |

`concrete eval = CVal × Cτ`; `k-CFA = AVal × Kτ k`. Path/flow sensitivity is
orthogonal to both.

### Choosing `k` and sensitivity

`k` is the k-CFA **context** depth (how many call sites of calling-context are kept
apart); sensitivity is the orthogonal **store**-sharing knob. Measured on the
bundled examples:

- **`k` is the dominant lever.** `k = 0` merges every calling context — a
  polymorphic helper collapses to `⊤`. `k = 1` recovers most precision; `k = 2`
  nails the polyvariance example to an exact constant. `kCFA()` therefore defaults
  to **`k = 1`**, not 0.
- **flow-sensitive is the sweet spot** (the default). It respects program order —
  e.g. after `o.x = 1; a = o.x; o.x = "s"`, flow-sensitive reports `a : num`, while
  flow-insensitive reports `a : num | str`.
- **path-sensitive buys nothing over flow-sensitive here**, because the abstract
  value domain is *non-relational* (per-field, no cross-field correlations). It is
  identical in precision on every example and only costs more — path-sensitivity
  pays off only with a relational domain. (It is still exact for the *concrete*
  domain, where it is the default.)

A fourth knob, the **context strategy** (`context: "call-site" | "object"`),
chooses what a call's context increment is: the call site (classic k-CFA) or, for
**method** calls, the *receiver's allocation site* (**object sensitivity**). Object
sensitivity is strictly more precise for method-heavy code at a given `k` — e.g. a
`.get()` invoked from one wrapper on boxes from two allocation sites is
disambiguated at `k=1` under object sensitivity but needs `k=2` under call-site
sensitivity (`npm run bench` shows this head-to-head). And higher precision often
means *fewer* states: for the polyvariance example, `k=2` explores fewer states
and iterations than `k=0` while being exact — removing spurious merges removes the
bogus successor states they generate.

### Stack order → sensitivity (the headline result)

With `St[s]` the state transformer and `Pt` the nondeterminism transformer:

- **`St[s] ∘ Pt`** — state *outside* nondeterminism ⟹ **path-sensitive**
  (`s → ℘(A × s)`: every branch keeps its own store).
- **`Pt ∘ St[s]`** — state *inside* nondeterminism ⟹ **flow-insensitive**
  (`s → ℘(A) × s`: one global store, joined at every branch).
- flow-sensitive sits between (one store per control point).

This library realizes those as two concrete monads
(`pathSensitiveMonad`, `flowInsensitiveMonad`) plus three reachability drivers.
The demo shows the same program losing precision as the store is shared more
aggressively:

```
sensitivity          result             states  iters
path-sensitive       num:{-14,94}          15     20
flow-sensitive       num:{-14,94}          15     20
flow-insensitive     num:{-14,94,202}      15     15
```

## Why TypeScript with dictionary-passing (and not HKT)

MAAM is written in Haskell and is *polymorphic over the monad*. TypeScript has no
higher-kinded types, so we cannot write `forall m. Monad m => …` directly.
Rather than fight for HKT with the fp-ts `URItoKind` defunctionalization trick
(verbose, poor error messages), this port uses **explicit dictionary passing** —
exactly how a Haskell compiler desugars type classes:

- a type class → an `interface` of operations;
- an instance → a value of that interface, passed explicitly;
- the interpreter is written once against a single **opaque** computation type
  `Comp<A>` and an `AnalysisMonad` dictionary. Each concrete monad reinterprets
  `Comp` as its own representation; the tiny amount of unsafe casting is confined
  to each monad, and the interpreter and all client code stay fully typed.

The upshot: the analysis is plain, importable, co-developable TypeScript — which
is what a self-hosted TS compiler needs. See [`docs/DESIGN.md`](docs/DESIGN.md)
for the full rationale and the mapping to the paper.

## The restricted JavaScript dialect

The example language is a real subset of JS — functions/arrows, `const`/`let`,
`if`/`else`, `return`, calls, operators, ternaries, literals, closures, and
(mutual) recursion — with three constructs **deliberately banned** so that a
sound whole-program CFA is even possible:

| Banned | Why |
|--------|-----|
| `eval(...)` | executes arbitrary code synthesized at runtime |
| `new Function(...)` / `Function(...)` | builds a function from a runtime code string |
| `with (...) { ... }` | makes lexical scope unresolvable at compile time |

Violations are reported (with source spans and a named rule) by
`checkRestrictions`, or thrown by `assertRestrictions` / `analyze`.

## Architecture

```
src/
  order.ts          PartialOrder                      (POrdering, ⊑)
  lattice.ts        JoinSemilattice, Lattice, lfp     (⊥, ⊔, least fixed point)
  lattices.ts       flat / product / boolean lattices
  galois.ts         Galois connections                (α, γ, compose, law checks)
  data/             value-keyed FinSet / FinMap + their lattices
  time.ts           Time abstraction                  (Cτ / Kτ k / Zτ)
  monad/
    monad.ts        AnalysisMonad interface + derived ops (the interpreter's contract)
    monads.ts       pathSensitiveMonad, flowInsensitiveMonad (the transformer stacks)
  driver.ts         reachable-states fixpoint          (exploreConfigs / …FlowSensitive / …Global)
  lang/
    ast.ts          ESTree re-exports + a generic node walker & span accessor
    parse.ts        acorn convenience wrapper (dev/test only; not in the public graph)
    restrictions.ts the no-eval / no-Function / no-with validator (walks ESTree)
    normalize.ts    ESTree → ANF core (α-rename, hoist, tail calls, objects)
    core.ts         the ANF core IR the machine steps
    shapes.ts       hidden classes (interned shapes + transition graph)
    state.ts        addresses, environments, closures, continuations, object heap, store
    values.ts       ValDomain + concrete & abstract instances (incl. object refs)
    machine.ts      the CESK* machine — the single definitional interpreter
  layout.ts         hidden classes → struct layouts (offsets, sizes, terminals)
  analysis.ts       ties the knobs together; the analyze() entry point
  index.ts          public API + presets (concreteEval, kCFA)
```

## Using it in a compiler

The analyzer's input is **ESTree** — the exact AST your compiler already builds
(via esprima) — so pass your `Program` straight to `analyze`; there is no parsing
step to route around. `analyze` validates the dialect (`checkRestrictions`),
normalizes ESTree to the ANF core IR (`normalize.ts`), and runs the machine.

The only runtime dependency is `@types/estree` (types). acorn is a *dev*
dependency, used solely by the test/demo parser wrapper; it is not on the path of
`analyze`. If you'd rather analyze a different IR entirely, everything below the
front-end — lattices, monads, drivers, the CESK* machine — is language-agnostic:
target the core IR in `core.ts` directly and supply a new `ValDomain` and `step`.

## Objects & hidden classes

Object literals, property get/set, and mutation are modeled with a **hidden-class
(shape) heap**, in the V8/Map sense. Each object lives at an allocation-site
address `(loc, time)` — so k-CFA context-sensitivity extends to the heap for free
— and carries a set of *shapes* plus a field map. Writes **strong-update** under
concrete time (unique addresses) and **weak-update** under k-CFA.

Shapes are **type-aware**: a shape is an ordered list of `(name, representation)`
fields, so `{x: number}` and `{x: string}` are *different* hidden classes. (A
runtime JIT can start structural and re-specialize representations later; an
ahead-of-time compiler cannot, so the representation is baked into the class
identity up front.) Type polymorphism therefore shows up as multiple shapes in an
object's shape set.

The payoff a compiler wants: per allocation site and per access site you learn the
set of hidden classes, hence whether a site is monomorphic. A function called with
two incompatible shapes has a parameter whose inferred type is the *union* of both
classes:

```ts
const r = analyze(parse(`
  function render(node) { return node; }
  const box    = { width: 10, height: 20 };
  const circle = { radius: 5, color: 1, filled: 1 };
  render(box); render(circle); 0;
`), kCFA(0));

r.shapesOfVar("node").map(shapeToString);
// ⇒ ["{width: num, height: num}", "{radius: num, color: num, filled: num}"]
```

### From hidden classes to memory layout

`result.layouts()` / `result.layoutOf(site)` turn the inferred classes into
concrete **struct layouts** for codegen: per allocation site, the *terminal*
hidden classes (intermediate construction shapes filtered out), and for each a
struct with field offsets and total size computed from a pluggable `sizeOf`
model. A **monomorphic** site is a `malloc(sizeBytes)` + fixed-offset-access
candidate; a polymorphic site is where you choose a tagged union / largest-struct
/ expando fallback. Sites carry their **source span**, so a struct maps back to
code (for emission and warnings).

```
site { hp: 100, name: "hero", alive: true }  — monomorphic ✓ struct-able
  struct (24 bytes) {
    + 0  num   hp
    + 8  str   name
    +16  bool  alive
  }
```

See §5–6 of `npm run demo`.

## Constructors

`new F(args)` and `this` are supported: a fresh object is bound to `this`, the
constructor body builds it up (`this.x = …`), and `new` yields that object (or an
explicitly-returned object). `result.constructors()` reports, per function used as
a constructor, the terminal hidden class(es) its objects settle into and their
struct layouts; `result.warnings()` flags a **polymorphic constructor** — one that
can produce more than one hidden class (incompatible field sets, or a
representation-unstable field like `this.v` being sometimes `num`, sometimes
`str`). Construction intermediates (`{}`, `{x}`, …) are absorbed, so a
straight-line constructor reads as monomorphic.

```
Vec2   monomorphic ✓      {x: num, y: num}
Node   polymorphic (2) ✗  {value: num}  |  {left: num, right: num}
⚠ constructor `Node` may produce 2 distinct hidden classes: {value: num} | {left: num, right: num}
```

See §7 of `npm run demo`.

## Methods & object sensitivity

`obj.f(args)` is a method call: the machine reads `f` from `obj`, dispatches per
possible receiver, and binds `this` to that receiver (so `this.x` reads/writes the
right object). Methods are ordinary function-valued properties — no prototype
needed. Because dispatch is per-receiver, the **object-sensitive** context strategy
(`context: "object"`) can key a method's context on the receiver's allocation site,
which beats call-site k-CFA on method-heavy code (see the head-to-head in
`npm run bench`).

## Function specialization (return type from parameter types)

`result.specializations()` reads off, per function, its `(parameter types) →
return type` table — one row per distinct type signature observed across the
analyzed calling contexts. It's the direct input to monomorphization:

```
id  (x)  2 specializations  (num) → num   |   (str) → str
sq  (n)  monomorphic ✓      (num) → num
⚠ function `id` has 2 type specializations: (num) → num ; (str) → str
```

A single row ⇒ emit one specialized version. Several rows ⇒ emit one per signature
(or a boxed fallback when a return is `⊤`/union). This needs no extra analysis —
it reads the `(param types, return type)` the interpreter already computes per
context — so its sharpness tracks `k` and the context strategy directly. See §8 of
`npm run demo`.

## Classes, prototypes & accessors (EchoJS IR)

The analyzer targets the shape [EchoJS](https://github.com/toshok/echojs) produces
after it desugars `class` syntax (before closure-conversion): plain ESTree plus a
few object primitives. It recognizes and models them:

- `Object.defineProperty(proto, "m", {value})` — a prototype **method** (data prop).
- `Object.defineProperty`/`defineProperties` with `{get, set}` — **accessor
  properties**. A property read/write that hits an accessor **dispatches as a call**
  (getter/setter run with `this` = receiver), walking the prototype chain — so it is
  modeled *soundly*, not ignored.
- `Object.create(p)` / `%objectCreate`, `Object.setPrototypeOf` / `%setPrototypeOf`,
  `%setConstructorKind*` — prototype-chain setup (inheritance).

The accessor payoff is codegen: `result.accessorSites()` reports every property
access that dispatched to a getter/setter and the functions it resolved to. A
**monomorphic** site (one target) is inlinable — the trivial `get area()` folds
back to a `this.w * this.h` field computation, eliminating the call.

## Control flow, arrays & exceptions

The analyzable core is now most of ES: alongside objects/prototypes/accessors it
handles imperative control and data flow, all lowered to the small ANF core:

- **Loops** (`while`/`do`/`for`) lower to tail-recursive local functions;
  `break`/`continue` become continuation calls. They terminate under abstract
  interpretation via the store's finite-height widening.
- **Variable reassignment** (`x = …`, `x += …`, `x++`) — a `setVar` RHS mutates
  the binding; flow-sensitivity then tracks the changing type across the mutation.
- **Arrays** (`[a, b]`, `o[i]`) — index-insensitive: elements smash into one
  bucket, computed keys blur. Numeric-key reads are kept distinct from `length`.
- **Exceptions** — `throw` ends its own control path (`mzero`); `try/catch/finally`
  lowers to a `nondet` between normal completion and the handler, both flowing
  through the finalizer. Sound (handler always considered reachable) but coarse:
  the caught value is approximated as unknown, and `finally` is not re-run on an
  uncaught throw escaping a bare `try/finally`.
- **Modules** — `import`/`export` normalize (exports unwrap to their declaration;
  imports degrade to `undefined`). EchoJS desugars these to `%module*` intrinsics
  before analysis, so this is a robustness fallback, not real cross-module linking.
- **`switch`** (with fall-through), **`for-in`** (enumerates own+inherited property
  names; abstraction-only — the loop bound is nondeterministic), **`delete`** (yields
  `true`; the field is kept — sound for may-types), **computed method calls**
  (`obj[e](args)`), **member updates** (`o.x++`), **`new foo.Bar()`**, and **regex
  literals** (opaque objects) all lower to the same core.

### Running on real code (graceful degradation)

Real programs call things the analyzer doesn't model — runtime builtins (`Math`,
`Array`), a benchmark harness, cross-module imports. A call/`new`/method whose callee
resolves to **no closure** is *degraded*: the result becomes an unknown value (an
empty object for `new`, `undefined` otherwise) and the path **continues** rather than
being silently killed. This is deliberately imprecise (an unknown callee could return
or mutate anything) and is surfaced, not hidden: `result.metrics.unknownCalls` counts
these sites and `result.warnings()` reports them. **In a closed-world AOT program this
count should be 0** — every non-zero entry marks where a result was assumed, not
computed.

### Benchmark corpus (`examples/benchmarks/`)

The bundled Octane benchmarks (BSD / public-domain) are the instrument for the
monomorphism hypothesis and for watching analysis cost grow. `npx tsx
examples/benchmarks/run.ts` sweeps them (subprocess-isolated, with a per-benchmark
timeout/heap cap), reporting parse/normalize/analyze timing plus the N-distribution.
Early findings: cost is dominated by **shape interning, not state count** — `code-load`
converges in <1s with 12/12 *monomorphic* specializations, but `splay` interns ~110k
type-aware hidden classes for only 47 states (recursive data structures with imprecise
field types explode combinatorially), and the heavier benchmarks don't yet converge in
tens of seconds.

Two scaling fixes came out of this:

- **Worklist drivers** (`driver.ts`): the flow-sensitive and flow-insensitive
  fixpoints re-step a control point only when its store input grows, instead of
  re-stepping the whole reached set every round. ~5× on `code-load`, ~2× on `splay`,
  identical results.
- **Order-insensitive shapes** (`shapes.ts`): hidden classes are interned by their
  *sorted* field set, not insertion order. An object built up field-by-field (e.g. a
  prototype whose methods are assigned in a fixpoint-explored interleaving) otherwise
  interns all N! orderings — `splay` was **109,603** shapes for 47 states. After the
  fix it interns **258**, and analysis dropped from **25 s to 64 ms** (~400×). Field
  order is a layout/codegen decision the compiler owns (it can even reorder to pack or
  to keep hot fields in the header's cache line), so class *identity* shouldn't carry
  it. `Shape.fields` stays in canonical order for a deterministic struct.

## Limitations & next steps

This is a faithful, runnable core, not a production analyzer. Known gaps:

- The runtime environment is not modeled: `Object.defineProperty` etc. are
  recognized *syntactically*, which assumes `Object` is the unshadowed builtin
  (true for compiler-generated IR).
- Exceptions are control-only — thrown values aren't propagated to the catch
  binding, and the handler is always treated as reachable (over-approximation).
- Cross-module linking is not modeled; imported names read as `undefined`.
- Strong update keys off `time.singletonAddrs` (concrete ⇒ strong). A recency /
  cardinality abstraction would enable strong update under k-CFA too.
- The abstract numeric/string domains are constant-propagation with a widening
  bound; richer domains (intervals, etc.) slot in as new `ValDomain`s.
- Flow-sensitivity follows the public Haskell (a collecting-set widening) rather
  than the paper's distinct `Ft` transformer.
- `%constructSuperApply` (spread `super(...args)`) is not yet modeled.

## References

- Darais, Might, Van Horn. *Galois Transformers and Modular Abstract
  Interpreters.* OOPSLA 2015. [arXiv:1411.3962](https://arxiv.org/abs/1411.3962)
- Van Horn, Might. *Abstracting Abstract Machines.* ICFP 2010.
- Darais, Labich, Nguyễn, Van Horn. *Abstracting Definitional Interpreters.*
  ICFP 2017.
- Original Haskell: <https://github.com/davdar/maam>
