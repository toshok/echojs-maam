# Total, Composable Abstract Interpretation for JavaScript

> **Rough full draft.** Numbers are real (measured on the current implementation)
> except where marked ⟨PENDING⟩. Prose is first-pass; tighten on the editing
> pass. Section numbering follows the intended final structure.

---

## Abstract

We present a whole-program abstract interpreter for a JavaScript core, built as
the static-analysis engine of a self-hosted, ahead-of-time TypeScript compiler.
The analyzer follows the Abstracting Abstract Machines (AAM) recipe and the
Galois-transformer factoring of Modular Abstract Interpreters (MAAM): a single
monadic small-step relation from which both a faithful concrete interpreter and a
family of abstract analyses are *assembled* by swapping four components — value
domain, context abstraction, control sensitivity, and fixpoint driver. Onto this
core we compose, as five independent and individually-ablatable knobs, a decade of
precision and performance techniques from the "Might diaspora": abstract garbage
collection, recency-based strong update, abstract counting, P4F pushdown, and a
megamorphic shape widening. Because an AOT compiler may not refuse any input, we
add an adaptive per-function context cap that bounds the reachable state space to
`locations × (cap + 1)`, making the analysis **total** — guaranteed to terminate
on every program — with a precision knob in place of a precision cliff. Using the
analyzer as an instrument over the Octane benchmark suite, we find that real
JavaScript is overwhelmingly monomorphic — 353 of 353 function specializations —
and, crucially, that this monomorphism *survives* the coarsening the totality
guarantee imposes: the precision a naïve analysis spends distinguishing contexts
is, empirically, mostly redundant. Per-technique ablations quantify what each knob
buys, including a two-sided result — abstract counting yields a 12.8× shape
reduction on crypto but regresses the allocation-heavy box2d — that we trace to a
fundamental limitation of context-insensitive strong update.

---

## 1. Introduction

Ahead-of-time compilation of a dynamically-typed language rests on a static
analysis that answers a deceptively simple question: *at this program point, what
could this value be?* For an ahead-of-time compiler the question carries an
unusual constraint. A just-in-time compiler may observe a value's actual type at
run time and deoptimize when it guesses wrong; an AOT compiler has one shot, and —
more sharply — it may not *refuse* to compile a program. Whatever pathological
control or data flow a source file contains, the analysis must terminate and
return a sound answer. There is no "analysis timed out, please simplify your code."

This paper reports on the static-analysis engine of a self-hosted AOT TypeScript
compiler, and on what building under that constraint taught us. The engine is an
abstract interpreter for a JavaScript core in the style of Abstracting Abstract
Machines [Van Horn & Might 2010], organized — following the Galois-transformer
view of Modular Abstract Interpreters [Darais et al. 2015] — as a single
parameterized step relation. Our contribution is not a new analysis algorithm but
three things that emerge from taking composition, totality, and measurement
seriously in one system.

**Composition.** The literature offers a rich menu of precision- and
performance-enhancing techniques for control-flow analysis — abstract GC, recency
abstraction, abstract counting, pushdown/CFA2 — many due to Matthew Might and
collaborators. In their original presentations each is entangled with a specific
analysis. We show that on a modern AAM core they refactor cleanly into
*orthogonal, individually-toggleable parameters* over one step relation. Each is a
single flag; they compose; and — the property we exploit throughout — each can be
ablated to measure its actual contribution. From the same step relation, a
faithful concrete interpreter also drops out, and (a property we verify survives
every extension) does so exactly.

**Totality.** The AOT constraint forces the analysis to terminate on *every*
input. AAM makes the state space finite for a fixed context abstraction, but
flow-sensitive analysis of a real program can still produce astronomically many
*states*, exhausting time or memory in practice even where it terminates in
theory. We introduce an adaptive per-function context cap: once a function has
been entered in more than `cap` distinct calling contexts, further calls collapse
to a single widened continuation, and environments are canonicalized per program
point (sound at `k = 0`). This bounds the reachable state space to
`locations × (cap + 1)` — a *total* analysis, terminating on any input, trading
precision for a guaranteed result via a knob rather than falling off a cliff.

**Measurement.** With termination guaranteed, the analyzer becomes an instrument.
The question it is built to answer at scale — how polymorphic is real JavaScript?
— has a striking answer on the Octane suite: **every one of 353 function
specializations is monomorphic**. More striking, this survives the coarsening the
totality cap imposes. Coarsening the context does not manufacture polymorphism,
because the polymorphism was not there to begin with; the precision a context-
sensitive analysis spends is, for this class of program, mostly redundant. We
temper this with an honest counterpoint: object *layout* polymorphism, which our
type-aware hidden-class abstraction is designed to see, is real though rare (some
constructors build objects of more than one shape), and those are precisely the
sites an AOT compiler must handle dynamically.

**Contributions.**
- A single parameterized abstract interpreter for a JavaScript core in which value
  domain, k-CFA context, control sensitivity, and five orthogonal precision
  techniques are independent knobs over one monadic step relation, preserving the
  MAAM property that a concrete interpreter is recovered by component selection
  (§3, §4).
- A type-aware hidden-class ("shape") abstraction that yields, as a direct analysis
  product, the per-site specialization and layout data an AOT compiler consumes
  (§3.3).
- A totality guarantee via an adaptive context cap bounding the state space to
  `locations × (cap + 1)`, terminating on any input (§5).
- A value-level model of the JavaScript standard library — statics, prototype
  methods with heap effects, and higher-order methods that enter the user callback
  through the machine — that tightens the soundness envelope (removing the
  degradation over-approximation) and, in doing so, makes callbacks reachable only
  through `map`/`reduce` analyzable and hence compilable (§4.7).
- An empirical study over Octane establishing near-total function-level
  monomorphism that survives coarsening, with per-technique ablations — including a
  negative result for abstract counting that exposes a `k = 0` strong-update
  ceiling (§6).

### A worked example: from analysis to a compiled loop

> *(This is intended as a standalone "Overview" section (§2) in the final draft;
> subsequent sections renumber. Kept in §1 here to avoid churn.)*

Consider three lines of ordinary JavaScript:

```js
function scale(x) { return x * 100; }
const out = [1, 2, 3].map(scale);
out[0];
```

Nothing in this program calls `scale` directly. To a control-flow analysis that
does not model `Array.prototype.map`, the call `[1,2,3].map(scale)` is a call to an
unknown callee: it degrades to an unknown result, `scale` is *never entered*, and
`out` is an unknown value. `scale` is, to the analysis, dead code — and therefore
to an ahead-of-time compiler it is a function with *no type information at all*.
This is the state of our analyzer with intrinsic modeling off, and we have measured
exactly it: `scale` does not appear in the specialization report, and `out[0]`
reads as ⊥/degraded.

With the standard library modeled (§4.7), `map` is a known operation whose semantics
the analyzer executes: it enters the callback with the array's (abstract) element
value and collects the callback's return into a fresh result array. The same three
lines now yield four facts, each a precondition a compiler needs:

1. **The callee is known.** `map` resolved to a modeled intrinsic, not an unknown
   call, so the compiler may lower `map` *itself* to a loop rather than a call.
2. **The callback resolves to a single closure** (`scale`) — one body to inline, no
   dispatch.
3. **The callback is type-monomorphic**, reported as `scale : (num) → num` — the
   inlined body needs no argument guard.
4. **Element and result types are known** — `num[]` in, `num[]` out — so both the
   read and the freshly-allocated result array are unboxed.

Composing the four, the source compiles to a monomorphic, unboxed loop with the
callback spliced in — no closure allocation, no dynamic dispatch, no boxing, no
deoptimization guard:

```
out : num[len]
for i in 0 .. len-1:
    out[i] = in[i] * 100        // scale inlined; num throughout
```

This is the callback-inlining a just-in-time compiler performs *speculatively*,
recovering from a wrong guess by deoptimizing. Our analyzer establishes the same
preconditions *statically and soundly*: monomorphism is a proven property of the
whole program, not a runtime observation that may be invalidated, so the AOT
compiler emits the specialized loop with no fallback path.

Two points of the paper are visible in this one example. First, the analyzer's
*index-insensitivity is aligned with the transform, not a limitation of it*: the
callback is entered **once** with the smashed element value precisely because
inlining wants a single body valid for every element; per-element analysis would be
wasted work. Second, the monomorphism verdict *is* the compiler's decision procedure
— one target and one type row means "inline, unguarded"; had the array been
`num | str`, the analyzer would report `(num | str) → …` and hand the compiler the
exact reason it needs a guard or a second specialization. The rest of the paper is
about making analyses like this one *total* (so no program is un-analyzable, §5) and
about *measuring* how often real code is this monomorphic (§6).

---

## 2. Background

### 2.1 Abstracting Abstract Machines

AAM [Van Horn & Might 2010] derives a computable abstract interpreter from a
concrete small-step machine by a single systematic change: *store-allocate*
everything recursive. A concrete CESK machine has a control expression, an
environment, a store, and a continuation; making the analysis finite is a matter
of bounding the address space the store ranges over and store-allocating the
continuation (the "CESK\*" machine) so the call stack, too, becomes heap data. A
finite address space makes the store a finite map into a join-semilattice, the
state space finite, and the collecting semantics computable as a least fixed point.

The address abstraction is the analysis's single tuning point for *context
sensitivity*: addresses tagged with the last `k` call sites yield k-CFA. `k = 0`
(0-CFA) merges all calling contexts of a variable to one address — the cheapest,
coarsest analysis.

### 2.2 Galois transformers and modular abstract interpreters

The Galois-transformer view [Darais et al. 2015] observes that the *shape* of the state space — whether
the analysis is path-sensitive, flow-sensitive, or flow-insensitive — is itself a
parameter, expressible as a choice of monad. A path-sensitive analysis threads
state through a nondeterminism monad that keeps configurations distinct; a
flow-insensitive analysis threads a single global store. The same underlying
transition function, written monadically, runs under all of them. The concrete
interpreter is the instance at the identity/deterministic monad with an exact
value domain and unbounded addresses. This is the property we preserve: analyses
are *assembled from components*, not written.

### 2.3 The precision diaspora

A line of work, much of it by Might and collaborators, sharpens CFA:
- **Abstract garbage collection** and **abstract counting** [Might & Shivers 2006]
  — restrict the store to reachable addresses, and track how many concrete objects
  an abstract address summarizes, enabling strong update.
- **Recency abstraction** [Balakrishnan & Reps 2006] — split each allocation site
  into a most-recent (strong-updatable) and a summary address.
- **Pushdown / CFA2 / P4F** [Vardoulakis & Shivers 2010; Johnson & Van Horn 2014;
  Gilray et al. 2016] — recover exact call/return matching that store-allocated
  continuations otherwise smear.

Each targets a specific source of imprecision or cost. Our system implements all
of them over one core and measures them against each other.

---

## 3. Architecture

### 3.1 A CESK\* machine over an ANF core

The analyzer is a small-step CESK\* interpreter for a normalized JavaScript core.
Source JavaScript — a restricted dialect with no `eval`, `new Function`, or `with`,
consistent with an AOT setting where the whole program is known — is desugared to
an A-normal-form intermediate representation in which every intermediate result is
let-bound and every call occupies a tail position with an explicit continuation.
Two desugaring choices matter for precision. First, `this` is bound as an ordinary
*per-function parameter* (named after the enclosing lambda) rather than treated as
a magic global, so distinct functions' receivers occupy distinct addresses instead
of colliding. Second, prototypes and methods are lowered to ordinary object and
property operations, so the analysis need model only a small object calculus.

A machine *control* is `(control-expr, env, kaddr, time)`. The *store* is a product
of four finite maps, each a join-semilattice combined pointwise:

```
Store = (vals   : Addr  → Val)           -- variable bindings
      × (konts  : KAddr → ℘(Kont))        -- store-allocated continuations
      × (objs   : OAddr → Object)         -- the heap
      × (counts : OAddr → {ONE, MANY})    -- abstract counts (§4.4; empty when off)
```

Every address carries a `time` component drawn from a finite `Time`; finiteness of
`Time` is what makes the address space, and hence the analysis, finite. An
`Object` is a set of *shapes* (§3.3), a field map, an accessor (getter/setter) map,
a set of prototype links, and an index-insensitive "elements" bucket for arrays
and computed writes.

### 3.2 One step relation, four swappable components

The transition relation is a single monadic function

```
step : AnalysisMonad<Store> ⇒ (Control → Comp<Control>)
```

polymorphic in the monad `M`. An analysis is *assembled* by choosing four
components, after which the same `step` is iterated to a least fixed point by a
driver:

| component        | concrete interpreter        | abstract analysis                    |
|------------------|-----------------------------|--------------------------------------|
| **value domain** | exact values                | constants ⊕ closures ⊕ object refs   |
| **time**         | unbounded, singleton addrs  | k-CFA (`k = 0` default)              |
| **monad**        | deterministic / path        | nondeterministic + store-state       |
| **driver**       | configuration collection    | collecting semantics to fixpoint     |

Control **sensitivity** is not an argument to `step` but a property of the monad
and driver: a path/flow-sensitive monad threads a per-control-point store, a
flow-insensitive monad threads one global store, and nothing in `step` changes.
The value domain is a join-semilattice of type-tagged constant sets plus closure
and object-reference sets; the concrete domain is the special case in which every
set is a singleton and joins never widen.

**Concrete recovery, preserved.** Selecting the concrete domain, concrete time,
and the path-sensitive monad recovers a faithful interpreter from the very same
`step`. This is not merely true of the base machine but is preserved through every
widening in §4, by construction: the two operations that could lose information —
object *installation* and property *write* — both test `time.singletonAddrs` (true
under concrete time) *first*, performing an exact strong update and never
consulting the abstract machinery (counts, shape caps, weak joins). Every abstract
technique is therefore structurally unreachable under concrete time. Concretely
evaluating `new Pt(id(3), id("s")).a` yields exactly `3`; the 0-CFA analysis of the
same program soundly reports `{3}` for the numeric component (and `"s"` in the
string component, since 0-CFA merges the two calls of `id`).

### 3.3 Type-aware hidden classes

Objects are abstracted by *shapes* — hidden classes in the sense of a modern
JavaScript engine, but abstracted and made *type-aware*. A shape records the
object's set of property names together with the abstract type of each field's
value; two objects with the same fields but different field types have different
shapes. Shapes are interned into a transition graph shared across the analysis run:
extending a shape with a property `p : τ` is a memoized graph edge, so the millions
of `addProperty` operations a run performs collapse onto a small interned graph.
Shapes are canonicalized to be insensitive to the *order* in which properties are
inserted while remaining sensitive to the *set* of (name, type) pairs — the
abstraction a compiler's struct layout actually depends on.

Shapes are the analyzer's compiler-facing product. Two reports fall directly out of
the shape and heap data:

- **Specializations.** For each function, the set of observed
  (parameter-type-tuple → return-type) rows, accumulated per (function,
  entry-context). A single row means the function is *monomorphic*: one compiled
  specialization suffices. Multiple rows name the exact type-polymorphism a
  compiler must either specialize or box.
- **Constructors.** For each constructor, the shapes of the objects it builds. A
  single shape means a monomorphic layout — a fixed struct; multiple shapes name a
  site that must be compiled with a layout guard.

A **megamorphic ⊤-shape** (§4.6) sits at the top of the shape lattice: an object
that may have any field. Reads from a ⊤-shape object are still handled soundly (the
field may be present or absent, so the read continues up the prototype chain and to
`undefined`), but the layout is not compilable to a fixed struct — the analysis has
declared the site megamorphic.

---

## 4. Precision and performance as orthogonal knobs

Each technique below is a single independent flag over the §3 core. They compose;
§6 evaluates them in isolation and together. All are sound; several are *precision*
improvements, several are *cost* controls, and one (abstract GC) is both.

### 4.1 Context sensitivity (`k`)

Standard k-CFA. Addresses are tagged with the last `k` call sites. `k = 0` is the
default; §6 finds it sufficient for function-level monomorphism across the suite.
Increasing `k` splits calling contexts and is the principled (but expensive) fix
for the strong-update ceiling of §4.4.

### 4.2 Abstract garbage collection (`gc`)

Following ΓCFA [Might & Shivers 2006], at each control point we restrict the store
to the addresses reachable from that point's environment and continuation — a
mark-and-sweep over the abstract heap. This attacks the dominant cost of
flow-sensitive analysis, the size of per-control-point stores, and *sharpens*
precision: a dead binding cannot merge with a live one of the same address in a
later context. Abstract GC is also the enabler for abstract counting (§4.4):
collecting an address resets its count, which is what lets a non-escaping
allocation remain a strong-updatable singleton.

### 4.3 Recency: strong update on singletons (`recency`)

A function's prototype object is a statically-known singleton — one per function,
never reallocated. Writes to such an object may *replace* rather than *accumulate*.
Without this, installing N methods on a prototype accretes the full 2ᴺ subset
powerset of field sets (every order and subset the flow-merge admits); with it,
the prototype's shape walks a single linear chain of length N. `recency` is a
uniform, cheap win and is on in every converging configuration in §6.

### 4.4 Abstract counting (`counting`)

Abstract counting [Might & Shivers 2006] generalizes §4.3 from prototypes to *any*
address. The store carries a per-address count in `{ONE, MANY}` (absent = zero); a
(re)allocation *bumps* the count (`0 → ONE → MANY`), and a property write to a
`ONE` address is a sound strong update — the address provably summarizes at most
one concrete object, so overwriting loses nothing. The count lattice is
`0 ⊑ ONE ⊑ MANY` with join = max, so at a control-flow merge an address that is
`ONE` on one path and `MANY` on another becomes `MANY` (some concrete configuration
has several objects there, so strong update would be unsound).

The technique pairs with abstract GC (§4.2): because GC drops dead addresses'
counts back to zero, a non-escaping allocation whose previous incarnation has been
collected bumps `0 → ONE` again and stays strong-updatable across iterations. This
collapses a once-allocated object's field initialization from a 2ᴺ shape powerset
to an N-step linear chain — measured directly on a four-field constructor, **16 →
5 shapes** (§6.3).

We implement counting on the *single* per-site address, not the two-address
recency split of Balakrishnan & Reps [2006]. This is a deliberate soundness
choice: single-address counting has no stale-pointer hazard (a strong update
overwrites the one object the address denotes), whereas the two-address split must
reconcile references to a most-recent object after it has aged into the summary. We
return to the precision cost of this choice in §6.3 and §7.

### 4.5 P4F pushdown (`pushdown`)

Store-allocating continuations makes the state space finite but smears returns: a
function returns to *every* context that shares its call site, not its actual
caller. P4F [Gilray et al. 2016] keys each continuation address on the caller's
*environment* in addition to the call site, recovering exact call/return matching
without a separate pushdown system. In principle this helps deep and recursive call
graphs where return smearing multiplies contexts; §6.3 finds it a *net cost* on the
Octane workload, whose programs are already monomorphic enough that the exact
matching only adds context distinctions. It is off in the recommended configuration.

### 4.6 Shape cap (`shapeCap`)

The state cap (§5) bounds the *number of states*; it does not bound the *shape*
space at a single address. An allocation-heavy program that builds many distinct
hidden classes at one site can exhaust memory in the object heap even with a
bounded state count. The shape cap addresses this orthogonally: once the number of
distinct shapes at an address exceeds a threshold, its shape set is widened to the
megamorphic ⊤-shape. This bounds heap memory and is, together with the state cap,
what the most allocation-intensive benchmark (box2d) requires to converge.

### 4.7 Standard-library intrinsics (`intrinsics`)

The knobs above tune *precision*; this one tunes the *soundness envelope's tightness*.
A whole-program analysis of real JavaScript inevitably calls into the standard
library — `Math.floor`, `new Array(n)`, `str.charCodeAt`, `arr.map(f)`. With the
library unmodeled, such a call resolves to no closure and must be *degraded*: its
result is taken to be unknown (⊤) and the path continues. Degradation is sound but
lossy, and — as §6.2 notes — can only *inflate* apparent polymorphism, since ⊤
flowing out of a library call is maximally imprecise.

We model the library at the value level. The initial store is seeded with the
globals as *intrinsic* values carrying summary transfer functions; a call whose
callee is an intrinsic dispatches to its summary rather than degrading. The model
composes with the object machinery rather than special-casing syntax: `Math` is an
ordinary object whose fields are intrinsic functions (so `var f = Math.floor; f(x)`
works via the normal property read); `Array.prototype` is a real object that
freshly-allocated arrays link to (so `arr.push` resolves through the prototype
walk); and mutating methods (`push`) apply a heap effect on the receiver's elements.
Three tiers of coverage, in increasing difficulty: (1) pure statics and constructors
(`Math.*`, `parseInt`, `new Array`); (2) prototype methods with heap effects
(`push`/`slice`/`charCodeAt`); (3) higher-order methods (`map`/`forEach`/`reduce`),
which *enter the user callback through the machine* — the case the §1 worked example
turns on. Because array elements are index-insensitive, a higher-order callback is
entered once with the smashed element value, so modeling it adds no state explosion
(measured: nested `map`s stay bounded; benchmarks without higher-order calls are
byte-identical on/off).

The effect is a precision/soundness win rather than a cost control: it removes the
degradation over-approximation (tightening the monomorphism result of §6.2), and it
*discovers* code that degradation hid — a function used only as a `map` callback goes
from unanalyzed to fully specialized `(num) → num` (§1). Its shape-space effect is
two-sided and workload-dependent (§6.3): on array-by-index code (crypto) it removes
⊤-pollution and *reduces* shapes; on `Math`-heavy code it *differentiates* previously
collapsed `undefined` results into real typed shapes.

---

## 5. Totality

### 5.1 The problem

For a fixed context abstraction, AAM guarantees a finite state space and thus
termination *in principle*. In practice, flow-sensitive analysis of a real program
can produce enough states to exhaust time or memory long before the theoretical
bound is reached — the state space, though finite, is enormous. For a JIT this is
merely slow; for our AOT setting it is a correctness-level failure, because the
compiler must produce *some* sound result for *every* input. Totality here means
not just "terminates eventually" but "terminates within a bound we control."

### 5.2 An adaptive per-function context cap

We bound the reachable state space directly. Two mechanisms combine:

1. **Per-program-point environment canonicalization.** Under the cap, a control
   point's identity drops the environment's interned id. At `k = 0` the environment
   is determined by the control location, so distinct path-dependent environments at
   the same point are spurious distinctions; merging them is sound and removes a
   multiplier. (Value differences remain in the store, which is joined per point.)

2. **Per-function context capping.** The machine tracks, per function location, the
   set of distinct continuation addresses it has been entered with. Once a function
   has been entered in more than `cap` distinct contexts, every further caller is
   routed through a single *widened* continuation address shared by all such
   callers. Their continuations merge there; the function's returns smear back to
   every over-cap caller — a deliberate loss of return precision — but the number of
   distinct calling contexts per function is bounded by `cap + 1`.

### 5.3 Termination bound

**Proposition (totality).** *Under the state cap with parameter `cap ≥ 1` at
`k = 0`, the number of reachable control states is at most `L × (cap + 1)`, where
`L` is the number of program locations.*

*Argument (sketch).* A control state under the cap is identified by
`(location, continuation-address, time)`. At `k = 0`, `time` is a single point.
Environment ids are canonicalized away (mechanism 1), so they do not multiply
states. For each function, the continuation address is drawn from at most `cap`
per-context addresses plus one shared widened address — at most `cap + 1` values —
and every location belongs to one function. Hence at most `L × (cap + 1)` control
states, each with one joined store. ∎

The store at each point is itself bounded (finitely many addresses, each mapping
into a finite-height lattice once shapes are capped, §4.6), so the whole analysis
terminates within a bound set by `cap`. Precision is recovered monotonically as
`cap` is raised; §6.2 measures the states-vs-precision curve. The cap is *adaptive*
in that it fires only for functions that actually exceed `cap` contexts — a
monomorphic-in-context function is never widened.

---

## 6. Evaluation

We evaluate on the Octane benchmark suite (BSD / public domain), a standard
collection of moderately-sized real JavaScript programs (a scheme/richards-style
scheduler, a constraint solver, a raytracer, a 2-D physics engine, an RSA
big-integer implementation, and others). Each benchmark is analyzed whole-program:
its `setup`/`run`/`teardown` entry points are invoked from a synthetic driver, and
unbound runtime intrinsics (`Math`, `Array`, the benchmark harness) are soundly
*degraded* — a call to an unmodeled callee yields an unknown result and continues,
over-approximating its effect. All measurements are at `k = 0`, flow-sensitive, on
⟨MACHINE SPEC — pending⟩.

> **TODO (measurement platform).** Every timing in §6 is currently from a
> development laptop (Apple Silicon) and is *provisional*. Before submission,
> regenerate the entire results set in one batch on the reference machine (AMD
> Ryzen 7, ⟨exact model / clock / RAM⟩; Node.js ⟨version⟩, ⟨heap cap⟩) so all times
> are mutually consistent and reproducible, and fill in `⟨MACHINE SPEC⟩` here. The
> *structural* results — state/shape/specialization counts and every monomorphism
> verdict — are hardware-independent and will not change; only wall-clock times
> will. Note that the state cap needed for a benchmark to converge is a function of
> the *memory/time budget*, not just the analysis, so the per-benchmark valve
> settings in §6.1 (e.g. crypto `stateCap = 1`) should be re-confirmed on the
> reference machine, where a larger budget may permit a higher cap (more precision)
> within the same guarantee.

**Research questions.**
- **RQ1 (totality).** Does the analysis terminate on the whole suite, and what does
  termination require of the knobs?
- **RQ2 (monomorphism).** How monomorphic is real JavaScript under this instrument,
  and does monomorphism survive the coarsening totality imposes?
- **RQ3 (ablation).** What does each precision knob actually buy?

### 6.1 RQ1 — Whole-suite totality

With abstract GC and recency alone, five of eight benchmarks converge. The
remaining three are resource-bound: crypto and raytrace by the *state* space, box2d
by the *shape* space. Under the total configuration — GC + recency + the adaptive
state cap, plus the shape cap where an allocation-heavy program requires it — **all
eight terminate**:

| benchmark      | knobs beyond GC+recency | time    | states | shapes | specs (mono) | ctors (mono) |
|----------------|-------------------------|--------:|-------:|-------:|--------------|--------------|
| splay          | —                       | 0.01 s  |     47 |     11 | 2 (2)        | 0            |
| navier-stokes  | —                       | 0.04 s  |    138 |    257 | 12 (12)      | 1 (1)        |
| code-load      | —                       | 0.06 s  |    113 |      2 | 12 (12)      | 0            |
| deltablue      | —                       | 0.40 s  |    444 |    192 | 27 (27)      | 8 (8)        |
| richards       | —                       | 2.2 s   |    600 |   1057 | 39 (39)      | 7 (2)        |
| raytrace       | stateCap = 2            | 5.4 s   |    442 |    108 | 3 (3)        | 0            |
| box2d          | shapeCap = 8, stateCap=1| 27.8 s  |   2997 |    861 | 26 (26)      | 1 (1)        |
| crypto         | stateCap = 1            | 192.6 s |   4747 |   7204 | 232 (232)    | 7 (3)        |

crypto at 192.6 s is slow but *bounded*: the guarantee the AOT compiler needs is
termination, not speed, and the state cap delivers it where every prior
configuration diverged. box2d is the case that establishes the shape cap and state
cap as *orthogonal* — it needs both, because bounding the number of states does not
bound the number of hidden classes at a single allocation site.

### 6.2 RQ2 — Monomorphism, and its survival under coarsening

**Function-level monomorphism is total: 353 of 353 specializations are
monomorphic**, across every benchmark, including all 232 in crypto (a jsbn
big-integer/RSA implementation, the largest and least regular program in the
suite). Under 0-CFA with these abstractions, every function is observed at a single
(parameter-types → return-type) row.

The load-bearing observation is that **this holds under the state cap's
coarsening**. The cap merges calling contexts to enforce the termination bound of
§5.3; one might expect that merging to *manufacture* polymorphism by conflating
distinct uses. It does not. Coarsening the context does not create polymorphism,
because for this class of program the polymorphism was not there to begin with —
the precision a context-sensitive analysis spends distinguishing these contexts is
redundant. This is the paper's central empirical claim, and the totality mechanism
is what makes it measurable on programs that otherwise would not converge at all.

The state-cap precision curve makes this concrete. Raising the cap on richards
weakens the coarsening — more calling contexts are kept distinct, so the state
count rises — while the monomorphism verdict does not move:

| richards, cap = | states | specs (mono) |
|-----------------|-------:|--------------|
| 1               |    547 | 39 (39)      |
| 2               |    600 | 39 (39)      |
| 4               |    639 | 39 (39)      |
| 8               |    660 | 39 (39)      |
| off             |    778 | 39 (39)      |

The most aggressive setting (`cap = 1`) discards 30% of the states the uncapped
analysis explores (778 → 547) and loses *nothing*: all 39 specializations remain
monomorphic across the entire range. The states the cap merges away carried no
polymorphism to distinguish. This is the coarsening-is-precision-neutral claim in
one table, and — because the cap is what lets crypto and box2d converge at all —
it is measurable precisely on the programs for which it matters most.

**Object-level polymorphism is real but rare.** Constructors are *not* all
monomorphic: richards reports 2 of 7 monomorphic, crypto 3 of 7. A minority of
allocation sites build objects of more than one shape. This is the honest
counterpoint and, we argue, a strength of the type-aware shape abstraction: it
*finds* genuine layout polymorphism that a type-only abstraction would miss, and
those sites are exactly the ones a compiler must compile with a layout guard rather
than a fixed struct. The finding is not "everything is monomorphic" but
"monomorphism is the rule and the exceptions are identified precisely."

### 6.3 RQ3 — Ablation

**Abstract counting (§4.4)** is the sharpest ablation, because its effect is
workload-dependent and, at `k = 0`, two-sided:

| workload             | shapes: counting off → on | outcome                          |
|----------------------|--------------------------:|----------------------------------|
| 4-field constructor  | 16 → 5                    | mechanism confirmed (2⁴ → N+1)   |
| crypto               | **7204 → 561** (12.8×)    | large win; still 232/232 mono    |
| richards             | 993 → 648 (−35%)          | win; small time cost             |
| box2d                | 861 → **1270**            | **regression**; slower           |

Counting collapses the field-initialization powerset for allocation-*light* code —
crypto's big-integer objects and richards's tasks and packets are constructed once
and their addresses are singletons — where it is a large, precision-preserving win
(crypto stays 232/232 monomorphic). It *regresses* box2d, whose `Vec2` objects are
allocated in physics inner loops. At `k = 0` a reused loop variable keeps the prior
object's address live across iterations, so the count saturates to `MANY`
regardless, and counting only adds store-component overhead plus transient
chain-shapes before the site goes megamorphic.

This exposes a **fundamental `k = 0` ceiling**: single-address counting cannot keep
a looped allocation strong-updatable when the source variable is reused, because
monovariance collapses the fresh object and its predecessors onto one address, and
GC cannot collect an address the live variable still names. The two-address recency
split [Balakrishnan & Reps 2006], or simply `k ≥ 1`, would separate the fresh
allocation and recover strong update; that is the natural next increment (§7).
Because the effect is two-sided, counting is kept a *separate* knob from recency
(a uniform, cheap win) rather than bundled — a design decision the measurements
forced, not one taken a priori.

**Abstract GC (§4.2).** On the already-tractable benchmarks, GC is a shape-space
and speed win rather than a state-count win:

| benchmark      | gc off (states / shapes / time) | gc on (states / shapes / time) |
|----------------|---------------------------------|--------------------------------|
| richards       | 778 / 1041 / 3.8 s              | 778 / 993 / 2.7 s              |
| deltablue      | 584 / 256 / 0.9 s               | 581 / 192 / 0.4 s              |
| navier-stokes  | 146 / 257 / —                   | 146 / 257 / —                  |
| splay          | 47 / 11 / —                     | 47 / 11 / —                    |

GC reduces shapes (dead bindings can no longer merge into live objects) and roughly
halves analysis time (smaller per-point stores mean cheaper joins), with
monomorphism preserved throughout; on the smallest benchmarks it is inert. The
state-count effect is modest *here* precisely because these programs are already
small enough to converge without it. GC's decisive role is on the resource-bound
benchmarks (crypto, raytrace, box2d), which do *not* converge without it at all —
the reachability restriction is what keeps their per-point stores from compounding
across the state space. GC is thus the primary flow-sensitivity enabler even though
its effect on the easy cases looks incremental.

**P4F pushdown (§4.5).** Pushdown is a *net-negative* on this workload — a result
worth stating plainly:

| benchmark  | push off (states / time) | push on (states / time) |
|------------|--------------------------|-------------------------|
| richards   | 778 / 2.6 s              | 1316 / 3.9 s            |
| deltablue  | 581 / 0.4 s              | 665 / 0.5 s             |
| raytrace   | 442 / 5.6 s              | 446 / 5.7 s             |

Keying continuation addresses on the caller's environment *adds* context
distinctions (richards 778 → 1316 states, +69%) while leaving the monomorphism
verdict unchanged (39/39 throughout). P4F pays off when return-flow smearing causes
spurious value merges that cascade into a larger state space elsewhere; on
already-monomorphic programs there is no such cascade to prevent, so the exact
call/return matching only multiplies contexts. This is a second instance of the
paper's theme — added precision that the workload does not need is not free — and a
reason pushdown is *off* in the recommended configuration. It remains available for
programs (e.g. heavily higher-order or CPS-style code) where return smearing does
cascade; we simply do not observe that regime in Octane.

**Standard-library intrinsics (§4.7).** Modeling the library reduces the number of
call sites that must be degraded (`unknownCalls`) across the board — the metric that
most directly measures where the analysis, and hence a compiler, must give up:

| benchmark | unknownCalls (off → on) | shapes (off → on) |
|-----------|-------------------------|-------------------|
| crypto    | 19 → **8**              | 7204 → **5179**   |
| navier-stokes | 9 → **3**           | 257 → 257         |
| richards  | 5 → **3**               | 993 → 1065        |
| deltablue | 9 → **7**               | 192 → 192         |

Monomorphism is preserved throughout (e.g. crypto stays 232/232), and on crypto the
analysis is also *faster* (249 → 190 s) because sharper value types cut spurious
exploration. The shape-space effect is two-sided and diagnostic of *why* a program
was imprecise: crypto's arrays (used by index) shed the ⊤-pollution that unmodeled
`new Array` injected (−28%), whereas `Math`-heavy code (richards) sees a small
*increase* — degradation had collapsed `Math` results to a single `undefined`, and
real `num` typing correctly differentiates them. Neither changes the state count.

The sharpest effect is not in these totals but in *coverage*, and it is the §1
example measured: a function reachable only as a higher-order callback is, with the
library unmodeled, never entered — absent from the analysis and thus uncompilable;
with modeling on it is entered and reported as a monomorphic `(num) → num`
specialization. Octane predates functional-style JavaScript and exercises this
little (its higher-order calls are on unrun jQuery source), so the coverage gain is
demonstrated on constructed inputs rather than suite totals; we expect it to dominate
on modern code.

### 6.4 Baseline comparison

The natural baseline is JSAI [Kashyap et al. 2014], the closest architectural
neighbor (a configurable AAM-style JavaScript analyzer), with TAJS [Jensen et al.
2009] and SAFE [Lee et al. 2012] as sound full-language points of reference. A
head-to-head is not yet apples-to-apples: those tools analyze full ECMAScript
(including `eval` and the intrinsic library) under a different soundness envelope
than our AOT whole-program dialect, and — more fundamentally — they report abstract
*value sets* at program points, not the *specialization* and *shape-monomorphism*
verdicts that are our unit of measurement, so the headline numbers do not directly
line up. A fair comparison therefore needs a translation layer: run all tools on
the shared Octane subset each admits, and map their value-set output onto our
per-function monomorphism and per-site layout metrics (and, conversely, our output
onto a common precision measure such as call-target or points-to set sizes). We
believe this is feasible and it is the single most valuable addition to the
evaluation.

> **TODO (baselines).** Run JSAI (primary) and, if the dialect gap allows, TAJS on
> the Octane subset; report (a) which benchmarks each terminates on and at what
> cost — directly testing our totality claim against a non-total analyzer — and
> (b) a common precision metric (e.g. call-target-set size per site) alongside our
> monomorphism verdict. Until then, §6.1–6.3 are self-relative (ablations against
> our own configurations), not comparative.
>
> *Fallback if the artifacts prove costly to resurrect* (JSAI is an older
> Scala/JavaScript research artifact; TAJS is Java but actively maintained): drop to
> a *paper comparison* — cite these tools' published Octane/precision numbers where
> they exist and compare qualitatively, and lean on the *totality* axis, which needs
> no shared metric (any benchmark on which a baseline diverges or exhausts memory
> while we return a bounded result is a direct, self-contained data point). This is
> weaker than a controlled run but keeps the claim honest and is a viable path if a
> head-to-head is out of scope for this submission.

### 6.5 Threats to validity

Octane is moderately sized and flavored toward JIT benchmarking, not a uniform
sample of production JavaScript; the monomorphism finding should be read as holding
*for this class of program* pending a larger corpus. Sound degradation of unbound
intrinsics over-approximates their behavior, which can only *inflate* apparent
polymorphism — so the monomorphism result is conservative in the favorable
direction. Whole-program driver synthesis may exercise call patterns a real harness
would not, or miss ones it would. Times are single-run wall-clock and indicative
only; the totality claim rests on the state bound of §5.3, not on the timings.

---

## 7. Discussion and limitations

**The strong-update ceiling.** The counting ablation (§6.3) is the clearest
statement of the analysis's main precision limitation: at `k = 0`, monovariance
prevents strong update of looped allocations through reused variables. This is not
a defect in counting but the price of context-insensitivity; it is recovered by the
two-address recency abstraction or by `k ≥ 1`. We chose single-address counting for
its unconditional soundness (no stale-pointer reconciliation) and measured the
cost; the two-address split is the obvious future extension, and the framework's
knob structure means it can be added and ablated in isolation.

**Precision knobs vs. precision cliffs.** The recurring design lesson is that a
*total* analysis wants graceful degradation, not hard failure. Every widening in
this system — the shape cap, the state cap — turns an unbounded quantity into a
tunable bound rather than a crash. The empirical payoff (§6.2) is that, for this
workload, the bound can be set aggressively low without losing monomorphism.

**What the numbers are for.** The analyzer exists to feed an AOT compiler; its
outputs (specializations and constructor shapes) are exactly the layout and
dispatch decisions the compiler must make. The monomorphism finding is therefore
not only a scientific observation but an operational one: it says the common case
the compiler should optimize for is a single specialization and a fixed layout, and
it identifies the minority of sites that need guards.

**Generality.** Nothing in the core is JavaScript-specific beyond the object
calculus and the intrinsic-degradation model; the parameterization, the totality
cap, and the knob composition apply to any language with an AAM formulation.

---

## 8. Related work

**Foundations.** Abstract interpretation [Cousot & Cousot 1977] provides the
lattice-theoretic frame — Galois connections, soundness by construction, and
widening as the general device for enforcing termination, of which our shape and
state caps are instances. Control-flow analysis for higher-order programs, and the
k-CFA family of context abstractions we parameterize over, originate with Shivers
[1991]. The k-CFA paradox — that context sensitivity is cheap for functional but
expensive for object-oriented programs — is analyzed by Might, Smaragdakis & Van
Horn [2010], and the object-sensitivity design space by Smaragdakis, Bravenboer &
Lhoták [2011]; our finding that `k = 0` suffices for function-level monomorphism on
this workload is a data point in that discussion.

**Abstracting Abstract Machines and modular interpreters.** Our core is the AAM
construction of Van Horn & Might [2010], whose store-allocation recipe we adopt
wholesale, including the CESK\* treatment of continuations. The component-swapping
architecture — and the concrete-interpreter recovery we verify is preserved through
every extension — is the Galois-transformer factoring of Darais, Might & Van Horn
[2015]; the later definitional-interpreter formulation [Darais et al. 2017] is a
related packaging of the same modularity. Where those works establish the recipe,
we report on composing the subsequent precision literature onto it as ablatable
knobs and measuring what each contributes.

**The precision diaspora.** Abstract garbage collection and abstract counting are
both due to Might & Shivers [2006]; we implement them as the `gc` and `counting`
knobs (§4.2, §4.4) and quantify their interaction — in particular the GC⊕counting
synergy (a collected address's count resets, preserving strong update for
non-escaping allocations) and the `k = 0` ceiling that bounds it. Recency
abstraction [Balakrishnan & Reps 2006] is the two-address generalization of our
single-address counting; we implement the single-address form for its
unconditional soundness and identify the two-address split as the route past our
strong-update ceiling (§7). Pushdown control-flow analysis — CFA2 [Vardoulakis &
Shivers 2010], the Abstracting Abstract Control machine [Johnson & Van Horn 2014],
and Pushdown-for-Free [Gilray et al. 2016] — recovers exact call/return matching;
we adopt P4F's caller-environment keying as the least invasive fit for a
store-allocated machine (§4.5), and report the perhaps-surprising result that on an
already-monomorphic workload it is a net cost.

**JavaScript static analysis.** TAJS [Jensen et al. 2009] and SAFE [Lee et al.
2012] are sound whole-program analyzers for full JavaScript with detailed models of
the language's coercions and builtins; WALA-based points-to analysis for JavaScript
[Sridharan et al. 2012] contributes correlation tracking for the dynamic
property-access idiom. Closest to our architecture is JSAI [Kashyap et al. 2014], a
configurable abstract interpreter for JavaScript that, like ours, exposes
sensitivity as a parameter over an AAM-style machine. We differ in three respects:
(i) the composition of the full precision diaspora — abstract GC, counting,
recency, and pushdown — as independent knobs, rather than context sensitivity
alone; (ii) the totality guarantee (§5), motivated by the AOT setting, which to our
knowledge no prior JavaScript analyzer provides as a bounded-state property; and
(iii) the type-aware hidden-class abstraction as the analysis's compiler-facing
output. Our dialect is correspondingly narrower — an AOT whole-program setting
excludes `eval` and dynamic code generation that these general analyzers must
model. A direct empirical comparison against JSAI is the most valuable open item in
our evaluation; §6.4 scopes what it requires (a metric-translation layer, since
these tools report value sets rather than specialization verdicts).

**Hidden classes and type specialization.** Maps/hidden classes originate as an
implementation technique in SELF [Chambers, Ungar & Lee 1989] and underpin
polymorphic inline caches [Hölzle, Chambers & Ungar 1991] and run-time type
feedback [Hölzle & Ungar 1994]; they remain the core object model of production JIT
engines (V8, SpiderMonkey) and of trace-based type specialization [Gal et al.
2009]. Our contribution is to lift the hidden class from a run-time, profile-driven
mechanism to a *static, type-aware* abstraction: rather than discovering shapes by
observation and guarding against change, we compute the set of shapes an allocation
site may take and report, ahead of time, which sites are monomorphic (a fixed
struct) and which require a layout guard.

---

## 9. Conclusion

Building the static-analysis engine for an AOT TypeScript compiler forces a
property most control-flow analyses treat as optional: totality on every input. We
met it not with a bespoke analysis but by assembling one from a parameterized AAM
core, composing the precision diaspora as orthogonal knobs, and adding an adaptive
context cap that bounds the state space to `locations × (cap + 1)`. The instrument
that resulted answers its motivating question sharply: real JavaScript, on the
Octane suite, is monomorphic at the function level — 353 of 353 specializations —
and stays so under the coarsening totality demands. The precision a
context-sensitive analysis spends is, for this class of program, mostly redundant;
what remains to be handled dynamically is a small, precisely-identified set of
layout-polymorphic allocation sites. The framework's knob structure turned every
design question — including the negative result that abstract counting regresses
allocation-heavy code — into a measurement, which is the disposition we most want
in an analysis meant to be trusted by a compiler.

---

## References

> First-pass bibliography — venues and years verified from memory; **double-check
> page numbers and the two entries marked (†) before submission.**

- Gogul Balakrishnan and Thomas Reps. 2006. Recency-Abstraction for Heap-Allocated
  Storage. In *Static Analysis Symposium (SAS)*. LNCS 4134, 221–239.
- Craig Chambers, David Ungar, and Elgin Lee. 1989. An Efficient Implementation of
  SELF, a Dynamically-Typed Object-Oriented Language Based on Prototypes. In
  *OOPSLA*. 49–70.
- Patrick Cousot and Radhia Cousot. 1977. Abstract Interpretation: A Unified Lattice
  Model for Static Analysis of Programs by Construction or Approximation of
  Fixpoints. In *POPL*. 238–252.
- David Darais, Matthew Might, and David Van Horn. 2015. Galois Transformers and
  Modular Abstract Interpreters: Reusable Metatheory for Program Analysis. In
  *OOPSLA*. 552–571.
- David Darais, Nicholas Labich, Phúc C. Nguyễn, and David Van Horn. 2017.
  Abstracting Definitional Interpreters (Functional Pearl). *Proc. ACM Program.
  Lang.* 1, ICFP, Article 12.
- Andreas Gal, Brendan Eich, Mike Shaver, David Anderson, David Mandelin, et al.
  2009. Trace-based Just-in-Time Type Specialization for Dynamic Languages. In
  *PLDI*. 465–478.
- Thomas Gilray, Steven Lyde, Michael D. Adams, Matthew Might, and David Van Horn.
  2016. Pushdown Control-Flow Analysis for Free. In *POPL*. 691–704.
- Urs Hölzle, Craig Chambers, and David Ungar. 1991. Optimizing Dynamically-Typed
  Object-Oriented Languages with Polymorphic Inline Caches. In *ECOOP*. LNCS 512,
  21–38.
- Urs Hölzle and David Ungar. 1994. Optimizing Dynamically-Dispatched Calls with
  Run-Time Type Feedback. In *PLDI*. 326–336.
- Simon Holm Jensen, Anders Møller, and Peter Thiemann. 2009. Type Analysis for
  JavaScript. In *Static Analysis Symposium (SAS)*. LNCS 5673, 238–255.
- J. Ian Johnson and David Van Horn. 2014. Abstracting Abstract Control. In
  *Dynamic Languages Symposium (DLS)*. 11–22.
- Vineeth Kashyap, Kyle Dewey, Ethan A. Kuefner, John Wagner, Kevin Gibbons, Jason
  Sarracino, Ben Wiedermann, and Ben Hardekopf. 2014. JSAI: A Static Analysis
  Platform for JavaScript. In *FSE*. 121–132.
- Hongki Lee, Sooncheol Won, Joonho Jin, Junhee Cho, and Sukyoung Ryu. 2012. SAFE:
  Formal Specification and Implementation of a Scalable Analysis Framework for
  ECMAScript. In *FOOL*. (†)
- Matthew Might and Olin Shivers. 2006. Improving Flow Analyses via ΓCFA: Abstract
  Garbage Collection and Counting. In *ICFP*. 13–25.
- Matthew Might, Yannis Smaragdakis, and David Van Horn. 2010. Resolving and
  Exploiting the k-CFA Paradox: Illuminating Functional vs. Object-Oriented Program
  Analysis. In *PLDI*. 305–315.
- Olin Shivers. 1991. *Control-Flow Analysis of Higher-Order Languages*. Ph.D.
  Dissertation, Carnegie Mellon University. CMU-CS-91-145.
- Yannis Smaragdakis, Martin Bravenboer, and Ondřej Lhoták. 2011. Pick Your Contexts
  Well: Understanding Object-Sensitivity. In *POPL*. 17–30.
- Manu Sridharan, Julian Dolby, Satish Chandra, Max Schäfer, and Frank Tip. 2012.
  Correlation Tracking for Points-To Analysis of JavaScript. In *ECOOP*. LNCS 7313,
  435–458.
- Dimitrios Vardoulakis and Olin Shivers. 2010. CFA2: A Context-Free Approach to
  Control-Flow Analysis. In *ESOP*. LNCS 6012, 570–589. (†journal version in
  *Logical Methods in Computer Science*, 2011)
- David Van Horn and Matthew Might. 2010. Abstracting Abstract Machines. In *ICFP*.
  51–62.
