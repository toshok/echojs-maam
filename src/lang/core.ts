/**
 * The core intermediate representation the abstract machine actually runs.
 *
 * The restricted-JS surface syntax (`ast.ts`) is normalized (`normalize.ts`)
 * into this small **A-normal form (ANF)** language: operands are always
 * *atomic* (a variable, a literal, or a lambda — evaluable with no further
 * steps), and all sequencing is made explicit with `Let`. ANF is what keeps the
 * CESK* machine small: the only control constructs that push a continuation are
 * non-tail calls.
 *
 * Every node carries a `loc` (a unique program location). `loc` is the context
 * increment fed to `tick`, so it is what k-CFA remembers — the identity of a
 * call site.
 */

/** A program location — unique per core node; the unit of context-sensitivity. */
export type Loc = number;

/** Variable / parameter name. Normalization makes all names globally unique. */
export type Name = string;

/**
 * The binding name for a function's implicit `this` receiver. `this` is a real
 * per-function parameter (as EchoJS desugars it), NOT a shared global: each
 * function that binds `this` gets its own name keyed on its lambda loc, so two
 * functions' receivers never collide on one address (which, at k=0, would merge
 * every receiver in the program into a single value — see `thisVarName` callers).
 */
export const thisVarName = (lamLoc: Loc): Name => `this$${lamLoc}`;

/**
 * Primitive literal values of the dialect, plus the degradation literal `top`:
 * "any value, no information".  `top` is not surface syntax — the normalizer
 * emits it where a value exists but cannot be modeled (unmodeled imports, rest
 * array contents), and the domains map it to their `⊤` element.
 */
export type Lit =
  | { readonly kind: "num"; readonly value: number }
  | { readonly kind: "bigint"; readonly value: bigint }
  | { readonly kind: "bool"; readonly value: boolean }
  | { readonly kind: "str"; readonly value: string }
  | { readonly kind: "null" }
  | { readonly kind: "undef" }
  | { readonly kind: "top" };

/**
 * Atomic expressions — evaluated by the machine's pure `atomEval`, never
 * stepped. `Var`, `Lit`, and `Lam` (which becomes a closure over the current
 * environment).
 */
export type AExp =
  | { readonly tag: "var"; readonly loc: Loc; readonly name: Name }
  | { readonly tag: "lit"; readonly loc: Loc; readonly lit: Lit }
  | {
      readonly tag: "lam";
      readonly loc: Loc;
      readonly params: ReadonlyArray<Name>;
      readonly body: Expr;
    };

/** Binary primitive operators supported by the dialect. */
export type BinOp =
  | "+" | "-" | "*" | "/" | "%" | "**"
  | "<" | "<=" | ">" | ">=" | "===" | "!==" | "==" | "!="
  | "&&" | "||"
  | "&" | "|" | "^" | "<<" | ">>" | ">>>"
  | "instanceof" | "in";

/**
 * Unary primitive operators. `toStr` is not surface syntax: the normalizer
 * inserts it for the implicit ToString a template literal performs on each
 * interpolated expression (its result is always string-typed).
 */
export type UnOp = "-" | "+" | "!" | "~" | "typeof" | "void" | "toStr";

/**
 * The right-hand side of a `Let`: something that produces a value to bind. Either
 * an atomic expression, a primitive application (pure, no continuation), or a
 * function call (non-tail — pushes a continuation).
 */
export type RHS =
  | { readonly tag: "atom"; readonly loc: Loc; readonly atom: AExp }
  | { readonly tag: "bin"; readonly loc: Loc; readonly op: BinOp; readonly l: AExp; readonly r: AExp }
  | { readonly tag: "un"; readonly loc: Loc; readonly op: UnOp; readonly arg: AExp }
  | { readonly tag: "call"; readonly loc: Loc; readonly fn: AExp; readonly args: ReadonlyArray<AExp> }
  // --- objects (hidden-class heap) ---
  /** Allocate a fresh object with these properties, in order (sets the initial shape). */
  | { readonly tag: "obj"; readonly loc: Loc; readonly fields: ReadonlyArray<readonly [string, AExp]> }
  /** Read property `key` from `obj`. */
  | { readonly tag: "get"; readonly loc: Loc; readonly obj: AExp; readonly key: string }
  /** Write `val` to property `key` of `obj` (transitions its shape); result is `val`. */
  | { readonly tag: "put"; readonly loc: Loc; readonly obj: AExp; readonly key: string; readonly val: AExp }
  /** Reassign an existing variable `name` to `val` (mutation); result is `val`. */
  | { readonly tag: "setVar"; readonly loc: Loc; readonly name: Name; readonly val: AExp }
  /** Allocate an array from element values (`[a, b, …]`). */
  | { readonly tag: "array"; readonly loc: Loc; readonly elems: ReadonlyArray<AExp> }
  /** Read a property under a *computed* key (`obj[keyExpr]`). */
  | { readonly tag: "getDyn"; readonly loc: Loc; readonly obj: AExp; readonly keyExpr: AExp }
  /** Write a property under a *computed* key (`obj[keyExpr] = val`); result is `val`. */
  | { readonly tag: "putDyn"; readonly loc: Loc; readonly obj: AExp; readonly keyExpr: AExp; readonly val: AExp }
  /** Enumerable property *names* of `obj` (own + inherited), as an abstract string value — for `for-in`. */
  | { readonly tag: "keys"; readonly loc: Loc; readonly obj: AExp }
  /**
   * An element `obj` yields under iteration (`for-of`, array-pattern rest): the
   * join of the element buckets of the arrays it may be. Iterating anything
   * whose elements are not tracked (an unknown value, a closure, an object with
   * no element bucket — possibly a non-array iterable) degrades to `⊤` and is
   * recorded as an unknown-call-class event.
   */
  | { readonly tag: "iterElem"; readonly loc: Loc; readonly obj: AExp }
  /** `new fn(args)`: allocate an object, run `fn` as a constructor with `this` bound to it. */
  | { readonly tag: "new"; readonly loc: Loc; readonly fn: AExp; readonly args: ReadonlyArray<AExp> }
  /** `obj.key(args)`: read the method from `obj`, call it with `this` bound to `obj`. */
  | {
      readonly tag: "method";
      readonly loc: Loc;
      readonly obj: AExp;
      readonly key: string;
      readonly args: ReadonlyArray<AExp>;
    }
  // --- prototype intrinsics (EchoJS `%objectCreate` / `%setPrototypeOf`) ---
  /** Allocate a fresh object whose prototype is `proto` (`Object.create` / `%objectCreate`). */
  | { readonly tag: "objectCreate"; readonly loc: Loc; readonly proto: AExp }
  /** Set `obj`'s prototype link to `proto` (`%setPrototypeOf`); result is `obj`. */
  | { readonly tag: "setProto"; readonly loc: Loc; readonly obj: AExp; readonly proto: AExp }
  /** Install an accessor property (getter/setter) on `obj` (`Object.defineProperty` `{get,set}`). */
  | {
      readonly tag: "defineAccessor";
      readonly loc: Loc;
      readonly obj: AExp;
      readonly key: string;
      readonly getter?: AExp;
      readonly setter?: AExp;
    }
  /**
   * Invoke `fn` with an explicit receiver (`Function.prototype.call` /
   * `%constructSuper`): runs `fn`'s body with `this` = `thisArg` and no fresh
   * allocation. This is how EchoJS lowers `super(...)` and `super.m(...)`.
   */
  | {
      readonly tag: "apply";
      readonly loc: Loc;
      readonly fn: AExp;
      readonly thisArg: AExp;
      readonly args: ReadonlyArray<AExp>;
    };

/**
 * Core expressions — the machine's "control". Each either finishes (returns an
 * atomic value to the current continuation), binds a value and continues,
 * branches, or tail-calls.
 */
export type Expr =
  | { readonly tag: "ret"; readonly loc: Loc; readonly atom: AExp }
  | { readonly tag: "let"; readonly loc: Loc; readonly name: Name; readonly rhs: RHS; readonly body: Expr }
  | {
      readonly tag: "letrec";
      readonly loc: Loc;
      readonly bindings: ReadonlyArray<{ readonly name: Name; readonly lam: AExp }>;
      readonly body: Expr;
    }
  | {
      readonly tag: "if";
      readonly loc: Loc;
      readonly cond: AExp;
      readonly then: Expr;
      readonly else: Expr;
    }
  | { readonly tag: "tailcall"; readonly loc: Loc; readonly fn: AExp; readonly args: ReadonlyArray<AExp> }
  /** `throw val` — evaluate `val`, then terminate this control path. */
  | { readonly tag: "throw"; readonly loc: Loc; readonly val: AExp }
  /** Nondeterministic control: continue as any one of `alts` (used to lower `try/catch`). */
  | { readonly tag: "nondet"; readonly loc: Loc; readonly alts: ReadonlyArray<Expr> };

// --- smart constructors (used by the normalizer and hand-written tests) -----

export const litNum = (value: number): Lit => ({ kind: "num", value });
export const litBigint = (value: bigint): Lit => ({ kind: "bigint", value });
export const litBool = (value: boolean): Lit => ({ kind: "bool", value });
export const litStr = (value: string): Lit => ({ kind: "str", value });
export const litNull: Lit = { kind: "null" };
export const litUndef: Lit = { kind: "undef" };
export const litTop: Lit = { kind: "top" };

/**
 * A monotonic source of fresh locations and names, threaded through
 * normalization so every core node and generated temporary is unique.
 */
export class Fresh {
  private locCounter = 0;
  private nameCounter = 0;
  loc(): Loc {
    return this.locCounter++;
  }
  name(base = "t"): Name {
    return `${base}$${this.nameCounter++}`;
  }
}

// --- pretty-printing (for reporting reached expressions) --------------------

export function litToString(l: Lit): string {
  switch (l.kind) {
    case "num":
      return String(l.value);
    case "bigint":
      return `${l.value}n`;
    case "bool":
      return String(l.value);
    case "str":
      return JSON.stringify(l.value);
    case "null":
      return "null";
    case "undef":
      return "undefined";
    case "top":
      return "⊤";
  }
}

export function aexpToString(a: AExp): string {
  switch (a.tag) {
    case "var":
      return a.name;
    case "lit":
      return litToString(a.lit);
    case "lam":
      return `(${a.params.join(", ")}) => …@${a.loc}`;
  }
}

export function rhsToString(r: RHS): string {
  switch (r.tag) {
    case "atom":
      return aexpToString(r.atom);
    case "bin":
      return `${aexpToString(r.l)} ${r.op} ${aexpToString(r.r)}`;
    case "un":
      return `${r.op}${aexpToString(r.arg)}`;
    case "call":
      return `${aexpToString(r.fn)}(${r.args.map(aexpToString).join(", ")})`;
    case "obj":
      return `{${r.fields.map(([k, v]) => `${k}: ${aexpToString(v)}`).join(", ")}}`;
    case "get":
      return `${aexpToString(r.obj)}.${r.key}`;
    case "put":
      return `${aexpToString(r.obj)}.${r.key} = ${aexpToString(r.val)}`;
    case "new":
      return `new ${aexpToString(r.fn)}(${r.args.map(aexpToString).join(", ")})`;
    case "method":
      return `${aexpToString(r.obj)}.${r.key}(${r.args.map(aexpToString).join(", ")})`;
    case "objectCreate":
      return `Object.create(${aexpToString(r.proto)})`;
    case "setProto":
      return `setProto(${aexpToString(r.obj)}, ${aexpToString(r.proto)})`;
    case "defineAccessor": {
      const parts = [r.getter ? "get" : "", r.setter ? "set" : ""].filter(Boolean).join("/");
      return `defineAccessor(${aexpToString(r.obj)}, ${r.key}, ${parts})`;
    }
    case "apply":
      return `${aexpToString(r.fn)}.call(${[r.thisArg, ...r.args].map(aexpToString).join(", ")})`;
    case "setVar":
      return `${r.name} = ${aexpToString(r.val)}`;
    case "array":
      return `[${r.elems.map(aexpToString).join(", ")}]`;
    case "getDyn":
      return `${aexpToString(r.obj)}[${aexpToString(r.keyExpr)}]`;
    case "putDyn":
      return `${aexpToString(r.obj)}[${aexpToString(r.keyExpr)}] = ${aexpToString(r.val)}`;
    case "keys":
      return `keys(${aexpToString(r.obj)})`;
    case "iterElem":
      return `iterElem(${aexpToString(r.obj)})`;
  }
}

export function exprToString(e: Expr): string {
  switch (e.tag) {
    case "ret":
      return `return ${aexpToString(e.atom)}`;
    case "let":
      return `let ${e.name} = ${rhsToString(e.rhs)}; …`;
    case "letrec":
      return `letrec ${e.bindings.map((b) => b.name).join(", ")}; …`;
    case "if":
      return `if (${aexpToString(e.cond)}) …`;
    case "tailcall":
      return `${aexpToString(e.fn)}(${e.args.map(aexpToString).join(", ")})`;
    case "throw":
      return `throw ${aexpToString(e.val)}`;
    case "nondet":
      return `nondet(${e.alts.length})`;
  }
}

// --- free variables (for environment trimming) ------------------------------

type Lam = Extract<AExp, { tag: "lam" }>;
const fvLamCache = new WeakMap<Lam, ReadonlySet<Name>>();

/**
 * The free variables of a lambda — the names its body references but does not
 * itself bind. Memoized per lambda node. Used to **trim** a closure's captured
 * environment to only what it can access: this both shrinks the (serialized)
 * environment keys that dominate control-state dedup and removes spurious
 * state distinctions on irrelevant bindings.
 *
 * Two structural facts shape the implementation:
 *
 * - Names are globally unique after normalization (see `Name`), so there is
 *   no shadowing and fv is simply references ∖ binders — no scope tracking.
 * - The core is a DAG, not a tree: the normalizer materializes a statement
 *   sequence's continuation once and splices it into every branch arm by
 *   reference (see normIf's `cont`), so sequential branching gives a node
 *   exponentially many root paths. The visited set makes the walk O(nodes);
 *   a tree walk here does not terminate on branch-heavy functions.
 *
 * Let-spines are walked iteratively — their length is a function's statement
 * count, far past any comfortable recursion depth.
 */
export function freeVarsOfLam(lam: Lam): ReadonlySet<Name> {
  const cached = fvLamCache.get(lam);
  if (cached) return cached;

  const refs = new Set<Name>();
  const binders = new Set<Name>();
  const visited = new WeakSet<Expr>();
  for (const p of lam.params) binders.add(p);

  const atom = (a: AExp): void => {
    switch (a.tag) {
      case "var":
        refs.add(a.name);
        return;
      case "lit":
        return;
      case "lam":
        // the nested lambda's own binders are already subtracted; what
        // it captures is a plain reference from our point of view
        for (const n of freeVarsOfLam(a)) refs.add(n);
        return;
    }
  };

  const rhs = (r: RHS): void => {
    switch (r.tag) {
      case "atom":
        return atom(r.atom);
      case "bin":
        atom(r.l);
        return atom(r.r);
      case "un":
        return atom(r.arg);
      case "call":
      case "new":
        atom(r.fn);
        r.args.forEach(atom);
        return;
      case "method":
        atom(r.obj);
        r.args.forEach(atom);
        return;
      case "apply":
        atom(r.fn);
        atom(r.thisArg);
        r.args.forEach(atom);
        return;
      case "obj":
        for (const [, v] of r.fields) atom(v);
        return;
      case "array":
        r.elems.forEach(atom);
        return;
      case "get":
      case "keys":
      case "iterElem":
        return atom(r.obj);
      case "put":
        atom(r.obj);
        return atom(r.val);
      case "getDyn":
        atom(r.obj);
        return atom(r.keyExpr);
      case "putDyn":
        atom(r.obj);
        atom(r.keyExpr);
        return atom(r.val);
      case "setVar":
        refs.add(r.name); // a reassignment references the variable
        return atom(r.val);
      case "objectCreate":
        return atom(r.proto);
      case "setProto":
        atom(r.obj);
        return atom(r.proto);
      case "defineAccessor":
        atom(r.obj);
        if (r.getter) atom(r.getter);
        if (r.setter) atom(r.setter);
        return;
    }
  };

  const walk = (e0: Expr): void => {
    let e = e0;
    // iterative over let-spines; the visited check doubles as the DAG
    // sharing cutoff and the guard against re-entering a shared spine
    while (true) {
      if (visited.has(e)) return;
      visited.add(e);
      switch (e.tag) {
        case "let":
          binders.add(e.name);
          rhs(e.rhs);
          e = e.body;
          continue;
        case "ret":
          return atom(e.atom);
        case "letrec":
          for (const b of e.bindings) binders.add(b.name);
          for (const b of e.bindings) atom(b.lam);
          e = e.body;
          continue;
        case "if":
          atom(e.cond);
          walk(e.then);
          e = e.else;
          continue;
        case "tailcall":
          atom(e.fn);
          e.args.forEach(atom);
          return;
        case "throw":
          return atom(e.val);
        case "nondet": {
          const alts = e.alts;
          for (let i = 0; i + 1 < alts.length; i++) walk(alts[i]!);
          if (alts.length === 0) return;
          e = alts[alts.length - 1]!;
          continue;
        }
      }
    }
  };

  walk(lam.body);
  for (const b of binders) refs.delete(b);
  fvLamCache.set(lam, refs);
  return refs;
}
