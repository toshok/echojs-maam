/**
 * Normalization: restricted-JS **ESTree** → ANF core IR.
 *
 * A classic CPS-style A-normalizer (Flanagan et al.): it names every
 * intermediate result, threads a continuation, and produces the small
 * {@link Expr} core the machine steps. Along the way it
 *
 *  - **alpha-renames** every binding to a globally-unique name, so distinct
 *    source variables never collide at the same abstract address;
 *  - **hoists** function declarations into a `letrec` per scope (JS function-
 *    declaration hoisting), which is also what enables mutual recursion;
 *  - compiles `return f(x)` as a **tail call**, and short-circuiting `&&`/`||`
 *    and `?:` into core `if`s that share their continuation.
 *
 * Anything outside the analyzable core — objects/member access, `new`,
 * assignment, loops, `with`, loose equality, spreads, destructuring — raises a
 * {@link NormalizeError} naming the offending construct.
 */

import type {
  ArrowFunctionExpression,
  BlockStatement,
  CallExpression,
  CatchClause,
  Expression as EExpr,
  FunctionDeclaration,
  FunctionExpression,
  Identifier,
  ModuleDeclaration,
  Node,
  Pattern,
  Program,
  Span,
  Statement,
} from "./ast.js";
import { spanOf } from "./ast.js";

/** A top-level item: an ordinary statement or an ES module declaration. */
type Stmt = Statement | ModuleDeclaration;
import type { AExp, BinOp, Expr, ImportSummary, Lit, Loc, Name, RHS, UnOp } from "./core.js";
import { Fresh, litBigint, litBool, litNull, litNum, litStr, litSummary, litTop, litUndef, thisVarName } from "./core.js";

export class NormalizeError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "NormalizeError";
  }
}

/** Lexical scope: source name → unique core name. */
type Scope = ReadonlyMap<string, Name>;

/**
 * EchoJS/old-esprima function extras: a `defaults` array parallel to `params`
 * (`null` for params without a default) and a trailing `rest` identifier.
 * Standard ESTree functions simply have neither field.
 */
interface OldFunctionDialect {
  readonly defaults?: ReadonlyArray<EExpr | null> | null;
  readonly rest?: Identifier | null;
}

/** Source info about a lambda, keyed by its core `loc` (for constructor reports). */
export interface LambdaInfo {
  readonly name?: string;
  readonly span: Span;
}

/**
 * A binding the normalizer could not model precisely and bound to a degraded
 * value instead (e.g. an old-esprima rest parameter). Surfaced through
 * `AnalysisResult.warnings()` and `metrics.degradedBindings` so a degraded run
 * is never mistaken for a closed-world one.
 */
export interface DegradedBinding {
  readonly name: string;
  readonly reason: string;
  readonly span?: Span;
}

/** Owner id for top-level code (not inside any function). */
export const TOPLEVEL: Loc = -1;

/**
 * Host hooks into normalization.  `importValue` is cross-module linking
 * (docs/cross-module-summaries.md): given an ImportDeclaration's source
 * specifier (verbatim — the HOST resolves it, since module resolution is
 * the host's) and the imported export name (`"default"` for a default
 * import), return the exporting module's {@link ImportSummary} for that
 * binding, or `undefined` when none exists.  A miss binds `⊤` and records
 * a degraded binding — exactly the hook-less behavior — so correctness
 * never depends on the host's registry being complete.
 */
export interface ImportHooks {
  importValue?(source: string, imported: string): ImportSummary | undefined;
}

/** Options for {@link normalizeProgram} beyond the hooks. */
export interface NormalizeOptions {
  /**
   * Inject the EXPORT HARNESS: after the real toplevel, a `letrec`
   * nondeterministic LOOP that calls every syntactically-function export
   * with `⊤` arguments and re-enters itself.  Its fixpoint over-approximates
   * every external call sequence — repetition included, which a single
   * straight-line ⊤-call would NOT (module state like `count++` needs the
   * ascent) — so the harness call results (`exportResultNames`) are sound
   * ⊤-argument result summaries.  The harness also joins ⊤ into exported
   * functions' parameters, so a harness run's node types are WIDER than the
   * plain run's: use a separate plain analysis for the type oracle.
   */
  readonly exportHarness?: boolean;
}

/** A syntactically-function export: the harness knows its arity statically. */
interface FnExport {
  readonly exportName: string;
  readonly localName: string;
  readonly arity: number;
}

/**
 * The exports whose FUNCTION-ness is syntactically evident: exported
 * function declarations, exported `const f = function/arrow`, export
 * specifiers naming such toplevel declarations, and a NAMED default
 * function.  (An export whose function-ness is only semantic — `export
 * const f = compose(g, h)` — is not harnessed and gets no result summary.)
 */
export function collectFnExports(body: ReadonlyArray<Node>): FnExport[] {
  const fnDecls = new Map<string, number>();
  const declFromStmt = (s: Node): void => {
    const st = s as { type?: string } & Record<string, unknown>;
    if (st.type === "FunctionDeclaration") {
      const d = s as FunctionDeclaration;
      if (d.id) fnDecls.set(d.id.name, d.params.length);
    } else if (st.type === "VariableDeclaration") {
      const decls = (st.declarations as Array<{ id?: { type?: string; name?: string }; init?: { type?: string; params?: unknown[] } }>) ?? [];
      for (const d of decls) {
        if (
          d.id?.type === "Identifier" &&
          d.id.name !== undefined &&
          d.init &&
          (d.init.type === "FunctionExpression" || d.init.type === "ArrowFunctionExpression")
        )
          fnDecls.set(d.id.name, (d.init.params ?? []).length);
      }
    }
  };
  for (const s of body) {
    const st = s as { type?: string; declaration?: Node | null };
    if (st.type === "ExportNamedDeclaration" && st.declaration) declFromStmt(st.declaration);
    else declFromStmt(s);
  }
  const out: FnExport[] = [];
  const seen = new Set<string>();
  const add = (exportName: string, localName: string): void => {
    const arity = fnDecls.get(localName);
    if (arity === undefined || seen.has(exportName)) return;
    seen.add(exportName);
    out.push({ exportName, localName, arity });
  };
  for (const s of body) {
    const st = s as {
      type?: string;
      declaration?: Node | null;
      specifiers?: Array<{ local: { name: string }; exported: { name: string } }>;
      source?: unknown;
    };
    if (st.type === "ExportNamedDeclaration") {
      if (st.declaration) {
        const d = st.declaration as { type?: string; id?: { name?: string }; declarations?: Array<{ id?: { type?: string; name?: string } }> };
        if (d.type === "FunctionDeclaration" && d.id?.name !== undefined) add(d.id.name, d.id.name);
        else if (d.type === "VariableDeclaration")
          for (const dd of d.declarations ?? [])
            if (dd.id?.type === "Identifier" && dd.id.name !== undefined) add(dd.id.name, dd.id.name);
      } else if (!st.source) {
        for (const spec of st.specifiers ?? []) add(spec.exported.name, spec.local.name);
      }
    } else if (st.type === "ExportDefaultDeclaration") {
      const d = (s as { declaration?: { type?: string; id?: { name?: string } | null } }).declaration;
      if (d && d.type === "FunctionDeclaration" && d.id?.name !== undefined) add("default", d.id.name);
    }
  }
  return out;
}

/** Normalize a whole program to a single core expression. */
export function normalizeProgram(
  program: Program,
  hooks?: ImportHooks,
  opts?: NormalizeOptions,
): {
  core: Expr;
  fresh: Fresh;
  /** Object allocation-site / `new`-site location → its source span. */
  siteSpans: Map<Loc, Span>;
  /** Lambda core-loc → its source name/span. */
  lambdaInfo: Map<Loc, LambdaInfo>;
  /** `ret` expression loc → the lambda loc that owns it (`TOPLEVEL` for main). */
  retOwner: Map<Loc, Loc>;
  /** Lambda loc → its source parameter names (for the specialization report). */
  lambdaParams: Map<Loc, ReadonlyArray<string>>;
  /** Bindings bound to a degraded value (imprecisely modeled constructs). */
  degradedBindings: ReadonlyArray<DegradedBinding>;
  /** Source node → core name holding its value (see Normalizer.nodeNames). */
  nodeNames: ReadonlyMap<Node, Name>;
  /**
   * The toplevel lexical scope at the end of the program: source name →
   * unique core name.  The export side of cross-module linking — this is
   * where `summarizeBinding` finds an exported binding's core identity.  A
   * source name whose final unique name differs across toplevel control
   * paths is omitted (ambiguous — no summary rather than a wrong one).
   */
  toplevelScope: ReadonlyMap<string, Name>;
  /** How many import bindings were bound from a host-supplied summary. */
  summaryBindings: number;
  /** Checked-tier import sites: synthetic loc → import label + declared shape. */
  importShapeSites: ReadonlyMap<Loc, { label: string; fields: ReadonlyArray<{ name: string; sig: string }> }>;
  /**
   * Export-harness result bindings: export name → the core names its
   * ⊤-argument harness call results bind to (one per harness copy — a
   * branching toplevel materializes the shared final continuation more than
   * once; extraction joins across all of them).  Empty without
   * {@link NormalizeOptions.exportHarness}.
   */
  exportResultNames: ReadonlyMap<string, ReadonlyArray<Name>>;
} {
  const fresh = new Fresh();
  const n = new Normalizer(fresh, hooks);
  // Empty statements are no-ops; drop them so a trailing `;` doesn't hide the
  // program's result-bearing final expression statement.
  const body = program.body.filter(isStatement).filter((s) => s.type !== "EmptyStatement");
  // The final continuation records the toplevel scope it is built with.  It
  // can run more than once (a shared continuation spliced into several
  // branch arms); entries that disagree between runs are ambiguous.
  const toplevel = new Map<string, Name>();
  const ambiguous = new Set<string>();
  const recordToplevel = (scope: Scope): void => {
    for (const [src, unique] of scope) {
      const prev = toplevel.get(src);
      if (prev === undefined) toplevel.set(src, unique);
      else if (prev !== unique) ambiguous.add(src);
    }
  };
  // The export harness (see NormalizeOptions.exportHarness): appended to
  // every materialization of the final continuation so no completion path
  // escapes it.
  const fnExports = opts?.exportHarness === true ? collectFnExports(program.body) : [];
  const exportResultNames = new Map<string, Name[]>();
  const withHarness = (scope: Scope, completion: Expr): Expr => {
    if (fnExports.length === 0) return completion;
    const harnessName = fresh.name("exharness");
    const arms: Expr[] = [];
    for (const fe of fnExports) {
      const unique = scope.get(fe.localName);
      if (unique === undefined) continue;
      const resName = fresh.name("exres");
      const names = exportResultNames.get(fe.exportName);
      if (names) names.push(resName);
      else exportResultNames.set(fe.exportName, [resName]);
      const args: AExp[] = [];
      for (let i = 0; i < fe.arity; i++) args.push(n.litA(litTop));
      arms.push(
        n.letE(
          resName,
          { tag: "call", loc: fresh.loc(), fn: n.varA(unique), args },
          { tag: "tailcall", loc: fresh.loc(), fn: n.varA(harnessName), args: [] },
        ),
      );
    }
    if (arms.length === 0) return completion;
    const harnessBody: Expr = arms.length === 1 ? arms[0]! : { tag: "nondet", loc: fresh.loc(), alts: arms };
    return {
      tag: "letrec",
      loc: fresh.loc(),
      bindings: [{ name: harnessName, lam: n.lamA([], harnessBody) }],
      body: {
        tag: "nondet",
        loc: fresh.loc(),
        alts: [completion, { tag: "tailcall", loc: fresh.loc(), fn: n.varA(harnessName), args: [] }],
      },
    };
  };
  // The program's "result" is the value of a trailing expression statement, if
  // any; otherwise the program yields `undefined`.
  const last = body[body.length - 1];
  let core: Expr;
  if (last && last.type === "ExpressionStatement") {
    const init = body.slice(0, -1);
    core = n.normStmts(init, new Map(), (scope) => {
      recordToplevel(scope);
      return withHarness(scope, n.normAtom(last.expression, scope, (a) => n.retE(a)));
    });
  } else {
    core = n.normStmts(body, new Map(), (scope) => {
      recordToplevel(scope);
      return withHarness(scope, n.retE(n.litA(litUndef)));
    });
  }
  for (const name of ambiguous) toplevel.delete(name);
  return {
    core,
    fresh,
    siteSpans: n.siteSpans,
    lambdaInfo: n.lambdaInfo,
    retOwner: n.retOwner,
    lambdaParams: n.lambdaParams,
    degradedBindings: n.degradedBindings,
    nodeNames: n.nodeNames,
    toplevelScope: toplevel,
    summaryBindings: n.summaryBindings,
    importShapeSites: n.importShapeSites,
    exportResultNames,
  };
}

function isStatement(n: Node): n is Stmt {
  // Top-level items are statements or module declarations; the normalizer
  // handles both. Anything genuinely odd is caught when we normalize it.
  return typeof (n as { type?: unknown }).type === "string";
}

class Normalizer {
  /** Object/`new` allocation-site loc → source span, filled in during lowering. */
  readonly siteSpans = new Map<Loc, Span>();
  /** Lambda core-loc → source name/span. */
  readonly lambdaInfo = new Map<Loc, LambdaInfo>();
  /** `ret` expression loc → owning lambda loc. */
  readonly retOwner = new Map<Loc, Loc>();
  /** Lambda loc → source parameter names. */
  readonly lambdaParams = new Map<Loc, ReadonlyArray<string>>();
  /** Bindings bound to a degraded value (imprecisely modeled constructs). */
  readonly degradedBindings: DegradedBinding[] = [];
  /**
   * Source node → the core {@link Name} that holds the node's value — the raw
   * material of the node-identity type oracle (`AnalysisResult.typeOfNode`).
   *
   * Mapping policy:
   *  - an EXPRESSION node maps to the name its value is bound to: the declared
   *    variable when normalization binds it directly (`normNamed`), otherwise
   *    the ANF temporary minted for it (`normAtom` — a `var` atom result);
   *  - a DECLARATION Identifier (variable declarator, parameter, pattern leaf,
   *    catch param, import specifier local, function name, for-in/for-of loop
   *    variable, rest target) maps to its alpha-renamed binding;
   *  - GLUE stays unmapped: plain literals (no binding — but a REGEX literal
   *    IS mapped: it allocates an object held in a temp), lambda atoms,
   *    template concat/toStr intermediates, loop/join scaffolding, and
   *    temporaries internal to intrinsic lowerings;
   *  - UNBOUND identifier reads (free/global names) are unmapped — they have
   *    no store binding, and mapping their raw source name could alias a
   *    fresh-minted core name;
   *  - a for-in/for-of head that REUSES a pre-declared variable (the `setVar`
   *    form) maps nothing; only declaration-form heads map the loop variable.
   * The first mapping for a node wins (a `var x = e` maps `e` to `x`, not to
   * the temp a nested lowering may also produce). Identity-keyed: the exact
   * node object, never structural.
   */
  readonly nodeNames = new Map<Node, Name>();
  /** The lambda currently being compiled (`TOPLEVEL` at the program level). */
  private currentOwner: Loc = TOPLEVEL;
  /**
   * The lambda whose `this` is in scope. Unlike {@link currentOwner}, arrow
   * functions do NOT update this — an arrow captures the enclosing function's
   * `this` lexically, so `this` inside it names the enclosing binding.
   */
  private currentThisOwner: Loc = TOPLEVEL;
  /** Enclosing loops, innermost last — targets for `break`/`continue`. */
  private readonly loopStack: Array<{ onBreak: () => Expr; onContinue: () => Expr }> = [];

  /** Count of import bindings bound from a host-supplied summary. */
  summaryBindings = 0;
  /**
   * Checked-tier import allocation sites: the synthetic `shapedTop` loc →
   * the import it stands for (`source#exportName`) and its declared shape.
   * The analysis compares each site's FINAL heap state against the
   * declaration to report which imported objects this module mutates
   * (`AnalysisResult.mutatedImports`).
   */
  readonly importShapeSites = new Map<Loc, { label: string; fields: ReadonlyArray<{ name: string; sig: string }> }>();

  constructor(
    private readonly fresh: Fresh,
    private readonly hooks?: ImportHooks,
  ) {}

  /** Per-function hoist-scan ref sets, memoized on node identity
   * (functionSubtreeRefs — pure per subtree; enclosing lists re-query
   * the same fn nodes once per statement position). */
  private readonly fnRefsMemo = new Map<AnyNode, ReadonlySet<string>>();
  /** Nodes spliced into multiple binding sites — poisoned, never reported. */
  private readonly poisonedNodes = new Set<Node>();
  /** Nodes whose mapping came from `normNamed` and still owes its inner lowering one alias. */
  private readonly pendingInitAlias = new Set<Node>();

  /**
   * Record that `node`'s value is held by core name `name`.
   *
   *  - Benign duplicate (same node, same name): first mapping wins.
   *  - The `normNamed` → `normAtom` ALIAS PAIR is expected: `var y = x` maps
   *    the initializer node to `y` (fromInit) and its inner lowering then
   *    reports the read's own name — two correct names for ONE occurrence.
   *    The init mapping is kept and exactly one such alias is absorbed.
   *  - Any OTHER different-name remap means a shared node object spliced into
   *    several sites (EchoJS's `common-ids` singleton identifiers do exactly
   *    this): any single answer would be silently wrong for the other sites,
   *    so the node is evicted and POISONED — the oracle reports `undefined`
   *    and the consumer degrades soundly.
   */
  private mapNode(node: Node, name: Name, fromInit = false): void {
    if (this.poisonedNodes.has(node)) return;
    const existing = this.nodeNames.get(node);
    if (existing === undefined) {
      this.nodeNames.set(node, name);
      if (fromInit) this.pendingInitAlias.add(node);
      return;
    }
    if (existing === name) return;
    if (!fromInit && this.pendingInitAlias.has(node)) {
      this.pendingInitAlias.delete(node); // the one expected alias — absorbed
      return;
    }
    this.nodeNames.delete(node);
    this.pendingInitAlias.delete(node);
    this.poisonedNodes.add(node);
  }

  // --- core constructors (each mints a fresh location) ---------------------

  varA(name: Name): AExp {
    return { tag: "var", loc: this.fresh.loc(), name };
  }
  litA(lit: Lit): AExp {
    return { tag: "lit", loc: this.fresh.loc(), lit };
  }
  lamA(params: ReadonlyArray<Name>, body: Expr): AExp {
    return { tag: "lam", loc: this.fresh.loc(), params, body };
  }
  retE(atom: AExp): Expr {
    const loc = this.fresh.loc();
    this.retOwner.set(loc, this.currentOwner); // attribute this return to its function
    return { tag: "ret", loc, atom };
  }
  letE(name: Name, rhs: RHS, body: Expr): Expr {
    return { tag: "let", loc: this.fresh.loc(), name, rhs, body };
  }
  ifE(cond: AExp, then: Expr, els: Expr): Expr {
    return { tag: "if", loc: this.fresh.loc(), cond, then, else: els };
  }
  tailE(fn: AExp, args: ReadonlyArray<AExp>): Expr {
    return { tag: "tailcall", loc: this.fresh.loc(), fn, args };
  }

  // --- statements ----------------------------------------------------------

  /**
   * Compile a statement list. `k` receives the scope in force at the *end* of the
   * list and returns the continuation expression. Function declarations in the
   * list are hoisted into a leading `letrec`.
   */
  normStmts(stmts: ReadonlyArray<Stmt>, scope: Scope, k: (scope: Scope) => Expr): Expr {
    // Import bindings are HOISTED by spec: they exist (and are initialized —
    // the exporting module runs first) before any statement of this module.
    // Bind them ABOVE everything else, so hoisted function declarations'
    // closures capture the import addresses; a hoisted function that
    // references an import would otherwise read `⊥` (free variable), and
    // summaries would never reach function bodies — which is where imports
    // are actually used.
    const imports = stmts.filter((s) => s.type === "ImportDeclaration");
    if (imports.length > 0 && imports.length !== stmts.length) {
      const others = stmts.filter((s) => s.type !== "ImportDeclaration");
      return this.normStmts(imports, scope, (sc) => this.normStmts(others, sc, k));
    }
    const allFuncs = stmts.filter((s): s is FunctionDeclaration => s.type === "FunctionDeclaration");
    // async/generator functions are not modeled: their name binds ⊤ (a call
    // then degrades as an unknown call), their body is never compiled, and
    // the degradation is VISIBLE — never a silently-sync mis-model (an async
    // call really returns a Promise, not the body's return value).
    const funcs = allFuncs.filter((f) => !unmodeledFnKind(f));
    const degradedFuncs = allFuncs.filter((f) => unmodeledFnKind(f));
    const rest = stmts.filter((s) => s.type !== "FunctionDeclaration");

    let scope1: Scope = scope;
    if (funcs.length > 0 || degradedFuncs.length > 0) {
      const m = new Map(scope);
      for (const f of funcs) m.set(fnName(f), this.fresh.name(fnName(f)));
      for (const f of degradedFuncs) m.set(fnName(f), this.fresh.name(fnName(f)));
      scope1 = m;
    }
    for (const f of degradedFuncs) {
      if (f.id) this.mapNode(f.id, scope1.get(fnName(f))!);
      this.degradedBindings.push({
        name: fnName(f),
        reason: `${unmodeledFnKind(f)} functions are not modeled; the binding holds ⊤`,
        span: spanOf(f),
      });
    }

    // JS hoisting (differential-harness finding, extended per adversarial
    // review): a closure created textually AT OR BEFORE a variable's
    // declaration in the same list — a hoisted function declaration, or a
    // function expression / arrow / object-literal method in an earlier (or
    // the same) statement — may reference that variable. Compiling it against
    // the incremental scope left the name un-renamed, so the closure's
    // reads/writes silently missed the real binding (writes were DROPPED: an
    // oracle unsoundness, e.g. `var f = function () { n = "x"; }; var n = 0;
    // f(); n;` reported num). Model the hoisted binding faithfully: detect
    // capture with a syntactic, over-approximate scan (functionSubtreeRefs),
    // mint the captured names' uniques up front, pre-bind them to `undefined`
    // ABOVE everything (so closures capture the address), and have their
    // declaration statements ASSIGN (`setVar`) instead of re-binding (a
    // re-`let` after a call/loop would mint a different address under the
    // machine's (name, time) addressing and split the variable).
    //
    // Positional: a name declared at statement j takes the hoisted path only
    // if some function subtree at statement i ≤ j (hoisted declarations count
    // as i = −1) references it. Declare-then-capture shapes (i > j) already
    // work through ordinary scoping and keep the precise fresh-`let` path, so
    // their nodeTypes joins never widen with the pre-binding's `undefined`.
    //
    // Not modeled, kept VISIBLE instead (degradedBindings — the harness
    // precondition trips and the file SKIPs): `var` hoisting out of NESTED
    // blocks into this scope when a function here captures the name, and
    // destructuring-pattern LEAVES captured at-or-before their declaration
    // (review R1). Re-declared (`var x` twice) captures ARE modeled: both
    // declarations assign the one pre-minted binding. Phase 3.5 results note
    // tracks the rest.
    // Per-name declaration records for this list. A name may be declared by
    // identifier declarators, by destructuring-pattern leaves, or (degenerate
    // but legal) by both; every closure reference position matters, so record
    // ALL indexes per kind.
    type DeclRec = { idxs: number[]; at: Stmt };
    const idDecls = new Map<string, DeclRec>();
    const patDecls = new Map<string, DeclRec>();
    rest.forEach((s, j) => {
      if (s.type !== "VariableDeclaration") return;
      for (const d of s.declarations) {
        if (d.id.type === "Identifier") {
          const n = d.id.name;
          if (funcs.some((f) => fnName(f) === n)) continue;
          const rec = idDecls.get(n) ?? { idxs: [], at: s };
          rec.idxs.push(j);
          idDecls.set(n, rec);
        } else if (d.id.type === "ObjectPattern" || d.id.type === "ArrayPattern") {
          for (const n of patternNames(d.id)) {
            const rec = patDecls.get(n) ?? { idxs: [], at: s };
            rec.idxs.push(j);
            patDecls.set(n, rec);
          }
        }
      }
    });

    const hoistedFuncRefs = new Set<string>();
    for (const f of funcs) functionSubtreeRefs(f as unknown as AnyNode, hoistedFuncRefs, this.fnRefsMemo);
    // Earliest closure-reference position per name (hoisted declarations count
    // as −1; `∃ ref ≤ X` ⟺ `min(refs) ≤ X`, so the minimum suffices).
    const minRef = new Map<string, number>();
    for (const n of hoistedFuncRefs) minRef.set(n, -1);
    rest.forEach((s, i) => {
      const refs = new Set<string>();
      functionSubtreeRefs(s as unknown as AnyNode, refs, this.fnRefsMemo);
      for (const n of refs) if (!minRef.has(n)) minRef.set(n, i);
    });

    // The MODELED case: an identifier-declared name whose earliest closure
    // reference is at-or-before its FIRST declaration takes the pre-bind +
    // setVar path — correct even under re-declaration (every identifier
    // declaration assigns the one pre-minted binding).
    const captured = new Set<string>();
    for (const [n, i] of minRef) {
      const id = idDecls.get(n);
      if (id && i <= id.idxs[0]!) captured.add(n);
    }

    // VISIBLE degradation for the binding-SPLIT shapes the modeled path does
    // not cover (review R1 + round-4 residual). ACCOUNTING ONLY — binding
    // behavior is untouched; what is banned is a silent wrong answer. A split
    // happens whenever some later declaration re-binds a name a closure
    // already captured:
    //  - a pattern leaf declared at-or-after a closure reference (bindPattern
    //    always fresh-binds; the closure writes the older binding);
    //  - a pattern re-declaration of a hoisted-captured name (the closure and
    //    the identifier declarations share the pre-minted binding, the
    //    pattern splits off a fresh one) — the round-4 reviewer repro;
    //  - an identifier re-declaration AFTER a closure capture that was not
    //    hoisted-modeled (the closure holds the first binding, the re-`let`
    //    mints a second) — the same class, identifier-only.
    // All-refs-after-all-declarations shapes are consistent (the closure sees
    // the final binding, and so does every later statement): no degradation.
    for (const [n, i] of minRef) {
      const id = idDecls.get(n);
      const pat = patDecls.get(n);
      if (!id && !pat) continue;
      const lastIdx = Math.max(id ? id.idxs[id.idxs.length - 1]! : -1, pat ? pat.idxs[pat.idxs.length - 1]! : -1);
      let reason: string | null = null;
      if (pat && captured.has(n)) {
        reason =
          "destructuring-pattern re-declaration of a hoisted-captured variable splits the binding (the closure and identifier declarations share the pre-minted binding; the pattern fresh-binds) — not modeled; without this accounting the closure's writes would be silently lost";
      } else if (pat && i <= lastIdx) {
        reason =
          "destructuring-pattern binding captured by a closure created at-or-before its declaration — hoisted pattern-leaf capture is not modeled; without this accounting the closure's writes would be silently lost";
      } else if (!pat && id && !captured.has(n) && i <= lastIdx) {
        reason =
          "identifier re-declaration after a closure capture splits the binding (the closure holds the earlier binding; the re-declaration mints a fresh one) — not modeled; without this accounting the closure's writes would be silently lost";
      }
      if (reason) this.degradedBindings.push({ name: n, reason, span: spanOf((pat ?? id)!.at) });
    }
    const allFuncRefs = new Set<string>(minRef.keys());

    // Function-scope hoisting we do NOT model: a `var` declared in a nested
    // block whose name a function in this list captures. Count it (visible
    // degradation — the differential harness's skip precondition), instead of
    // silently computing on a ⊥ binding.
    if (allFuncRefs.size > 0) {
      const nested = new Map<string, AnyNode>();
      for (const s of rest) {
        if (s.type === "VariableDeclaration") continue; // list-level: modeled above
        nestedVarNames(s as unknown as AnyNode, nested);
      }
      for (const [n, at] of nested) {
        if (allFuncRefs.has(n) && !idDecls.has(n) && !patDecls.has(n)) {
          this.degradedBindings.push({
            name: n,
            reason:
              "nested-block `var` captured by a function in the enclosing scope — function-scope hoisting out of blocks is not modeled; the binding reads as ⊥",
            span: spanOf(at as unknown as Node),
          });
        }
      }
    }

    // the ⊤ bindings for unmodeled (async/generator) function declarations,
    // wrapped around whatever this list compiles to
    const wrapDegraded = (body: Expr): Expr => {
      let out = body;
      for (const f of [...degradedFuncs].reverse()) {
        out = this.letE(
          scope1.get(fnName(f))!,
          { tag: "atom", loc: this.fresh.loc(), atom: this.litA(litTop) },
          out,
        );
      }
      return out;
    };

    if (funcs.length === 0 && captured.size === 0) return wrapDegraded(this.normStmtSeq(rest, scope1, k));

    const hoisted = new Map<string, Name>();
    const scopeBody = new Map(scope1);
    for (const [src] of idDecls) {
      if (captured.has(src)) {
        const u = this.fresh.name(src);
        hoisted.set(src, u);
        scopeBody.set(src, u);
      }
    }

    const bindings = funcs.map((f) => {
      const unique = scope1.get(fnName(f))!;
      if (f.id) this.mapNode(f.id, unique);
      return {
        name: unique,
        lam: this.compileFunction(f.params, f.body, scopeBody, { name: fnName(f), span: spanOf(f) }, false, f as OldFunctionDialect),
      };
    });

    const bodyExpr = this.normStmtSeq(rest, scopeBody, k, hoisted.size > 0 ? hoisted : undefined);
    let out: Expr =
      funcs.length > 0 ? { tag: "letrec", loc: this.fresh.loc(), bindings, body: bodyExpr } : bodyExpr;
    for (const u of [...hoisted.values()].reverse()) {
      out = this.letE(u, { tag: "atom", loc: this.fresh.loc(), atom: this.litA(litUndef) }, out);
    }
    return wrapDegraded(out);
  }

  private normStmtSeq(stmts: ReadonlyArray<Stmt>, scope: Scope, k: (scope: Scope) => Expr, hoisted?: ReadonlyMap<string, Name>): Expr {
    if (stmts.length === 0) return k(scope);
    const [head, ...tail] = stmts;
    return this.normStmt(head!, scope, (scope2) => this.normStmtSeq(tail, scope2, k, hoisted), hoisted);
  }

  private normStmt(s: Stmt, scope: Scope, k: (scope: Scope) => Expr, hoisted?: ReadonlyMap<string, Name>): Expr {
    switch (s.type) {
      case "VariableDeclaration": {
        // `const a = …, b = …;` ⇒ sequential bindings, left to right.
        const decls = s.declarations;
        const go = (i: number, sc: Scope): Expr => {
          if (i >= decls.length) return k(sc);
          const d = decls[i]!;
          if (d.id.type !== "Identifier") {
            // Destructuring declaration: bind the initializer to a temp, then
            // decompose the pattern into property/element reads.
            if (d.id.type !== "ObjectPattern" && d.id.type !== "ArrayPattern")
              throw new NormalizeError("destructuring patterns are not supported; use a plain name.");
            if (d.init === null || d.init === undefined)
              throw new NormalizeError("a destructuring declaration requires an initializer.");
            const sc2 = new Map(sc);
            for (const n of patternNames(d.id)) sc2.set(n, this.fresh.name(n));
            const tmp = this.fresh.name("destr");
            const cont = go(i + 1, sc2);
            return this.normNamed(d.init, sc, tmp, this.bindPattern(d.id, this.varA(tmp), sc2, cont));
          }
          const src = d.id.name;
          // A captured-by-hoisted-function name: its binding was pre-created
          // above the letrec — this declaration ASSIGNS it (see normStmts).
          const pre = hoisted?.get(src);
          if (pre !== undefined) {
            this.mapNode(d.id, pre);
            const sc2 = new Map(sc).set(src, pre);
            const cont = go(i + 1, sc2);
            if (d.init === null || d.init === undefined) return cont; // already `undefined`
            const tmp = this.fresh.name(src);
            return this.normNamed(
              d.init,
              sc,
              tmp,
              this.letE(this.fresh.name(), { tag: "setVar", loc: this.fresh.loc(), name: pre, val: this.varA(tmp) }, cont),
            );
          }
          const unique = this.fresh.name(src);
          this.mapNode(d.id, unique);
          const sc2 = new Map(sc).set(src, unique);
          const cont = go(i + 1, sc2);
          return d.init === null || d.init === undefined
            ? this.letE(unique, { tag: "atom", loc: this.fresh.loc(), atom: this.litA(litUndef) }, cont)
            : this.normNamed(d.init, sc, unique, cont);
        };
        return go(0, scope);
      }
      case "ReturnStatement": {
        if (!s.argument) return this.retE(this.litA(litUndef));
        const arg = s.argument;
        if (arg.type === "CallExpression") {
          // A `%intrinsic(...)` in return position is not a real callee: route
          // it through `normAtom` so `tryIntrinsic` lowers (or degrades) it,
          // instead of emitting a tail call to an unbound `%name`. A scope-bound
          // `%`-name (e.g. a `%super` parameter) stays an ordinary tail call.
          if (arg.callee.type === "Identifier" && arg.callee.name.startsWith("%") && !scope.has(arg.callee.name))
            return this.normAtom(arg, scope, (a) => this.retE(a));
          if (arg.callee.type !== "Identifier" && arg.callee.type !== "FunctionExpression" &&
              arg.callee.type !== "ArrowFunctionExpression")
            return this.normAtom(arg, scope, (a) => this.retE(a)); // fall back (may error inside)
          return this.normAtom(arg.callee as EExpr, scope, (fn) =>
            this.normArgs(arg.arguments, scope, (as) => this.tailE(fn, as)),
          );
        }
        return this.normAtom(arg, scope, (a) => this.retE(a));
      }
      case "IfStatement": {
        const cont = k(scope);
        return this.normAtom(s.test, scope, (tv) => {
          const then = this.normStmt(s.consequent, scope, () => cont);
          const els = s.alternate ? this.normStmt(s.alternate, scope, () => cont) : cont;
          return this.ifE(tv, then, els);
        });
      }
      case "ExpressionStatement":
        return this.normAtom(s.expression, scope, () => k(scope));
      case "BlockStatement":
        return this.normStmts(s.body, scope, () => k(scope));
      case "FunctionDeclaration":
        return this.normStmts([s], scope, k);
      case "EmptyStatement":
        return k(scope);
      case "WhileStatement":
        return this.normWhile(s.test, s.body, scope, k);
      case "DoWhileStatement":
        return this.normDoWhile(s.test, s.body, scope, k);
      case "ForStatement":
        return this.normFor(s, scope, k);
      case "SwitchStatement":
        return this.normSwitch(s, scope, k);
      case "ForInStatement":
        return this.normForIn(s, scope, k);
      case "ForOfStatement":
        return this.normForOf(s, scope, k);
      case "BreakStatement": {
        if (s.label) throw new NormalizeError("labeled `break` is not supported.");
        const ctx = this.loopStack[this.loopStack.length - 1];
        if (!ctx) throw new NormalizeError("`break` outside a loop.");
        return ctx.onBreak();
      }
      case "ContinueStatement": {
        if (s.label) throw new NormalizeError("labeled `continue` is not supported.");
        const ctx = this.loopStack[this.loopStack.length - 1];
        if (!ctx) throw new NormalizeError("`continue` outside a loop.");
        return ctx.onContinue();
      }
      case "ThrowStatement":
        // Evaluate the operand, then abandon this path (the `try` handler, if any,
        // is modeled as a reachable alternative).
        return this.normAtom(s.argument, scope, (av) => ({ tag: "throw", loc: this.fresh.loc(), val: av }));
      case "TryStatement":
        return this.normTry(s, scope, k);
      // --- modules (EchoJS desugars these; handled here for robustness) --------
      case "ImportDeclaration": {
        // Cross-module linking: bind an imported name to the exporting
        // module's summary when the host's `importValue` hook supplies one
        // (a namespace specifier asks for the whole module as `"*"`).
        // Otherwise bind ⊤ (an import is a real value we know nothing about
        // — binding `undefined` would be unsound as a *type*) and record the
        // degradation: an imports-only-degraded module must not read as a
        // closed world, and the degraded-binding count keeps measuring the
        // residual ⊤ imports.
        const source = s.source && typeof s.source.value === "string" ? s.source.value : undefined;
        let sc = scope;
        const bindings: Array<{ unique: Name; summary?: ImportSummary; span: Span; label: string }> = [];
        for (const spec of s.specifiers) {
          const local = spec.local.name;
          const unique = this.fresh.name(local);
          this.mapNode(spec.local, unique);
          sc = new Map(sc).set(local, unique);
          // The export name this specifier views ("*" = the namespace).
          const imported =
            spec.type === "ImportSpecifier"
              ? spec.imported.type === "Identifier"
                ? spec.imported.name
                : String(spec.imported.value)
              : spec.type === "ImportDefaultSpecifier"
                ? "default"
                : "*";
          const answered = source !== undefined ? this.hooks?.importValue?.(source, imported) : undefined;
          // a namespace is by definition an object: only the object form is
          // acceptable for "*" (a primitive answer would be a host bug —
          // treat it as a miss rather than bind nonsense)
          const summary = imported === "*" && answered !== undefined && answered.fields === undefined
            ? undefined
            : answered;
          const label = `${source ?? "?"}#${imported}`;
          if (summary !== undefined) {
            this.summaryBindings++;
            bindings.push({ unique, summary, span: spanOf(spec), label });
          } else {
            this.degradedBindings.push({
              name: local,
              reason: "unmodeled import — bound to ⊤; no export summary for this binding",
              span: spanOf(spec),
            });
            bindings.push({ unique, span: spanOf(spec), label });
          }
        }
        const go = (i: number): Expr => {
          if (i >= bindings.length) return k(sc);
          const b = bindings[i]!;
          if (b.summary === undefined)
            return this.letE(b.unique, { tag: "atom", loc: this.fresh.loc(), atom: this.litA(litTop) }, go(i + 1));
          return this.bindImportSummary(b.unique, b.summary, b.span, go(i + 1), b.label);
        };
        return go(0);
      }
      case "ExportNamedDeclaration":
        // `export const x = …` → analyze the declaration; `export { a }` → no-op.
        return s.declaration ? this.normStmt(s.declaration, scope, k) : k(scope);
      case "ExportDefaultDeclaration": {
        // A statement-shaped declaration: function/class declarations, and
        // the `let X = (classIIFE)()` a class desugars to (EchoJS runs its
        // class desugar before analysis, so `export default class` arrives
        // as a VariableDeclaration — outside ESTree's declared union).
        const d = s.declaration as Statement | EExpr;
        if (d.type === "FunctionDeclaration" || d.type === "ClassDeclaration" || d.type === "VariableDeclaration")
          return this.normStmt(d as Statement, scope, k);
        return this.normAtom(d as EExpr, scope, () => k(scope)); // export default <expr>
      }
      case "ExportAllDeclaration":
        return k(scope);
      case "WithStatement":
        throw new NormalizeError("`with` is not part of the analyzable dialect (rejected by the validator).");
      default:
        throw new NormalizeError(`unsupported statement: ${s.type}`);
    }
  }

  /**
   * Bind `unique` to an import summary's value, then continue with `rest`.
   * A primitive summary is a `Lit` atom; an OBJECT summary (`fields` — an
   * immutable field set, i.e. a module namespace) materializes as a
   * synthetic object literal at a fresh allocation site, so the importing
   * analysis interns its hidden class and tracks its fields exactly like a
   * local object; a CHECKED-TIER shape summary (`shape` — a mutable
   * exported object) materializes as an OPEN object with the declared
   * hidden class and `⊤` field values.  Nested object fields bind to temps
   * first (object fields are atoms).  `label` names the import
   * (`source#exportName`) for the mutated-imports report.
   */
  /** Default a callable summary's program-wide id to its import label. */
  private withFnId(s: ImportSummary, label: string): ImportSummary {
    if (s.fn === undefined || s.fn.id !== undefined) return s;
    return { ...s, fn: { ...s.fn, id: label } };
  }

  private bindImportSummary(unique: Name, s: ImportSummary, span: Span, rest: Expr, label: string): Expr {
    if (s.fields) {
      const fieldAtoms: Array<readonly [string, AExp]> = [];
      const nested: Array<{ unique: Name; summary: ImportSummary; label: string }> = [];
      for (const f of s.fields) {
        if (f.value !== undefined && (f.value.fields !== undefined || f.value.shape !== undefined)) {
          const t = this.fresh.name(f.name);
          nested.push({ unique: t, summary: f.value, label: `${label}.${f.name}` });
          fieldAtoms.push([f.name, this.varA(t)]);
        } else {
          fieldAtoms.push([
            f.name,
            this.litA(
              f.value !== undefined ? litSummary(this.withFnId(f.value, `${label}.${f.name}`)) : litTop,
            ),
          ]);
        }
      }
      const objLoc = this.fresh.loc();
      this.siteSpans.set(objLoc, span);
      let out: Expr = this.letE(unique, { tag: "obj", loc: objLoc, fields: fieldAtoms }, rest);
      for (let i = nested.length - 1; i >= 0; i--) {
        const n = nested[i]!;
        out = this.bindImportSummary(n.unique, n.summary, span, out, n.label);
      }
      return out;
    }
    if (s.shape) {
      const objLoc = this.fresh.loc();
      this.siteSpans.set(objLoc, span);
      this.importShapeSites.set(objLoc, { label, fields: s.shape });
      return this.letE(
        unique,
        { tag: "shapedTop", loc: objLoc, fields: s.shape.map((f) => [f.name, f.sig] as const) },
        rest,
      );
    }
    return this.letE(
      unique,
      { tag: "atom", loc: this.fresh.loc(), atom: this.litA(litSummary(this.withFnId(s, label))) },
      rest,
    );
  }

  /**
   * `try { body } catch (e) { handler } finally { fin }; rest` — modeled as a
   * nondeterministic choice between normal completion and the handler (with the
   * caught value approximated), both flowing through `finally` into `rest`. This
   * over-approximates (the handler is always considered reachable) but is sound:
   * a `throw` ends its own path, and the handler is analyzed independently.
   */
  private normTry(s: Extract<Statement, { type: "TryStatement" }>, scope: Scope, k: (s: Scope) => Expr): Expr {
    const join = this.fresh.name("join");
    const finThenRest = s.finalizer ? this.normStmts(s.finalizer.body, scope, () => k(scope)) : k(scope);
    const joinLam = this.lamA([], finThenRest);
    const toJoin = () => this.tailE(this.varA(join), []);

    const bodyBranch = this.normStmts(s.block.body, scope, () => toJoin());
    const alts: Expr[] = [bodyBranch];

    // Standard ESTree carries a single `handler`; the EchoJS/old-esprima
    // dialect instead carries `handlers` (an array) plus SpiderMonkey-era
    // `guardedHandlers` (`catch (e if cond)`). Every clause is treated as a
    // reachable alternative; a guard only *restricts* which throws a clause
    // catches, so evaluating it for its dataflow and taking the handler
    // unconditionally is a sound over-approximation.
    const dialect = s as typeof s & {
      handlers?: ReadonlyArray<CatchClause> | null;
      guardedHandlers?: ReadonlyArray<CatchClause> | null;
    };
    const handlers: CatchClause[] = [];
    for (const h of [s.handler, ...(dialect.handlers ?? []), ...(dialect.guardedHandlers ?? [])])
      if (h && !handlers.includes(h)) handlers.push(h);

    for (const handler of handlers) {
      const param = handler.param;
      let hScope = scope;
      let paramUnique: Name | null = null;
      if (param) {
        if (param.type !== "Identifier")
          throw new NormalizeError("destructuring catch parameters are not supported; use a plain name.");
        paramUnique = this.fresh.name(param.name);
        this.mapNode(param, paramUnique);
        hScope = new Map(scope).set(param.name, paramUnique);
      }
      let handlerBranch = this.normStmts(handler.body.body, hScope, () => toJoin());
      const guard = (handler as CatchClause & { guard?: EExpr | null }).guard;
      if (guard) handlerBranch = this.normAtom(guard, hScope, () => handlerBranch);
      // Bind the caught value: any value may be thrown, so the param is ⊤
      // (throw-site tracking would be the precise fix).
      if (paramUnique)
        handlerBranch = this.letE(
          paramUnique,
          { tag: "atom", loc: this.fresh.loc(), atom: this.litA(litTop) },
          handlerBranch,
        );
      alts.push(handlerBranch);
    }

    return {
      tag: "letrec",
      loc: this.fresh.loc(),
      bindings: [{ name: join, lam: joinLam }],
      body: { tag: "nondet", loc: this.fresh.loc(), alts },
    };
  }

  // --- loops: lowered to tail-recursive closures -----------------------------
  //
  // `while (t) body; rest` becomes, roughly:
  //   letrec loop = (brk) => if (t) { body; loop(brk) } else brk()
  //   in loop(() => rest)
  // where `break` calls `brk()` (⇒ runs `rest`) and `continue` tail-calls `loop`.
  // The CESK machine + fixpoint drive it to convergence (store widening), and the
  // loop body's mutations are visible across iterations via the shared store.

  private normWhile(test: EExpr | null | undefined, body: Statement, scope: Scope, k: (s: Scope) => Expr): Expr {
    const loop = this.fresh.name("loop");
    const brk = this.fresh.name("brk");
    const onContinue = () => this.tailE(this.varA(loop), [this.varA(brk)]);
    const onBreak = () => this.tailE(this.varA(brk), []);
    this.loopStack.push({ onBreak, onContinue });
    const bodyExpr = this.normStmt(body, scope, () => onContinue());
    this.loopStack.pop();
    const loopBody = this.normAtom(test ?? trueLiteral(), scope, (tv) => this.ifE(tv, bodyExpr, onBreak()));
    return this.emitLoop(loop, brk, loopBody, k(scope));
  }

  private normDoWhile(test: EExpr, body: Statement, scope: Scope, k: (s: Scope) => Expr): Expr {
    const loop = this.fresh.name("loop");
    const brk = this.fresh.name("brk");
    // `continue`/fall-through re-check the test at the bottom of the loop.
    const checkTest = () =>
      this.normAtom(test, scope, (tv) =>
        this.ifE(tv, this.tailE(this.varA(loop), [this.varA(brk)]), this.tailE(this.varA(brk), [])),
      );
    const onBreak = () => this.tailE(this.varA(brk), []);
    this.loopStack.push({ onBreak, onContinue: checkTest });
    const loopBody = this.normStmt(body, scope, () => checkTest());
    this.loopStack.pop();
    return this.emitLoop(loop, brk, loopBody, k(scope));
  }

  private normFor(s: Extract<Statement, { type: "ForStatement" }>, scope: Scope, k: (s: Scope) => Expr): Expr {
    // for (init; test; update) body ≡ init; while(test){ body; update }, where
    // `continue` runs the update before looping.
    const withInit = (cont: (sc: Scope) => Expr): Expr => {
      const init = s.init;
      if (!init) return cont(scope);
      if (init.type === "VariableDeclaration") return this.normStmt(init, scope, cont);
      return this.normAtom(init as EExpr, scope, () => cont(scope));
    };
    return withInit((sc) => {
      const loop = this.fresh.name("loop");
      const brk = this.fresh.name("brk");
      const updateThenLoop = () =>
        s.update
          ? this.normAtom(s.update, sc, () => this.tailE(this.varA(loop), [this.varA(brk)]))
          : this.tailE(this.varA(loop), [this.varA(brk)]);
      const onBreak = () => this.tailE(this.varA(brk), []);
      this.loopStack.push({ onBreak, onContinue: updateThenLoop });
      const bodyExpr = this.normStmt(s.body, sc, () => updateThenLoop());
      this.loopStack.pop();
      const loopBody = this.normAtom(s.test ?? trueLiteral(), sc, (tv) => this.ifE(tv, bodyExpr, onBreak()));
      // The code after the loop uses the *outer* scope (loop-init vars are local).
      return this.emitLoop(loop, brk, loopBody, k(scope));
    });
  }

  /**
   * `switch (d) { case a: … }` — lowered to a `letrec` of fall-through segments:
   * each case body is a 0-arg segment that, when done, tail-calls the *next*
   * segment (JS fall-through); the last falls into `brk` (the after-switch
   * continuation). A source-order `===` chain picks the entry segment, defaulting
   * to the `default:` segment (or `brk` if none). `break` calls `brk`; `continue`
   * delegates to the enclosing loop.
   */
  private normSwitch(s: Extract<Statement, { type: "SwitchStatement" }>, scope: Scope, k: (s: Scope) => Expr): Expr {
    const cases = s.cases;
    const brk = this.fresh.name("brk");
    const segNames = cases.map(() => this.fresh.name("case"));

    const prev = this.loopStack[this.loopStack.length - 1];
    this.loopStack.push({
      onBreak: () => this.tailE(this.varA(brk), []),
      onContinue: () => {
        if (!prev) throw new NormalizeError("`continue` outside a loop.");
        return prev.onContinue();
      },
    });
    const segBindings = cases.map((c, i) => {
      const fallThrough = () =>
        i + 1 < cases.length ? this.tailE(this.varA(segNames[i + 1]!), []) : this.tailE(this.varA(brk), []);
      return { name: segNames[i]!, lam: this.lamA([], this.normStmts(c.consequent, scope, () => fallThrough())) };
    });
    this.loopStack.pop();

    const defaultIdx = cases.findIndex((c) => c.test == null);
    return this.normAtom(s.discriminant, scope, (d) => {
      const chain = (i: number): Expr => {
        if (i >= cases.length)
          return defaultIdx >= 0 ? this.tailE(this.varA(segNames[defaultIdx]!), []) : this.tailE(this.varA(brk), []);
        if (cases[i]!.test == null) return chain(i + 1); // `default:` is not part of the test order
        return this.normAtom(cases[i]!.test as EExpr, scope, (tv) => {
          const cmp = this.fresh.name();
          return this.letE(
            cmp,
            { tag: "bin", loc: this.fresh.loc(), op: "===", l: d, r: tv },
            this.ifE(this.varA(cmp), this.tailE(this.varA(segNames[i]!), []), chain(i + 1)),
          );
        });
      };
      return {
        tag: "letrec",
        loc: this.fresh.loc(),
        bindings: [{ name: brk, lam: this.lamA([], k(scope)) }, ...segBindings],
        body: chain(0),
      };
    });
  }

  /**
   * `for (k in obj) body` — `k` ranges over `obj`'s enumerable property names.
   * We compute the name set once (`keys(obj)`, an abstract string value) and model
   * iteration as a loop that, each round, either exits (`nondet` alt) or binds `k`
   * to *some* key and runs the body. This is sound (any key, any number of rounds,
   * including zero) and terminates under store widening.
   */
  private normForIn(s: Extract<Statement, { type: "ForInStatement" }>, scope: Scope, k: (s: Scope) => Expr): Expr {
    const left = s.left;
    let bodyScope: Scope;
    let bindKey: (val: AExp, cont: Expr) => Expr;
    if (left.type === "VariableDeclaration") {
      const id = left.declarations[0]!.id;
      if (id.type !== "Identifier") throw new NormalizeError("`for-in` requires a simple variable name.");
      const unique = this.fresh.name(id.name);
      this.mapNode(id, unique);
      bodyScope = new Map(scope).set(id.name, unique);
      bindKey = (val, cont) => this.letE(unique, { tag: "atom", loc: this.fresh.loc(), atom: val }, cont);
    } else if (left.type === "Identifier") {
      const unique = scope.get(left.name) ?? left.name;
      bodyScope = scope;
      bindKey = (val, cont) =>
        this.letE(this.fresh.name(), { tag: "setVar", loc: this.fresh.loc(), name: unique, val }, cont);
    } else {
      throw new NormalizeError("`for-in` target must be a variable.");
    }

    return this.normAtom(s.right as EExpr, scope, (objAtom) => {
      const ks = this.fresh.name("keys");
      const loop = this.fresh.name("loop");
      const brk = this.fresh.name("brk");
      this.loopStack.push({
        onBreak: () => this.tailE(this.varA(brk), []),
        onContinue: () => this.tailE(this.varA(loop), [this.varA(brk)]),
      });
      const bodyExpr = this.normStmt(s.body, bodyScope, () => this.tailE(this.varA(loop), [this.varA(brk)]));
      this.loopStack.pop();
      // Each round: either stop, or bind the loop var to a key and run the body.
      const loopBody: Expr = {
        tag: "nondet",
        loc: this.fresh.loc(),
        alts: [this.tailE(this.varA(brk), []), bindKey(this.varA(ks), bodyExpr)],
      };
      return this.letE(
        ks,
        { tag: "keys", loc: this.fresh.loc(), obj: objAtom },
        this.emitLoop(loop, brk, loopBody, k(scope)),
      );
    });
  }

  /**
   * `for (x of arr) body` — EchoJS EIR lowers `for-of` natively, so post-desugar
   * trees still contain it. Model: evaluate the RHS once and read its abstract
   * per-iteration element (`iterElem` — the join of the element buckets of the
   * arrays it may be; anything untracked degrades to ⊤ and is counted). The loop
   * itself is the same nondeterministic exit-or-iterate fixpoint as `for-in`:
   * each round either stops or binds the loop variable to *some* element and
   * runs the body — sound for any element order and any number of rounds.
   */
  private normForOf(s: Extract<Statement, { type: "ForOfStatement" }>, scope: Scope, k: (s: Scope) => Expr): Expr {
    const left = s.left;
    let bodyScope: Scope;
    let bindElem: (val: AExp, cont: Expr) => Expr;
    if (left.type === "VariableDeclaration") {
      const id = left.declarations[0]!.id;
      if (id.type !== "Identifier") throw new NormalizeError("`for-of` requires a simple variable name.");
      const unique = this.fresh.name(id.name);
      this.mapNode(id, unique); // loop var ↔ the left Identifier node
      bodyScope = new Map(scope).set(id.name, unique);
      bindElem = (val, cont) => this.letE(unique, { tag: "atom", loc: this.fresh.loc(), atom: val }, cont);
    } else if (left.type === "Identifier") {
      const unique = scope.get(left.name) ?? left.name;
      bodyScope = scope;
      bindElem = (val, cont) =>
        this.letE(this.fresh.name(), { tag: "setVar", loc: this.fresh.loc(), name: unique, val }, cont);
    } else {
      throw new NormalizeError("`for-of` target must be a variable.");
    }

    return this.normAtom(s.right as EExpr, scope, (objAtom) => {
      const el = this.fresh.name("elem");
      const loop = this.fresh.name("loop");
      const brk = this.fresh.name("brk");
      this.loopStack.push({
        onBreak: () => this.tailE(this.varA(brk), []),
        onContinue: () => this.tailE(this.varA(loop), [this.varA(brk)]),
      });
      const bodyExpr = this.normStmt(s.body, bodyScope, () => this.tailE(this.varA(loop), [this.varA(brk)]));
      this.loopStack.pop();
      // Each round: either stop, or bind the loop var to an element and run the
      // body. `iterElem` is read INSIDE the loop, so mutations the body makes to
      // the iterated array (a live iterator observes appends) reach the loop
      // variable on the next fixpoint round.
      const loopBody: Expr = this.letE(
        el,
        { tag: "iterElem", loc: this.fresh.loc(), obj: objAtom },
        {
          tag: "nondet",
          loc: this.fresh.loc(),
          alts: [this.tailE(this.varA(brk), []), bindElem(this.varA(el), bodyExpr)],
        },
      );
      return this.emitLoop(loop, brk, loopBody, k(scope));
    });
  }

  /** Assemble `letrec loop = (brk) => loopBody in loop(() => rest)`. */
  private emitLoop(loop: Name, brk: Name, loopBody: Expr, rest: Expr): Expr {
    const loopLam = this.lamA([brk], loopBody);
    const brkClosure = this.lamA([], rest); // `break`/exit continuation: run the rest
    return {
      tag: "letrec",
      loc: this.fresh.loc(),
      bindings: [{ name: loop, lam: loopLam }],
      body: this.tailE(this.varA(loop), [brkClosure]),
    };
  }

  /** Bind `name` to the value of `e`, then continue with `cont`. */
  private normNamed(e: EExpr, scope: Scope, name: Name, cont: Expr): Expr {
    this.mapNode(e, name, /*fromInit*/ true); // the initializer's value lives in the declared name
    switch (e.type) {
      case "CallExpression": {
        const intr = this.tryIntrinsic(e, scope, (a) =>
          this.letE(name, { tag: "atom", loc: this.fresh.loc(), atom: a }, cont),
        );
        if (intr !== null) return intr;
        const callee = e.callee;
        if (callee.type === "MemberExpression" && !callee.computed) {
          const key = memberKeyName(callee);
          if (key === "call")
            return this.lowerDotCall(callee.object as EExpr, e.arguments, scope, (a) =>
              this.letE(name, { tag: "atom", loc: this.fresh.loc(), atom: a }, cont),
            );
          return this.normAtom(callee.object as EExpr, scope, (objA) =>
            this.normArgs(e.arguments, scope, (as) =>
              this.letE(name, { tag: "method", loc: this.fresh.loc(), obj: objA, key, args: as }, cont),
            ),
          );
        }
        if (callee.type === "MemberExpression" && callee.computed)
          return this.lowerComputedCall(callee, e.arguments, scope, (a) =>
            this.letE(name, { tag: "atom", loc: this.fresh.loc(), atom: a }, cont),
          );
        return this.normCallee(callee, scope, (fn) =>
          this.normArgs(e.arguments, scope, (as) =>
            this.letE(name, { tag: "call", loc: this.fresh.loc(), fn, args: as }, cont),
          ),
        );
      }
      case "BinaryExpression":
        return this.normAtom(e.left as EExpr, scope, (l) =>
          this.normAtom(e.right, scope, (r) =>
            this.letE(name, { tag: "bin", loc: this.fresh.loc(), op: binOp(e.operator), l, r }, cont),
          ),
        );
      case "UnaryExpression":
        if (e.operator === "delete") return this.normDelete(e, scope, (a) => this.letE(name, { tag: "atom", loc: this.fresh.loc(), atom: a }, cont));
        return this.normAtom(e.argument, scope, (a) =>
          this.letE(name, { tag: "un", loc: this.fresh.loc(), op: unOp(e.operator), arg: a }, cont),
        );
      default:
        return this.normAtom(e, scope, (a) =>
          this.letE(name, { tag: "atom", loc: this.fresh.loc(), atom: a }, cont),
        );
    }
  }

  // --- expressions (CPS A-normalization to an atomic result) ---------------

  normAtom(e: EExpr, scope: Scope, k: (a: AExp) => Expr): Expr {
    // Central node-mapping hook: whatever the inner lowering produces, if the
    // node's value ends up in a named atom (a binding read or an ANF temp),
    // record node → name for the type oracle. Literal/lambda atoms are not
    // named values; they stay unmapped (see the nodeNames policy block).
    return this.normAtomInner(e, scope, (a) => {
      // Unbound identifier reads keep their raw source name in the atom;
      // mapping those could alias a fresh-minted name — skip them (S2).
      if (a.tag === "var" && (e.type !== "Identifier" || scope.has(e.name))) this.mapNode(e, a.name);
      return k(a);
    });
  }

  private normAtomInner(e: EExpr, scope: Scope, k: (a: AExp) => Expr): Expr {
    switch (e.type) {
      case "Literal": {
        // A regex literal `/…/` is an opaque `RegExp` object — allocate a fresh
        // (empty, method-less) object so its identity and `.test()`/`.exec()` calls
        // degrade gracefully rather than being rejected.
        if ((e as Node & { regex?: unknown }).regex) {
          const t = this.fresh.name();
          return this.letE(t, { tag: "obj", loc: this.fresh.loc(), fields: [] }, k(this.varA(t)));
        }
        return k(this.litA(literal(e)));
      }
      case "Identifier":
        if (!scope.has(e.name) && e.name === "undefined") return k(this.litA(litUndef));
        // The global numeric constants are literals in the dialect (differential-
        // harness finding: an unbound `Infinity` read ⊥ and killed the path).
        if (!scope.has(e.name) && e.name === "Infinity") return k(this.litA(litNum(Infinity)));
        if (!scope.has(e.name) && e.name === "NaN") return k(this.litA(litNum(NaN)));
        return k(this.varA(scope.get(e.name) ?? e.name));
      case "FunctionExpression": {
        // async/generator functions are not modeled: the expression is ⊤,
        // visibly degraded (see the declaration path in normStmts)
        if (unmodeledFnKind(e)) {
          this.degradedBindings.push({
            name: e.id?.name ?? "(anonymous)",
            reason: `${unmodeledFnKind(e)} functions are not modeled; the value is ⊤`,
            span: spanOf(e),
          });
          return k(this.litA(litTop));
        }
        const self = e.id?.name;
        if (self !== undefined) {
          const selfUnique = this.fresh.name(self);
          if (e.id) this.mapNode(e.id, selfUnique);
          const inner = new Map(scope).set(self, selfUnique);
          const lam = this.compileFunction(e.params, e.body, inner, { name: self, span: spanOf(e) }, false, e as OldFunctionDialect);
          return {
            tag: "letrec",
            loc: this.fresh.loc(),
            bindings: [{ name: selfUnique, lam }],
            body: k(this.varA(selfUnique)),
          };
        }
        return k(this.compileFunction(e.params, e.body, scope, { span: spanOf(e) }, false, e as OldFunctionDialect));
      }
      case "ArrowFunctionExpression":
        if (unmodeledFnKind(e)) {
          this.degradedBindings.push({
            name: "(arrow)",
            reason: `${unmodeledFnKind(e)} functions are not modeled; the value is ⊤`,
            span: spanOf(e),
          });
          return k(this.litA(litTop));
        }
        return k(this.compileFunction(e.params, e.body, scope, { span: spanOf(e) }, /* isArrow */ true, e as OldFunctionDialect));
      case "BinaryExpression":
        return this.normAtom(e.left as EExpr, scope, (l) =>
          this.normAtom(e.right, scope, (r) => {
            const t = this.fresh.name();
            return this.letE(t, { tag: "bin", loc: this.fresh.loc(), op: binOp(e.operator), l, r }, k(this.varA(t)));
          }),
        );
      case "UnaryExpression":
        if (e.operator === "delete") return this.normDelete(e, scope, k);
        return this.normAtom(e.argument, scope, (a) => {
          const t = this.fresh.name();
          return this.letE(t, { tag: "un", loc: this.fresh.loc(), op: unOp(e.operator), arg: a }, k(this.varA(t)));
        });
      case "CallExpression": {
        const intr = this.tryIntrinsic(e, scope, k);
        if (intr !== null) return intr;
        const callee = e.callee;
        if (callee.type === "MemberExpression" && !callee.computed) {
          const key = memberKeyName(callee);
          // `fn.call(thisArg, ...args)` — invoke with an explicit receiver.
          if (key === "call") return this.lowerDotCall(callee.object as EExpr, e.arguments, scope, k);
          // Method call `obj.key(args)` — dispatched with `this` = obj.
          const t = this.fresh.name();
          return this.normAtom(callee.object as EExpr, scope, (objA) =>
            this.normArgs(e.arguments, scope, (as) =>
              this.letE(t, { tag: "method", loc: this.fresh.loc(), obj: objA, key, args: as }, k(this.varA(t))),
            ),
          );
        }
        if (callee.type === "MemberExpression" && callee.computed)
          return this.lowerComputedCall(callee, e.arguments, scope, k);
        return this.normCallee(callee, scope, (fn) =>
          this.normArgs(e.arguments, scope, (as) => {
            const t = this.fresh.name();
            return this.letE(t, { tag: "call", loc: this.fresh.loc(), fn, args: as }, k(this.varA(t)));
          }),
        );
      }
      case "LogicalExpression": {
        if (e.operator !== "&&" && e.operator !== "||" && e.operator !== "??")
          throw new NormalizeError(`unsupported logical operator \`${e.operator}\`.`);
        const t = this.fresh.name();
        const cont = k(this.varA(t));
        return this.normAtom(e.left, scope, (lv) => {
          const bindTo = (val: AExp) => this.letE(t, { tag: "atom", loc: this.fresh.loc(), atom: val }, cont);
          const evalRight = this.normAtom(e.right, scope, (rv) => bindTo(rv));
          if (e.operator === "??") {
            // `a ?? b`: branch on the nullish test — loose-eq-null is
            // true exactly for null/undefined
            const nz = this.fresh.name();
            return this.letE(
              nz,
              { tag: "bin", loc: this.fresh.loc(), op: "==", l: lv, r: this.litA(litNull) },
              this.ifE(this.varA(nz), evalRight, bindTo(lv)),
            );
          }
          return e.operator === "&&" ? this.ifE(lv, evalRight, bindTo(lv)) : this.ifE(lv, bindTo(lv), evalRight);
        });
      }
      case "ChainExpression": {
        // `a?.b`, `a?.[k]`, `f?.(…)`: one shared short-circuit — the
        // first nullish link binds the WHOLE chain's result to
        // undefined (spec short-circuit).  Each link is normalized
        // once; the nullish test is loose-eq-null.
        const t = this.fresh.name();
        const cont = k(this.varA(t));
        const bindTo = (val: AExp) => this.letE(t, { tag: "atom", loc: this.fresh.loc(), atom: val }, cont);
        return this.normChain(e.expression as EExpr, scope, () => bindTo(this.litA(litUndef)), bindTo);
      }
      case "ConditionalExpression": {
        const t = this.fresh.name();
        const cont = k(this.varA(t));
        return this.normAtom(e.test, scope, (tv) => {
          const then = this.normAtom(e.consequent, scope, (cv) =>
            this.letE(t, { tag: "atom", loc: this.fresh.loc(), atom: cv }, cont),
          );
          const els = this.normAtom(e.alternate, scope, (av) =>
            this.letE(t, { tag: "atom", loc: this.fresh.loc(), atom: av }, cont),
          );
          return this.ifE(tv, then, els);
        });
      }
      case "ObjectExpression": {
        // { a: e1, b: e2 } — evaluate values in order, then allocate.
        const props: Array<{ key: string; value: EExpr }> = e.properties.map((p) => {
          if (p.type !== "Property")
            throw new NormalizeError("object spread (`...x`) is not supported.");
          if (p.computed) throw new NormalizeError("computed object keys (`{[e]: …}`) are not supported.");
          if (p.kind !== "init") throw new NormalizeError("object getters/setters are not supported.");
          return { key: propKeyName(p.key), value: p.value as EExpr };
        });
        const t = this.fresh.name("obj");
        const objLoc = this.fresh.loc();
        this.siteSpans.set(objLoc, spanOf(e)); // remember the source of this site
        const buildFields = (i: number, acc: Array<readonly [string, AExp]>): Expr => {
          if (i >= props.length) {
            return this.letE(t, { tag: "obj", loc: objLoc, fields: acc }, k(this.varA(t)));
          }
          const pr = props[i]!;
          return this.normAtom(pr.value, scope, (av) => buildFields(i + 1, [...acc, [pr.key, av]]));
        };
        return buildFields(0, []);
      }
      case "MemberExpression": {
        const getLoc = this.fresh.loc();
        this.siteSpans.set(getLoc, spanOf(e)); // property-read site (for the accessor/inlining report)
        if (e.computed) {
          // `obj["foo"]` with a constant key is a static read; otherwise dynamic.
          const constKey = literalString(e.property as Node);
          if (constKey !== null)
            return this.normAtom(e.object as EExpr, scope, (obj) => {
              const t = this.fresh.name();
              return this.letE(t, { tag: "get", loc: getLoc, obj, key: constKey }, k(this.varA(t)));
            });
          return this.normAtom(e.object as EExpr, scope, (obj) =>
            this.normAtom(e.property as EExpr, scope, (keyExpr) => {
              const t = this.fresh.name();
              return this.letE(t, { tag: "getDyn", loc: getLoc, obj, keyExpr }, k(this.varA(t)));
            }),
          );
        }
        const key = memberKeyName(e);
        const t = this.fresh.name();
        return this.normAtom(e.object as EExpr, scope, (obj) =>
          this.letE(t, { tag: "get", loc: getLoc, obj, key }, k(this.varA(t))),
        );
      }
      case "ArrayExpression": {
        const arrLoc = this.fresh.loc();
        this.siteSpans.set(arrLoc, spanOf(e));
        const elemExprs = e.elements;
        const t = this.fresh.name("arr");
        const go = (i: number, acc: AExp[]): Expr => {
          if (i >= elemExprs.length) return this.letE(t, { tag: "array", loc: arrLoc, elems: acc }, k(this.varA(t)));
          const el = elemExprs[i];
          if (!el) return go(i + 1, [...acc, this.litA(litUndef)]); // elision (hole)
          if (el.type === "SpreadElement") throw new NormalizeError("array spread (`[...x]`) is not supported.");
          return this.normAtom(el as EExpr, scope, (av) => go(i + 1, [...acc, av]));
        };
        return go(0, []);
      }
      case "AssignmentExpression":
        return this.normAssign(e, scope, k);
      case "NewExpression": {
        if (e.callee.type === "Super") throw new NormalizeError("`new super(...)` is not supported.");
        // `new foo.Bar(...)`: `normAtom` reads the constructor value (a plain
        // property load, no `this`-binding) into a temp, then we construct it.
        const newLoc = this.fresh.loc();
        this.siteSpans.set(newLoc, spanOf(e));
        const t = this.fresh.name();
        return this.normAtom(e.callee, scope, (fn) =>
          this.normArgs(e.arguments, scope, (as) =>
            this.letE(t, { tag: "new", loc: newLoc, fn, args: as }, k(this.varA(t))),
          ),
        );
      }
      case "ThisExpression":
        // `this` is a reserved variable the machine binds on constructor entry.
        return k(this.varA(thisVarName(this.currentThisOwner)));
      case "SequenceExpression": {
        // `(a, b, c)` — evaluate each for effect, result is the last.
        const exprs = e.expressions;
        const go = (i: number): Expr =>
          i === exprs.length - 1
            ? this.normAtom(exprs[i] as EExpr, scope, k)
            : this.normAtom(exprs[i] as EExpr, scope, () => go(i + 1));
        return exprs.length === 0 ? k(this.litA(litUndef)) : go(0);
      }
      case "UpdateExpression":
        return this.normUpdate(e, scope, k);
      case "TemplateLiteral":
        return this.normTemplate(e, scope, k);
      case "TaggedTemplateExpression": {
        // Not modeled: evaluate the tag and every interpolated expression for
        // their dataflow, then lower to a call whose callee holds no closure —
        // counted in `metrics.unknownCalls`, result ⊤ (same treatment as an
        // unknown `%`-intrinsic).
        const exprs = e.quasi.expressions;
        return this.normAtom(e.tag as EExpr, scope, () => {
          const go = (i: number): Expr => {
            if (i >= exprs.length) {
              const t = this.fresh.name();
              return this.letE(
                t,
                { tag: "call", loc: this.fresh.loc(), fn: this.litA(litUndef), args: [] },
                k(this.varA(t)),
              );
            }
            return this.normAtom(exprs[i] as EExpr, scope, () => go(i + 1));
          };
          return go(0);
        });
      }
      default:
        throw new NormalizeError(`unsupported expression: ${e.type}`);
    }
  }

  /**
   * `` `a${x}b` `` — string concatenation with an implicit ToString on each
   * interpolated expression: `"a" + toStr(x) + "b"`. Expressions are evaluated
   * left to right; the result is always string-typed (the `toStr` unop
   * guarantees ⊆ string even for ⊤ operands).
   */
  private normTemplate(
    e: EExpr & { type: "TemplateLiteral" },
    scope: Scope,
    k: (a: AExp) => Expr,
  ): Expr {
    const quasis = e.quasis;
    const exprs = e.expressions;
    const cooked = (i: number): string => quasis[i]?.value.cooked ?? "";
    // Bind `name = l + r; cont(name)` — one concat step.
    const concat = (l: AExp, r: AExp, cont: (a: AExp) => Expr): Expr => {
      const t = this.fresh.name();
      return this.letE(t, { tag: "bin", loc: this.fresh.loc(), op: "+", l, r }, cont(this.varA(t)));
    };
    const go = (i: number, acc: AExp): Expr => {
      if (i >= exprs.length) return k(acc);
      return this.normAtom(exprs[i] as EExpr, scope, (ev) => {
        const s = this.fresh.name();
        return this.letE(s, { tag: "un", loc: this.fresh.loc(), op: "toStr", arg: ev }, // ToString(xᵢ)
          concat(acc, this.varA(s), (acc2) =>
            concat(acc2, this.litA(litStr(cooked(i + 1))), (acc3) => go(i + 1, acc3)),
          ),
        );
      });
    };
    return go(0, this.litA(litStr(cooked(0))));
  }

  /** Lower `x = v` / `obj.p = v` / `x += v` (variable or property assignment). */
  private normAssign(
    e: EExpr & { type: "AssignmentExpression" },
    scope: Scope,
    k: (a: AExp) => Expr,
  ): Expr {
    const compound = e.operator !== "=";
    const binToken = compound ? e.operator.slice(0, -1) : null; // "+=" → "+"
    const left = e.left;

    if (left.type === "Identifier") {
      const name = scope.get(left.name) ?? left.name;
      // value = right, or (x <op> right) for compound assignment
      const withValue = (cont: (val: AExp) => Expr): Expr =>
        compound
          ? this.normAtom(e.right, scope, (r) => {
              const t = this.fresh.name();
              return this.letE(
                t,
                { tag: "bin", loc: this.fresh.loc(), op: binOp(binToken!), l: this.varA(name), r },
                cont(this.varA(t)),
              );
            })
          : this.normAtom(e.right, scope, cont);
      return withValue((val) => {
        const t = this.fresh.name();
        return this.letE(t, { tag: "setVar", loc: this.fresh.loc(), name, val }, k(this.varA(t)));
      });
    }

    if (left.type === "MemberExpression" && !left.computed) {
      const key = memberKeyName(left);
      const putLoc = this.fresh.loc();
      this.siteSpans.set(putLoc, spanOf(e));
      // Evaluate the object once, then the value (for compound: obj.key <op> right).
      return this.normAtom(left.object as EExpr, scope, (obj) => {
        const doPut = (val: AExp): Expr => {
          const t = this.fresh.name();
          return this.letE(t, { tag: "put", loc: putLoc, obj, key, val }, k(this.varA(t)));
        };
        if (!compound) return this.normAtom(e.right, scope, doPut);
        const cur = this.fresh.name();
        return this.letE(
          cur,
          { tag: "get", loc: this.fresh.loc(), obj, key },
          this.normAtom(e.right, scope, (r) => {
            const combined = this.fresh.name();
            return this.letE(
              combined,
              { tag: "bin", loc: this.fresh.loc(), op: binOp(binToken!), l: this.varA(cur), r },
              doPut(this.varA(combined)),
            );
          }),
        );
      });
    }

    if (left.type === "MemberExpression" && left.computed) {
      const putLoc = this.fresh.loc();
      this.siteSpans.set(putLoc, spanOf(e));
      const constKey = literalString(left.property as Node);
      return this.normAtom(left.object as EExpr, scope, (obj) => {
        const withKey = (cont: (rhs: (val: AExp) => RHS) => Expr): Expr =>
          constKey !== null
            ? cont((val) => ({ tag: "put", loc: putLoc, obj, key: constKey, val }))
            : this.normAtom(left.property as EExpr, scope, (keyExpr) =>
                cont((val) => ({ tag: "putDyn", loc: putLoc, obj, keyExpr, val })),
              );
        return withKey((mkRhs) => {
          if (!compound)
            return this.normAtom(e.right, scope, (val) => {
              const t = this.fresh.name();
              return this.letE(t, mkRhs(val), k(this.varA(t)));
            });
          // compound computed assignment: read (via the same key), combine, write.
          const cur = this.fresh.name();
          const readRhs: RHS =
            constKey !== null
              ? { tag: "get", loc: this.fresh.loc(), obj, key: constKey }
              : { tag: "getDyn", loc: this.fresh.loc(), obj, keyExpr: this.litA(litUndef) };
          // Note: for a dynamic compound like `a[i] += 1`, we re-read the element
          // bucket rather than the exact index (sound for the smashed model).
          return this.letE(
            cur,
            readRhs,
            this.normAtom(e.right, scope, (r) => {
              const combined = this.fresh.name();
              return this.letE(
                combined,
                { tag: "bin", loc: this.fresh.loc(), op: binOp(binToken!), l: this.varA(cur), r },
                (() => {
                  const t = this.fresh.name();
                  return this.letE(t, mkRhs(this.varA(combined)), k(this.varA(t)));
                })(),
              );
            }),
          );
        });
      });
    }

    throw new NormalizeError("unsupported assignment target.");
  }

  /** Lower `x++` / `++x` / `x--` / `--x`, on a plain variable or an object member. */
  private normUpdate(e: EExpr & { type: "UpdateExpression" }, scope: Scope, k: (a: AExp) => Expr): Expr {
    const op = e.operator === "++" ? "+" : "-";
    if (e.argument.type === "MemberExpression") return this.normUpdateMember(e.argument, op, e.prefix, scope, k);
    if (e.argument.type !== "Identifier")
      throw new NormalizeError("update expressions are only supported on variables and object members.");
    const name = scope.get(e.argument.name) ?? e.argument.name;
    // old = x; x = x <op> 1; result = prefix ? new : old
    const oldName = this.fresh.name();
    const newName = this.fresh.name();
    return this.letE(
      oldName,
      { tag: "atom", loc: this.fresh.loc(), atom: this.varA(name) },
      this.letE(
        newName,
        { tag: "bin", loc: this.fresh.loc(), op, l: this.varA(name), r: this.litA(litNum(1)) },
        this.letE(
          this.fresh.name(),
          { tag: "setVar", loc: this.fresh.loc(), name, val: this.varA(newName) },
          k(this.varA(e.prefix ? newName : oldName)),
        ),
      ),
    );
  }

  /** Lower `o.x++` / `o[i]--` on an object member: read, `±1`, write back. */
  private normUpdateMember(
    m: EExpr & { type: "MemberExpression" },
    op: "+" | "-",
    prefix: boolean,
    scope: Scope,
    k: (a: AExp) => Expr,
  ): Expr {
    const loc = this.fresh.loc();
    this.siteSpans.set(loc, spanOf(m));
    const constKey = m.computed ? literalString(m.property as Node) : memberKeyName(m);
    return this.normAtom(m.object as EExpr, scope, (obj) => {
      // Resolve read/write RHS builders (static key, or a computed key evaluated once).
      const build = (readRhs: RHS, mkPut: (val: AExp) => RHS): Expr => {
        const oldName = this.fresh.name();
        const newName = this.fresh.name();
        return this.letE(
          oldName,
          readRhs,
          this.letE(
            newName,
            { tag: "bin", loc: this.fresh.loc(), op, l: this.varA(oldName), r: this.litA(litNum(1)) },
            this.letE(
              this.fresh.name(),
              mkPut(this.varA(newName)),
              k(this.varA(prefix ? newName : oldName)),
            ),
          ),
        );
      };
      if (constKey !== null)
        return build(
          { tag: "get", loc: this.fresh.loc(), obj, key: constKey },
          (val) => ({ tag: "put", loc, obj, key: constKey, val }),
        );
      // Dynamic key: evaluate it once, read the (smashed) element bucket, write it back.
      return this.normAtom(m.property as EExpr, scope, (keyExpr) =>
        build(
          { tag: "getDyn", loc: this.fresh.loc(), obj, keyExpr },
          (val) => ({ tag: "putDyn", loc, obj, keyExpr, val }),
        ),
      );
    });
  }

  /**
   * `delete obj.prop` — evaluate the object subexpression for effect and yield
   * `true`. We do *not* remove the field from the abstract object: a may-type
   * analysis that keeps a possibly-deleted property is sound (the property "may"
   * still be present); it only loses the "definitely absent" fact.
   */
  private normDelete(e: EExpr & { type: "UnaryExpression" }, scope: Scope, k: (a: AExp) => Expr): Expr {
    const arg = e.argument;
    const obj = arg.type === "MemberExpression" ? (arg.object as EExpr) : arg;
    return this.normAtom(obj, scope, () => k(this.litA(litBool(true))));
  }

  /** A callee must itself be atomic (identifier / literal function). */
  // --- optional chains -----------------------------------------------------
  // Lower one link of an optional chain.  `shortCircuit` is the shared
  // whole-chain exit (bind undefined); an optional link tests its base
  // with loose-eq-null and either exits or proceeds.  Property reads
  // are pure in-model (getters lower to defineAccessor, object-literal
  // getters are rejected), so the optional method call's read-then-
  // dispatch double read is sound.
  private normChain(e: EExpr, scope: Scope, shortCircuit: () => Expr, k: (a: AExp) => Expr): Expr {
    const guardNullish = (a: AExp, proceed: () => Expr): Expr => {
      const nz = this.fresh.name();
      return this.letE(
        nz,
        { tag: "bin", loc: this.fresh.loc(), op: "==", l: a, r: this.litA(litNull) },
        this.ifE(this.varA(nz), shortCircuit(), proceed()),
      );
    };
    if (e.type === "MemberExpression") {
      const getLoc = this.fresh.loc();
      this.siteSpans.set(getLoc, spanOf(e));
      const read = (obj: AExp): Expr => {
        if (e.computed) {
          const constKey = literalString(e.property as Node);
          if (constKey !== null) {
            const t = this.fresh.name();
            return this.letE(t, { tag: "get", loc: getLoc, obj, key: constKey }, k(this.varA(t)));
          }
          return this.normAtom(e.property as EExpr, scope, (keyExpr) => {
            const t = this.fresh.name();
            return this.letE(t, { tag: "getDyn", loc: getLoc, obj, keyExpr }, k(this.varA(t)));
          });
        }
        const key = memberKeyName(e);
        const t = this.fresh.name();
        return this.letE(t, { tag: "get", loc: getLoc, obj, key }, k(this.varA(t)));
      };
      return this.normChain(e.object as EExpr, scope, shortCircuit, (obj) =>
        e.optional ? guardNullish(obj, () => read(obj)) : read(obj),
      );
    }
    if (e.type === "CallExpression") {
      const callee = e.callee;
      if (callee.type === "MemberExpression") {
        if (callee.computed) throw new NormalizeError("computed method calls in an optional chain are not supported.");
        const key = memberKeyName(callee);
        const invoke = (obj: AExp): Expr =>
          this.normArgs(e.arguments, scope, (as) => {
            const t = this.fresh.name();
            return this.letE(t, { tag: "method", loc: this.fresh.loc(), obj, key, args: as }, k(this.varA(t)));
          });
        return this.normChain(callee.object as EExpr, scope, shortCircuit, (obj) => {
          const dispatch = (): Expr => {
            if (!e.optional) return invoke(obj);
            // `obj.m?.(…)`: read the method value for the nullish test,
            // then dispatch with the receiver
            const fv = this.fresh.name();
            const getLoc = this.fresh.loc();
            this.siteSpans.set(getLoc, spanOf(callee));
            return this.letE(fv, { tag: "get", loc: getLoc, obj, key }, guardNullish(this.varA(fv), () => invoke(obj)));
          };
          return callee.optional ? guardNullish(obj, dispatch) : dispatch();
        });
      }
      return this.normChain(callee as EExpr, scope, shortCircuit, (fn) => {
        const invoke = (): Expr =>
          this.normArgs(e.arguments, scope, (as) => {
            const t = this.fresh.name();
            return this.letE(t, { tag: "call", loc: this.fresh.loc(), fn, args: as }, k(this.varA(t)));
          });
        return e.optional ? guardNullish(fn, invoke) : invoke();
      });
    }
    // chain root: an ordinary expression
    return this.normAtom(e, scope, k);
  }

  private normCallee(callee: EExpr | { type: "Super" }, scope: Scope, k: (fn: AExp) => Expr): Expr {
    if (callee.type === "Super")
      throw new NormalizeError("`super` calls are not supported.");
    if (callee.type === "MemberExpression")
      throw new NormalizeError("computed method calls (`obj[e](...)`) are not supported.");
    return this.normAtom(callee, scope, k);
  }

  /**
   * `obj[e](args)` — a *computed* method call. Read the callee via a dynamic
   * property access (`getDyn`, which soundly joins the object's fields), then
   * invoke it with `this` bound to `obj` (an `apply`, like `fn.call(obj, …)`).
   */
  private lowerComputedCall(
    callee: EExpr & { type: "MemberExpression" },
    args: ReadonlyArray<EExpr | { type: "SpreadElement" }>,
    scope: Scope,
    k: (a: AExp) => Expr,
  ): Expr {
    return this.normAtom(callee.object as EExpr, scope, (objA) =>
      this.normAtom(callee.property as EExpr, scope, (keyA) => {
        const fnT = this.fresh.name();
        return this.letE(
          fnT,
          { tag: "getDyn", loc: this.fresh.loc(), obj: objA, keyExpr: keyA },
          this.normArgs(args, scope, (as) => {
            const t = this.fresh.name();
            return this.letE(
              t,
              { tag: "apply", loc: this.fresh.loc(), fn: this.varA(fnT), thisArg: objA, args: as },
              k(this.varA(t)),
            );
          }),
        );
      }),
    );
  }

  /** Normalize call arguments; spreads are rejected. */
  private normArgs(
    args: ReadonlyArray<EExpr | { type: "SpreadElement" }>,
    scope: Scope,
    k: (as: AExp[]) => Expr,
  ): Expr {
    const go = (i: number, acc: AExp[]): Expr => {
      if (i >= args.length) return k(acc);
      const a = args[i]!;
      if (a.type === "SpreadElement") throw new NormalizeError("spread arguments (`...x`) are not supported.");
      return this.normAtom(a, scope, (av) => go(i + 1, [...acc, av]));
    };
    return go(0, []);
  }

  // --- object intrinsics (EchoJS desugared class output) -------------------

  /**
   * Recognize the object-model primitives EchoJS's desugarer emits — the
   * `%objectCreate`/`%setPrototypeOf` intrinsics and the `Object.defineProperty`/
   * `Object.defineProperties`/`Object.create`/`Object.setPrototypeOf` calls — and
   * lower them to core forms. Returns `null` if `e` is an ordinary call.
   */
  private tryIntrinsic(e: CallExpression, scope: Scope, k: (a: AExp) => Expr): Expr | null {
    const callee = e.callee;
    const args = e.arguments.filter((a): a is EExpr => a.type !== "SpreadElement");

    // A scope-bound `%`-named identifier (e.g. the `%super` parameter in class
    // desugar output) is an ordinary variable, not an intrinsic: fall through.
    if (callee.type === "Identifier" && callee.name.startsWith("%") && !scope.has(callee.name)) {
      switch (callee.name) {
        case "%objectCreate":
          return this.lowerObjectCreate(args[0], scope, k);
        case "%setPrototypeOf":
          return this.lowerSetProto(args[0], args[1], scope, k);
        case "%setConstructorKindDerived":
        case "%setConstructorKindBase":
          return k(this.litA(litUndef)); // constructor-kind marker — no dataflow effect
        case "%constructSuper": {
          // %constructSuper(superCtor, ...args) — run the super constructor on the
          // *current* `this` (no fresh allocation).
          const sup = args[0];
          if (!sup) throw new NormalizeError("%constructSuper needs a superclass argument.");
          return this.normAtom(sup, scope, (fn) =>
            this.normArgs(args.slice(1), scope, (as) => {
              const t = this.fresh.name();
              return this.letE(
                t,
                { tag: "apply", loc: this.fresh.loc(), fn, thisArg: this.varA(thisVarName(this.currentThisOwner)), args: as },
                k(this.varA(t)),
              );
            }),
          );
        }
        default:
          // An intrinsic we don't model (`%arrayFromSpread`, `%makeGenerator`,
          // `%constructSuperApply`, …): evaluate the arguments for their
          // dataflow, then lower to a call whose callee holds no closure — the
          // machine records the site in `metrics.unknownCalls` and degrades
          // the result, exactly like any other unknown callee.
          return this.normArgs(args, scope, (as) => {
            const t = this.fresh.name();
            return this.letE(
              t,
              { tag: "call", loc: this.fresh.loc(), fn: this.litA(litUndef), args: as },
              k(this.varA(t)),
            );
          });
      }
    }

    if (
      callee.type === "MemberExpression" &&
      !callee.computed &&
      callee.object.type === "Identifier" &&
      callee.object.name === "Object" &&
      callee.property.type === "Identifier"
    ) {
      switch (callee.property.name) {
        case "create":
          return this.lowerObjectCreate(args[0], scope, k);
        case "setPrototypeOf":
          return this.lowerSetProto(args[0], args[1], scope, k);
        case "defineProperty":
          return this.lowerDefineProperty(args[0], args[1], args[2], scope, k);
        case "defineProperties":
          return this.lowerDefineProperties(args[0], args[1], scope, k);
        default:
          return null; // some other Object.* — leave as an ordinary (stuck) call
      }
    }
    return null;
  }

  /** Lower `fn.call(thisArg, ...args)` to the core `apply` form. */
  private lowerDotCall(
    fnExpr: EExpr,
    callArgs: ReadonlyArray<EExpr | { type: "SpreadElement" }>,
    scope: Scope,
    k: (a: AExp) => Expr,
  ): Expr {
    const argExprs = callArgs.filter((a): a is EExpr => a.type !== "SpreadElement");
    if (argExprs.length !== callArgs.length)
      throw new NormalizeError("spread arguments in `.call(...)` are not supported.");
    return this.normAtom(fnExpr, scope, (fn) => {
      const withThis = (cont: (ta: AExp) => Expr): Expr =>
        argExprs.length > 0 ? this.normAtom(argExprs[0]!, scope, cont) : cont(this.litA(litUndef));
      return withThis((thisArg) =>
        this.normArgs(argExprs.slice(1), scope, (as) => {
          const t = this.fresh.name();
          return this.letE(t, { tag: "apply", loc: this.fresh.loc(), fn, thisArg, args: as }, k(this.varA(t)));
        }),
      );
    });
  }

  private lowerObjectCreate(protoExpr: EExpr | undefined, scope: Scope, k: (a: AExp) => Expr): Expr {
    const proto = protoExpr ?? nullLiteral();
    return this.normAtom(proto, scope, (p) => {
      const t = this.fresh.name("obj");
      return this.letE(t, { tag: "objectCreate", loc: this.fresh.loc(), proto: p }, k(this.varA(t)));
    });
  }

  private lowerSetProto(oExpr: EExpr | undefined, pExpr: EExpr | undefined, scope: Scope, k: (a: AExp) => Expr): Expr {
    if (!oExpr || !pExpr) throw new NormalizeError("setPrototypeOf needs two arguments.");
    return this.normAtom(oExpr, scope, (o) =>
      this.normAtom(pExpr, scope, (p) => {
        const t = this.fresh.name();
        return this.letE(t, { tag: "setProto", loc: this.fresh.loc(), obj: o, proto: p }, k(this.varA(t)));
      }),
    );
  }

  private lowerDefineProperty(
    oExpr: EExpr | undefined,
    keyExpr: EExpr | undefined,
    descExpr: EExpr | undefined,
    scope: Scope,
    k: (a: AExp) => Expr,
  ): Expr {
    if (!oExpr || !keyExpr || !descExpr) throw new NormalizeError("Object.defineProperty needs three arguments.");
    const key = literalString(keyExpr);
    if (key === null) {
      // Dynamic key.  A DATA define (the host's class desugar emits
      // these for `[Symbol.iterator]()` methods) is a dynamic-key own
      // write: putDyn widens the object's key tracking soundly.
      // Dynamic-key ACCESSOR installs stay rejected — the getter's
      // call effects would be unmodeled.
      if (descExpr.type !== "ObjectExpression")
        throw new NormalizeError("Object.defineProperty requires a literal descriptor object.");
      const dynValue = descriptorField(descExpr, "value");
      if (descriptorField(descExpr, "get") || descriptorField(descExpr, "set") || !dynValue)
        throw new NormalizeError("Object.defineProperty with a dynamic key requires a `value` descriptor.");
      return this.normAtom(oExpr, scope, (o) =>
        this.normAtom(keyExpr, scope, (kx) =>
          this.normAtom(dynValue, scope, (v) => {
            const t = this.fresh.name();
            return this.letE(t, { tag: "putDyn", loc: this.fresh.loc(), obj: o, keyExpr: kx, val: v }, k(this.varA(t)));
          }),
        ),
      );
    }
    if (descExpr.type !== "ObjectExpression")
      throw new NormalizeError("Object.defineProperty requires a literal descriptor object.");
    const value = descriptorField(descExpr, "value");
    const getter = descriptorField(descExpr, "get");
    const setter = descriptorField(descExpr, "set");
    if (getter || setter) return this.lowerAccessor(oExpr, key, getter, setter, scope, k);
    if (!value) throw new NormalizeError("unsupported property descriptor (no `value`, `get`, or `set`).");
    // A data property define is exactly an own-property write.
    return this.normAtom(oExpr, scope, (o) =>
      this.normAtom(value, scope, (v) => {
        const t = this.fresh.name();
        return this.letE(t, { tag: "put", loc: this.fresh.loc(), obj: o, key, val: v }, k(this.varA(t)));
      }),
    );
  }

  /** Lower an accessor-property define to the core `defineAccessor` form. */
  private lowerAccessor(
    oExpr: EExpr,
    key: string,
    getterExpr: EExpr | null,
    setterExpr: EExpr | null,
    scope: Scope,
    k: (a: AExp) => Expr,
  ): Expr {
    return this.normAtom(oExpr, scope, (o) => {
      // Normalize the getter/setter functions (if present) to atoms, then install.
      const withGetter = (cont: (g?: AExp) => Expr): Expr =>
        getterExpr ? this.normAtom(getterExpr, scope, (g) => cont(g)) : cont(undefined);
      const withSetter = (cont: (s?: AExp) => Expr): Expr =>
        setterExpr ? this.normAtom(setterExpr, scope, (s) => cont(s)) : cont(undefined);
      return withGetter((g) =>
        withSetter((s) => {
          const t = this.fresh.name();
          const rhs: RHS = {
            tag: "defineAccessor",
            loc: this.fresh.loc(),
            obj: o,
            key,
            ...(g ? { getter: g } : {}),
            ...(s ? { setter: s } : {}),
          };
          return this.letE(t, rhs, k(this.varA(t)));
        }),
      );
    });
  }

  private lowerDefineProperties(
    oExpr: EExpr | undefined,
    descsExpr: EExpr | undefined,
    scope: Scope,
    k: (a: AExp) => Expr,
  ): Expr {
    if (!oExpr || !descsExpr) throw new NormalizeError("Object.defineProperties needs two arguments.");
    if (descsExpr.type !== "ObjectExpression")
      throw new NormalizeError("Object.defineProperties requires a literal descriptors object.");
    type Entry =
      | { kind: "data"; key: string; value: EExpr }
      | { kind: "accessor"; key: string; getter: EExpr | null; setter: EExpr | null };
    const entries: Entry[] = [];
    for (const p of descsExpr.properties) {
      if (p.type !== "Property") throw new NormalizeError("object spread in defineProperties is not supported.");
      const key = propKeyName(p.key);
      const desc = p.value;
      if (desc.type !== "ObjectExpression")
        throw new NormalizeError("each defineProperties descriptor must be a literal object.");
      const getter = descriptorField(desc, "get");
      const setter = descriptorField(desc, "set");
      if (getter || setter) {
        entries.push({ kind: "accessor", key, getter, setter });
      } else {
        const value = descriptorField(desc, "value");
        if (!value) throw new NormalizeError("unsupported descriptor in defineProperties (no value/get/set).");
        entries.push({ kind: "data", key, value });
      }
    }
    // Emit one define (data write or accessor install) per descriptor, in order.
    return this.normAtom(oExpr, scope, (o) => {
      const go = (i: number): Expr => {
        if (i >= entries.length) return k(this.litA(litUndef));
        const en = entries[i]!;
        const rest = () => go(i + 1);
        if (en.kind === "data") {
          return this.normAtom(en.value, scope, (v) => {
            const t = this.fresh.name();
            return this.letE(t, { tag: "put", loc: this.fresh.loc(), obj: o, key: en.key, val: v }, rest());
          });
        }
        // reuse lowerAccessor by supplying `o` as an already-atomic object
        return this.installAccessorAtom(o, en.key, en.getter, en.setter, scope, rest);
      };
      return go(0);
    });
  }

  /** Install an accessor on an already-atomic object, then continue with `cont`. */
  private installAccessorAtom(
    o: AExp,
    key: string,
    getterExpr: EExpr | null,
    setterExpr: EExpr | null,
    scope: Scope,
    cont: () => Expr,
  ): Expr {
    const withGetter = (c: (g?: AExp) => Expr): Expr =>
      getterExpr ? this.normAtom(getterExpr, scope, (g) => c(g)) : c(undefined);
    const withSetter = (c: (s?: AExp) => Expr): Expr =>
      setterExpr ? this.normAtom(setterExpr, scope, (s) => c(s)) : c(undefined);
    return withGetter((g) =>
      withSetter((s) => {
        const t = this.fresh.name();
        const rhs: RHS = {
          tag: "defineAccessor",
          loc: this.fresh.loc(),
          obj: o,
          key,
          ...(g ? { getter: g } : {}),
          ...(s ? { setter: s } : {}),
        };
        return this.letE(t, rhs, cont());
      }),
    );
  }

  /**
   * Build a lambda atom: fresh param names, body compiled in the extended scope.
   * `dialect` carries the EchoJS/old-esprima extras riding on the function node:
   * a `defaults` array parallel to `params` and a trailing `rest` identifier
   * (in that dialect, params themselves are always plain Identifiers).
   */
  private compileFunction(
    params: ReadonlyArray<Pattern>,
    body: BlockStatement | EExpr,
    scope: Scope,
    info: LambdaInfo,
    isArrow = false,
    dialect: OldFunctionDialect = {},
  ): AExp {
    // Allocate the lambda's loc *first* so its body's `ret`s can be attributed to
    // it as they are compiled.
    const lamLoc = this.fresh.loc();
    const savedOwner = this.currentOwner;
    const savedThisOwner = this.currentThisOwner;
    this.currentOwner = lamLoc;
    // A regular function binds its own `this` (named for this lambda); an arrow
    // inherits the enclosing function's `this` lexically.
    if (!isArrow) this.currentThisOwner = lamLoc;

    const inner = new Map(scope);
    const srcNames: string[] = [];
    // EchoJS post-desugar trees keep a trailing `...rest` in `params` as a
    // RestElement (DesugarDestructuring leaves it in place — EIR lowers it
    // natively); the old-esprima dialect carries it as the `rest` field
    // instead. Peel a trailing RestElement off and treat both identically.
    let positional = params;
    let restId: Identifier | null = dialect.rest ?? null;
    const lastParam = params[params.length - 1];
    if (!restId && lastParam?.type === "RestElement") {
      if (lastParam.argument.type !== "Identifier")
        throw new NormalizeError("a rest parameter target must be a plain name.");
      restId = lastParam.argument;
      positional = params.slice(0, -1);
    }
    // A pattern parameter (ObjectPattern/ArrayPattern) becomes a synthetic
    // positional param whose destructuring reads are prologue-wrapped around
    // the body (after the whole-pattern default, matching EIR order).
    const patternParams: Array<{ pattern: Pattern; unique: Name }> = [];
    const uniqueParams = positional.map((p) => {
      if (p.type === "Identifier") {
        const u = this.fresh.name(p.name);
        this.mapNode(p, u);
        inner.set(p.name, u);
        srcNames.push(p.name);
        return u;
      }
      if (p.type === "ObjectPattern" || p.type === "ArrayPattern") {
        const u = this.fresh.name("pat");
        for (const n of patternNames(p)) inner.set(n, this.fresh.name(n));
        patternParams.push({ pattern: p, unique: u });
        srcNames.push("<pattern>");
        return u;
      }
      throw new NormalizeError("only plain identifier or destructuring-pattern parameters are supported.");
    });
    // The rest parameter is in scope in the body (and in later defaults), but
    // the machine binds only declared params (extra arguments are dropped), so
    // the rest array's *contents* are not modeled: bind it to an array whose
    // element bucket is ⊤ — the right type tag, unknown contents — rather than
    // reject the function, and record the degradation so it is visible.
    const rest = restId;
    let restUnique: Name | null = null;
    if (rest) {
      restUnique = this.fresh.name(rest.name);
      this.mapNode(rest, restUnique);
      inner.set(rest.name, restUnique);
      this.degradedBindings.push({
        name: rest.name,
        reason: "rest parameter — bound to an array of unknown (⊤) contents; the arguments it would collect are not tracked individually",
        span: spanOf(rest),
      });
    }
    let coreBody =
      body.type === "BlockStatement"
        ? this.normStmts(body.body, inner, () => this.retE(this.litA(litUndef)))
        : this.normAtom(body, inner, (a) => this.retE(a));

    // Destructure pattern params (innermost wrap: runs after defaults, before
    // the body — the whole-pattern default in `defaults[i]` applies to the
    // synthetic param, then the pattern decomposes whatever value it holds).
    // Wrapping from the last pattern inward keeps left-to-right read order.
    for (let i = patternParams.length - 1; i >= 0; i--) {
      const pp = patternParams[i]!;
      coreBody = this.bindPattern(pp.pattern, this.varA(pp.unique), inner, coreBody);
    }

    // Old-esprima `defaults`: a param that arrived `undefined` takes its
    // default, evaluated left to right in the function scope (so a later
    // default may reference an earlier param) — matching EchoJS EIR lowering.
    // Wrapping from the last default inward makes the first one outermost.
    const defaults = dialect.defaults ?? [];
    for (let i = Math.min(defaults.length, uniqueParams.length) - 1; i >= 0; i--) {
      const dflt = defaults[i];
      if (!dflt) continue;
      const pu = uniqueParams[i]!;
      const isUndef = this.fresh.name();
      const takeDefault = this.normAtom(dflt, inner, (dv) =>
        this.letE(this.fresh.name(), { tag: "setVar", loc: this.fresh.loc(), name: pu, val: dv }, coreBody),
      );
      coreBody = this.letE(
        isUndef,
        { tag: "bin", loc: this.fresh.loc(), op: "===", l: this.varA(pu), r: this.litA(litUndef) },
        this.ifE(this.varA(isUndef), takeDefault, coreBody),
      );
    }
    if (restUnique && rest) {
      const restLoc = this.fresh.loc();
      this.siteSpans.set(restLoc, spanOf(rest));
      // An array of unknown contents AND unknown length (the machine pins an
      // array literal's `length` to its element count — join it up to ⊤, or
      // `r.length` would read as the constant 1).
      coreBody = this.letE(
        restUnique,
        { tag: "array", loc: restLoc, elems: [this.litA(litTop)] },
        this.letE(
          this.fresh.name(),
          { tag: "put", loc: this.fresh.loc(), obj: this.varA(restUnique), key: "length", val: this.litA(litTop) },
          coreBody,
        ),
      );
    }

    this.currentOwner = savedOwner;
    this.currentThisOwner = savedThisOwner;
    this.lambdaInfo.set(lamLoc, info);
    this.lambdaParams.set(lamLoc, srcNames);
    return { tag: "lam", loc: lamLoc, params: uniqueParams, body: coreBody };
  }

  /**
   * Decompose `pattern` against the value held in `src`, binding every
   * identifier leaf to its (pre-registered via {@link patternNames}) unique
   * name in `scope`, then continue with `cont`. Object patterns become
   * property reads; array patterns become index reads (the smashed element
   * bucket, so a read is element-join ⊔ undefined); pattern defaults use the
   * same `=== undefined` rule as parameter defaults (evaluated in `scope`,
   * left to right); an array rest binds a fresh array carrying the source's
   * per-iteration element approximation. `cont` is shared across default
   * branches — the established shared-continuation idiom.
   */
  private bindPattern(pattern: Pattern, src: AExp, scope: Scope, cont: Expr): Expr {
    switch (pattern.type) {
      case "Identifier": {
        const unique = scope.get(pattern.name);
        if (!unique)
          throw new NormalizeError(`internal: pattern name \`${pattern.name}\` was not pre-registered.`);
        this.mapNode(pattern, unique); // pattern leaf ↔ its Identifier node
        return this.letE(unique, { tag: "atom", loc: this.fresh.loc(), atom: src }, cont);
      }
      case "AssignmentPattern": {
        // `p = dflt` inside a pattern: the leaf takes the default when the
        // incoming value is `undefined` (the parameter-default rule).
        const isUndef = this.fresh.name();
        const takeDefault = this.normAtom(pattern.right as EExpr, scope, (dv) =>
          this.bindPattern(pattern.left, dv, scope, cont),
        );
        return this.letE(
          isUndef,
          { tag: "bin", loc: this.fresh.loc(), op: "===", l: src, r: this.litA(litUndef) },
          this.ifE(this.varA(isUndef), takeDefault, this.bindPattern(pattern.left, src, scope, cont)),
        );
      }
      case "ObjectPattern": {
        const props = pattern.properties;
        const go = (i: number): Expr => {
          if (i >= props.length) return cont;
          const p = props[i]!;
          if (p.type !== "Property")
            throw new NormalizeError("object rest patterns (`{...r}`) are not supported.");
          if (p.computed) throw new NormalizeError("computed keys in object patterns are not supported.");
          const key = propKeyName(p.key as Node);
          const t = this.fresh.name();
          const getLoc = this.fresh.loc();
          this.siteSpans.set(getLoc, spanOf(p as unknown as Node));
          return this.letE(
            t,
            { tag: "get", loc: getLoc, obj: src, key },
            this.bindPattern(p.value as Pattern, this.varA(t), scope, go(i + 1)),
          );
        };
        return go(0);
      }
      case "ArrayPattern": {
        // EchoJS dialect note: a declaration-position rest parses as
        // SpreadElement (assignment-position as RestElement) — accept both.
        const elems = pattern.elements as ReadonlyArray<
          (Pattern | { type: "SpreadElement" | "RestElement"; argument: Pattern }) | null
        >;
        const go = (i: number): Expr => {
          if (i >= elems.length) return cont;
          const el = elems[i];
          if (!el) return go(i + 1); // elision (hole)
          if (el.type === "SpreadElement" || el.type === "RestElement") {
            const target = el.argument;
            if (target.type !== "Identifier")
              throw new NormalizeError("an array-pattern rest target must be a plain name.");
            const unique = scope.get(target.name);
            if (!unique)
              throw new NormalizeError(`internal: pattern name \`${target.name}\` was not pre-registered.`);
            this.mapNode(target, unique);
            // Bind an array whose elements are the source's per-iteration
            // element approximation (a sound per-element over-approximation
            // of the tail; untracked sources degrade to ⊤ and are counted).
            // Its `length` is unknown — join it up to ⊤ so it never reads as
            // the constant 1 the allocation would otherwise pin.
            const elName = this.fresh.name("elem");
            return this.letE(
              elName,
              { tag: "iterElem", loc: this.fresh.loc(), obj: src },
              this.letE(
                unique,
                { tag: "array", loc: this.fresh.loc(), elems: [this.varA(elName)] },
                this.letE(
                  this.fresh.name(),
                  { tag: "put", loc: this.fresh.loc(), obj: this.varA(unique), key: "length", val: this.litA(litTop) },
                  go(i + 1),
                ),
              ),
            );
          }
          const t = this.fresh.name();
          return this.letE(
            t,
            { tag: "getDyn", loc: this.fresh.loc(), obj: src, keyExpr: this.litA(litNum(i)) },
            this.bindPattern(el as Pattern, this.varA(t), scope, go(i + 1)),
          );
        };
        return go(0);
      }
      default:
        throw new NormalizeError(`unsupported pattern: ${(pattern as { type: string }).type}`);
    }
  }
}

// --- helpers ---------------------------------------------------------------

/** A synthetic `null` literal (for `Object.create()` with no argument). */
function nullLiteral(): EExpr {
  return { type: "Literal", value: null } as EExpr;
}

/** A synthetic `true` literal (for an absent loop test, e.g. `for (;;)`). */
function trueLiteral(): EExpr {
  return { type: "Literal", value: true } as EExpr;
}

/** The string value of a string-literal node, else `null`. */
function literalString(node: Node): string | null {
  if (node.type === "Literal" && typeof (node as { value: unknown }).value === "string")
    return (node as { value: string }).value;
  return null;
}

/** Look up a named field's value expression in a literal descriptor object. */
function descriptorField(obj: Node & { type: "ObjectExpression" }, name: string): EExpr | null {
  for (const p of (obj as { properties: ReadonlyArray<Node> }).properties) {
    if (p.type !== "Property" || (p as { computed?: boolean }).computed) continue;
    const prop = p as { key: Node; value: Node };
    if (propKeyNameSafe(prop.key) === name) return prop.value as EExpr;
  }
  return null;
}

/** Like `propKeyName` but returns `null` instead of throwing (for descriptor scans). */
function propKeyNameSafe(key: Node): string | null {
  if (key.type === "Identifier") return (key as { name: string }).name;
  if (key.type === "Literal") {
    const v = (key as { value: unknown }).value;
    if (typeof v === "string" || typeof v === "number") return String(v);
  }
  return null;
}

/**
 * Every identifier a pattern binds (object/array/default/rest, any nesting) —
 * used to pre-register unique names before {@link Normalizer.bindPattern}
 * decomposes the pattern. Unsupported leaves are ignored here; `bindPattern`
 * rejects them with a precise error when it reaches them.
 */
// --- syntactic hoisting scan (see normStmts) --------------------------------
//
// A deliberately cheap, OVER-approximate ESTree walk: it answers "might this
// statement list's later-declared variable be referenced from inside a closure
// created at or before its declaration?" — the shape whose writes the machine
// would otherwise silently drop. Over-approximation only costs precision (the
// captured name's nodeTypes join widens with the hoisted pre-binding's
// `undefined`), never soundness.

type AnyNode = { readonly type?: string } & Record<string, unknown>;

const FUNCTION_NODE_TYPES = new Set(["FunctionDeclaration", "FunctionExpression", "ArrowFunctionExpression"]);

/** One candidate child (or array of candidates): visit every element that
 * looks like a node.  The same filter the generic walk applies per key. */
function visitMaybe(v: unknown, visit: (c: AnyNode) => void): void {
  if (Array.isArray(v)) {
    for (const c of v) if (c && typeof c === "object" && typeof (c as AnyNode).type === "string") visit(c as AnyNode);
  } else if (v && typeof v === "object" && typeof (v as AnyNode).type === "string") {
    visit(v as AnyNode);
  }
}

/** The generic child walk: every enumerable property that holds a node (or
 * array of nodes).  The soundness backstop for node types the fast walk
 * below does not enumerate — over-approximation must never turn into
 * under-approximation through a missing key. */
function walkChildrenGeneric(n: AnyNode, visit: (c: AnyNode) => void): void {
  for (const key of Object.keys(n)) {
    if (key === "loc" || key === "range") continue;
    visitMaybe(n[key], visit);
  }
}

/** Recurse into every ESTree child of `n` (arrays and single nodes).
 *
 * The common node types dispatch through literal-key accesses (compiled,
 * these are monomorphic per-arm property loads; the generic walk's
 * `Object.keys` + dynamic reads were the hottest property traffic in the
 * whole self-hosted analysis).  Key order matches the builders'
 * property-creation order — the walk feeds insertion-ordered Sets whose
 * order is observable downstream (degradation accounting).  Types not
 * listed — including dialect nodes with unusual fields — take the generic
 * walk unchanged. */
function walkChildren(n: AnyNode, visit: (c: AnyNode) => void): void {
  const a = n as Record<string, unknown>;
  switch (n.type) {
    case "Identifier":
    case "Literal":
    case "ThisExpression":
    case "EmptyStatement":
    case "DebuggerStatement":
      return;
    case "ExpressionStatement":
      visitMaybe(a.expression, visit);
      return;
    case "BlockStatement":
    case "Program":
      visitMaybe(a.body, visit);
      return;
    case "MemberExpression":
      visitMaybe(a.object, visit);
      visitMaybe(a.property, visit);
      return;
    case "CallExpression":
    case "NewExpression":
      visitMaybe(a.callee, visit);
      visitMaybe(a.arguments, visit);
      return;
    case "BinaryExpression":
    case "LogicalExpression":
    case "AssignmentExpression":
      visitMaybe(a.left, visit);
      visitMaybe(a.right, visit);
      return;
    case "ConditionalExpression":
    case "IfStatement":
      visitMaybe(a.test, visit);
      visitMaybe(a.consequent, visit);
      visitMaybe(a.alternate, visit);
      return;
    case "VariableDeclaration":
      visitMaybe(a.declarations, visit);
      return;
    case "VariableDeclarator":
      visitMaybe(a.id, visit);
      visitMaybe(a.init, visit);
      return;
    case "ReturnStatement":
    case "ThrowStatement":
    case "UnaryExpression":
    case "UpdateExpression":
    case "YieldExpression":
    case "AwaitExpression":
    case "SpreadElement":
    case "RestElement":
      visitMaybe(a.argument, visit);
      return;
    case "FunctionDeclaration":
    case "FunctionExpression":
    case "ArrowFunctionExpression":
      // old-esprima/echojs dialect: parallel `defaults` and a trailing
      // `rest` identifier ride beside `params`
      visitMaybe(a.id, visit);
      visitMaybe(a.params, visit);
      visitMaybe(a.defaults, visit);
      visitMaybe(a.rest, visit);
      visitMaybe(a.body, visit);
      return;
    case "ObjectExpression":
    case "ObjectPattern":
      visitMaybe(a.properties, visit);
      return;
    case "Property":
      visitMaybe(a.key, visit);
      visitMaybe(a.value, visit);
      return;
    case "ArrayExpression":
    case "ArrayPattern":
      visitMaybe(a.elements, visit);
      return;
    case "SequenceExpression":
      visitMaybe(a.expressions, visit);
      return;
    case "ForStatement":
      visitMaybe(a.init, visit);
      visitMaybe(a.test, visit);
      visitMaybe(a.update, visit);
      visitMaybe(a.body, visit);
      return;
    case "ForInStatement":
    case "ForOfStatement":
      visitMaybe(a.left, visit);
      visitMaybe(a.right, visit);
      visitMaybe(a.body, visit);
      return;
    case "WhileStatement":
      visitMaybe(a.test, visit);
      visitMaybe(a.body, visit);
      return;
    case "DoWhileStatement":
      // creation order puts body before test — the generic walk visited
      // it that way, and Set insertion order is observable downstream
      visitMaybe(a.body, visit);
      visitMaybe(a.test, visit);
      return;
    case "SwitchStatement":
      visitMaybe(a.discriminant, visit);
      visitMaybe(a.cases, visit);
      return;
    case "SwitchCase":
      visitMaybe(a.test, visit);
      visitMaybe(a.consequent, visit);
      return;
    case "LabeledStatement":
      visitMaybe(a.label, visit);
      visitMaybe(a.body, visit);
      return;
    case "BreakStatement":
    case "ContinueStatement":
      visitMaybe(a.label, visit);
      return;
    case "TryStatement":
      // both dialects: acorn {block, handler, finalizer}; old-esprima
      // adds parallel handlers/guardedHandlers arrays
      visitMaybe(a.block, visit);
      visitMaybe(a.handlers, visit);
      visitMaybe(a.handler, visit);
      visitMaybe(a.guardedHandlers, visit);
      visitMaybe(a.finalizer, visit);
      return;
    case "CatchClause":
      visitMaybe(a.param, visit);
      visitMaybe(a.body, visit);
      return;
    default:
      walkChildrenGeneric(n, visit);
  }
}

/** Every identifier NAME referenced under `root`, excluding non-computed member
 * properties and non-computed object keys (field names, not variable refs). */
function identifierRefs(root: AnyNode, out: Set<string>): void {
  const visit = (n: AnyNode): void => {
    if (n.type === "Identifier") {
      out.add(n["name"] as string);
      return;
    }
    if (n.type === "MemberExpression" && !n["computed"]) {
      const obj = n["object"] as AnyNode | undefined;
      if (obj && typeof obj.type === "string") visit(obj);
      return;
    }
    if (n.type === "Property" && !n["computed"]) {
      const val = n["value"] as AnyNode | undefined;
      if (val && typeof val.type === "string") visit(val);
      return;
    }
    walkChildren(n, visit);
  };
  visit(root);
}

/**
 * For each function-creating subtree within `root` (function declarations and
 * expressions, arrows — object-literal methods are FunctionExpressions), add
 * every identifier referenced inside it to `out`, minus that function's own
 * parameter names (a cheap shadow filter; inner locals/params of NESTED
 * functions are not filtered — over-approximate by design).
 */
function functionSubtreeRefs(
  root: AnyNode,
  out: Set<string>,
  memo?: Map<AnyNode, ReadonlySet<string>>,
): void {
  const visit = (n: AnyNode): void => {
    if (FUNCTION_NODE_TYPES.has(n.type ?? "")) {
      // The filtered ref set is a pure function of the fn subtree, and
      // enclosing statement lists re-scan the same fn nodes once per
      // statement position — memo on node identity collapses the
      // rescans (same computation, same insertion order).
      const hit = memo?.get(n);
      if (hit !== undefined) {
        for (const r of hit) out.add(r);
        return;
      }
      const params = new Set<string>();
      // Binding names only (patternNames walks pattern LEAVES — an ES6 default's
      // right-hand side is an expression, not a binding, and must stay in refs).
      for (const p of (n["params"] as AnyNode[] | undefined) ?? []) {
        for (const nm of patternNames(p as unknown as Node)) params.add(nm);
      }
      // Old-esprima/echojs dialect: a trailing `rest` identifier is a parameter.
      const restP = n["rest"] as AnyNode | undefined;
      if (restP?.type === "Identifier") params.add(restP["name"] as string);
      const refs = new Set<string>();
      const body = n["body"] as AnyNode | undefined;
      if (body && typeof body.type === "string") identifierRefs(body, refs);
      // Old-esprima/echojs dialect (review R2): `defaults` expressions evaluate
      // in the function's scope — scan them like the body. Unreachable via
      // acorn (ES6 defaults are AssignmentPatterns inside `params`, already
      // covered), but echojs post-desugar trees carry the parallel array.
      for (const d of (n["defaults"] as (AnyNode | null)[] | undefined) ?? []) {
        if (d && typeof d.type === "string") identifierRefs(d, refs);
      }
      const filtered = new Set<string>();
      for (const r of refs) if (!params.has(r)) filtered.add(r);
      memo?.set(n, filtered);
      for (const r of filtered) out.add(r);
      return;
    }
    walkChildren(n, visit);
  };
  visit(root);
}

/** `var`-kind declaration names in NESTED positions under `root` (inside
 * blocks/ifs/loops/for-heads — not inside nested functions, whose vars belong
 * to their own scope). Used for the visible-degradation accounting of
 * unmodeled function-scope hoisting. */
function nestedVarNames(root: AnyNode, out: Map<string, AnyNode>): void {
  const visit = (n: AnyNode): void => {
    if (FUNCTION_NODE_TYPES.has(n.type ?? "")) return;
    if (n.type === "VariableDeclaration" && n["kind"] === "var") {
      for (const d of (n["declarations"] as AnyNode[] | undefined) ?? []) {
        const id = d["id"] as AnyNode | undefined;
        if (id?.type === "Identifier" && !out.has(id["name"] as string)) out.set(id["name"] as string, n);
      }
      return;
    }
    walkChildren(n, visit);
  };
  visit(root);
}

function patternNames(p: Node): string[] {
  const out: string[] = [];
  const walkP = (n: Node | null | undefined): void => {
    if (!n) return;
    switch (n.type) {
      case "Identifier":
        out.push((n as { name: string }).name);
        return;
      case "ObjectPattern":
        for (const pr of (n as unknown as { properties: Node[] }).properties) {
          if (pr.type === "Property") walkP((pr as unknown as { value: Node }).value);
          else walkP((pr as unknown as { argument?: Node }).argument);
        }
        return;
      case "ArrayPattern":
        for (const el of (n as unknown as { elements: (Node | null)[] }).elements) walkP(el);
        return;
      case "AssignmentPattern":
        return walkP((n as unknown as { left: Node }).left);
      case "RestElement":
      case "SpreadElement":
        return walkP((n as unknown as { argument: Node }).argument);
      default:
        return;
    }
  };
  walkP(p);
  return out;
}

/** Extract a static property name from an object-literal key node. */
function propKeyName(key: Node): string {
  if (key.type === "Identifier") return key.name;
  if (key.type === "Literal") {
    const v = (key as { value: unknown }).value;
    if (typeof v === "string" || typeof v === "number") return String(v);
  }
  throw new NormalizeError("only identifier or string/number object keys are supported.");
}

/** Extract a static property name from a (non-computed) member access. */
function memberKeyName(m: { computed: boolean; property: Node }): string {
  if (m.computed) throw new NormalizeError("computed member access (`obj[e]`) is not supported.");
  if (m.property.type === "Identifier") return m.property.name;
  throw new NormalizeError("only `obj.name` member access is supported.");
}

function fnName(f: FunctionDeclaration): string {
  if (!f.id) throw new NormalizeError("function declarations must be named.");
  return f.id.name;
}

/** Which unmodeled function kind this is (`async` covers async generators),
 * or null for a plain function the normalizer compiles. */
function unmodeledFnKind(f: {
  async?: boolean | undefined;
  generator?: boolean | undefined;
}): "async" | "generator" | null {
  if (f.async) return "async";
  if (f.generator) return "generator";
  return null;
}

function literal(e: Node): Lit {
  const withExtras = e as Node & { bigint?: string; regex?: unknown; value: unknown };
  if (withExtras.regex) throw new NormalizeError("regular-expression literals are not supported.");
  // ESTree carries the digits in `bigint` (`value` may be null after a JSON
  // round trip); the concrete domain evaluates bigints exactly, the abstract
  // domain widens them to ⊤ (it has no bigint constituent).
  if (withExtras.bigint !== undefined) return litBigint(BigInt(withExtras.bigint));
  const v = withExtras.value;
  if (typeof v === "number") return litNum(v);
  if (typeof v === "string") return litStr(v);
  if (typeof v === "boolean") return litBool(v);
  if (v === null) return litNull;
  throw new NormalizeError(`unsupported literal value: ${String(v)}`);
}

const BIN_OPS: Record<string, BinOp> = {
  "+": "+", "-": "-", "*": "*", "/": "/", "%": "%", "**": "**",
  "<": "<", "<=": "<=", ">": ">", ">=": ">=",
  "===": "===", "!==": "!==", "==": "==", "!=": "!=",
  "&": "&", "|": "|", "^": "^", "<<": "<<", ">>": ">>", ">>>": ">>>",
  instanceof: "instanceof", in: "in",
};

function binOp(op: string): BinOp {
  const mapped = BIN_OPS[op];
  if (!mapped) throw new NormalizeError(`unsupported binary operator \`${op}\`.`);
  return mapped;
}

const UN_OPS: Record<string, UnOp> = {
  "-": "-", "+": "+", "!": "!", "~": "~", typeof: "typeof", void: "void",
};

function unOp(op: string): UnOp {
  const mapped = UN_OPS[op];
  if (!mapped) throw new NormalizeError(`unsupported unary operator \`${op}\`.`);
  return mapped;
}
