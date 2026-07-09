/**
 * Surface syntax of the restricted JavaScript dialect — **ESTree**.
 *
 * The dialect's AST is standard [ESTree](https://github.com/estree/estree), the
 * same format the host compiler produces (via esprima). We do not define our own
 * node types; we re-export the `estree` types the front-end consumes and add a
 * couple of helpers (a generic child-walker and a span accessor). Parsing for
 * tests/demos is done with acorn (`parse.ts`), but any ESTree `Program` — however
 * produced — can be fed straight to {@link analyze}.
 *
 * Three constructs are part of ESTree but **not** the analyzable dialect; the
 * validator (`restrictions.ts`) rejects them: `eval(...)`, `new Function(...)`,
 * and `with (...) { ... }`.
 */

import type { Node, Program } from "estree";

export type {
  Node,
  Program,
  Statement,
  ModuleDeclaration,
  Expression,
  Pattern,
  VariableDeclaration,
  VariableDeclarator,
  FunctionDeclaration,
  FunctionExpression,
  ArrowFunctionExpression,
  ReturnStatement,
  IfStatement,
  ExpressionStatement,
  BlockStatement,
  WithStatement,
  CallExpression,
  NewExpression,
  MemberExpression,
  BinaryExpression,
  LogicalExpression,
  UnaryExpression,
  ConditionalExpression,
  Identifier,
  Literal,
} from "estree";

/** A half-open source span `[start, end)` in code-unit offsets. */
export interface Span {
  readonly start: number;
  readonly end: number;
}

/**
 * The source span of a node. ESTree carries positions in the optional `range`
 * field (acorn emits it when `ranges: true`); we fall back to `{0,0}` if a tree
 * was produced without ranges.
 */
export function spanOf(node: Node): Span {
  const r = (node as Node & { range?: [number, number] }).range;
  if (r) return { start: r[0], end: r[1] };
  const s = node as Node & { start?: number; end?: number };
  if (typeof s.start === "number" && typeof s.end === "number") return { start: s.start, end: s.end };
  return { start: 0, end: 0 };
}

/** Is `x` an ESTree node (has a string `type` tag)? */
export function isNode(x: unknown): x is Node {
  return typeof x === "object" && x !== null && typeof (x as { type?: unknown }).type === "string";
}

/**
 * Yield every node in the tree rooted at `root`, pre-order. A generic structural
 * walk: it descends into every child that is itself a node or an array of nodes,
 * so it needs no per-node-type knowledge and is robust to the full ESTree grammar.
 */
export function* walk(root: Node): Generator<Node> {
  yield root;
  for (const key of Object.keys(root)) {
    if (key === "type" || key === "loc" || key === "range" || key === "start" || key === "end") continue;
    const child = (root as unknown as Record<string, unknown>)[key];
    if (isNode(child)) {
      yield* walk(child);
    } else if (Array.isArray(child)) {
      for (const el of child) if (isNode(el)) yield* walk(el);
    }
  }
}

/** Convenience: walk a whole program. */
export function walkProgram(program: Program): Generator<Node> {
  return walk(program);
}
