/**
 * A convenience parser for tests and demos, built on **acorn**.
 *
 * This is the *only* module that depends on acorn, and nothing in the analysis
 * pipeline imports it — the analyzer consumes ESTree, so the host compiler feeds
 * its own tree (e.g. from esprima) directly to {@link analyze} and never touches
 * this file. It exists so the test suite and `npm run demo` can turn source
 * strings into ESTree without pulling a parser into the library's public graph.
 *
 * acorn's node types are structurally ESTree; we parse with `ranges: true` so
 * `spanOf` can report accurate diagnostics, then present the result as the
 * `estree` types the rest of the code uses.
 */

import * as acorn from "acorn";
import type { Expression, Program } from "estree";

const OPTIONS: acorn.Options = {
  ecmaVersion: 2022,
  sourceType: "script",
  ranges: true,
  locations: true,
};

/**
 * Parse a whole program into an ESTree {@link Program}.
 *
 * We parse as a script by default (so non-strict constructs the dialect rejects
 * itself — e.g. `with` — reach the normalizer rather than dying in acorn's strict
 * check). Sources using `import`/`export` aren't valid scripts, so we retry them
 * as a module.
 */
export function parse(source: string): Program {
  try {
    return acorn.parse(source, OPTIONS) as unknown as Program;
  } catch {
    return acorn.parse(source, { ...OPTIONS, sourceType: "module" }) as unknown as Program;
  }
}

/** Parse a single expression (handy for tests). Requires it to consume all input. */
export function parseExpr(source: string): Expression {
  const node = acorn.parseExpressionAt(source, 0, OPTIONS) as unknown as Expression & {
    range?: [number, number];
  };
  const end = node.range?.[1] ?? source.length;
  if (source.slice(end).trim() !== "") {
    throw new SyntaxError(`unexpected trailing input after expression at offset ${end}`);
  }
  return node;
}
