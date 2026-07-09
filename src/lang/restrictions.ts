/**
 * The dialect's contract, enforced over ESTree.
 *
 * A sound whole-program control-flow analysis requires that the program text
 * *is* the program: nothing at runtime may synthesize new code or dynamically
 * rebind scope. This module rejects the three JavaScript constructs that would
 * break that assumption:
 *
 *   1. `eval(...)`          — runs an arbitrary string as code.
 *   2. `new Function(...)`  — builds a function from a string of code.
 *   3. `with (obj) { ... }` — resolves names against a runtime object.
 *
 * Also flagged: bare `Function(...)` calls, which behave like `new Function`.
 * Everything is reported (not thrown) so a compiler front-end can surface all
 * violations at once.
 */

import type { Node, Program, Span } from "./ast.js";
import { spanOf, walk } from "./ast.js";

/** A single dialect violation with the source span that triggered it. */
export interface Violation {
  readonly rule: "no-eval" | "no-new-function" | "no-function-constructor" | "no-with";
  readonly message: string;
  readonly span: Span;
}

/**
 * Scan a program and return every dialect violation. An empty array means the
 * program is a legal member of the restricted dialect.
 */
export function checkRestrictions(program: Program): Violation[] {
  const violations: Violation[] = [];
  for (const node of walk(program)) checkNode(node, violations);
  return violations;
}

/** Convenience: throw a {@link RestrictionError} if the program violates the dialect. */
export function assertRestrictions(program: Program): void {
  const violations = checkRestrictions(program);
  if (violations.length > 0) throw new RestrictionError(violations);
}

export class RestrictionError extends Error {
  constructor(readonly violations: Violation[]) {
    super(
      `restricted-JS dialect violated:\n` +
        violations.map((v) => `  • [${v.rule}] ${v.message}`).join("\n"),
    );
    this.name = "RestrictionError";
  }
}

function checkNode(n: Node, out: Violation[]): void {
  switch (n.type) {
    case "WithStatement":
      out.push({
        rule: "no-with",
        message: "`with` statements are not allowed: they make scope unresolvable at compile time.",
        span: spanOf(n),
      });
      break;
    case "CallExpression":
      if (n.callee.type === "Identifier") {
        if (n.callee.name === "eval") {
          out.push({
            rule: "no-eval",
            message: "`eval(...)` is not allowed: it executes arbitrary code generated at runtime.",
            span: spanOf(n),
          });
        } else if (n.callee.name === "Function") {
          out.push({
            rule: "no-function-constructor",
            message:
              "calling `Function(...)` is not allowed: it builds a function from a runtime code string.",
            span: spanOf(n),
          });
        }
      }
      break;
    case "NewExpression":
      if (n.callee.type === "Identifier" && n.callee.name === "Function") {
        out.push({
          rule: "no-new-function",
          message:
            "`new Function(...)` is not allowed: it builds a function from a runtime code string.",
          span: spanOf(n),
        });
      }
      break;
    default:
      break;
  }
}
