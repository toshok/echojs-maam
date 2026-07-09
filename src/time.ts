/**
 * Abstract time — the single knob that controls context-sensitivity of a CFA.
 *
 * Transliteration of MAAM's `Time` class. An address is `(name, time)`, so the
 * granularity of `Time` decides how many distinct addresses a variable can
 * have, i.e. how much calling-context the analysis keeps apart. The interpreter
 * only ever calls `tzero` (initial) and `tick` (advance on a call), so any
 * lawful instance plugs in unchanged — this is the whole "swap the abstraction,
 * reuse the interpreter" story for context.
 *
 * `Ctx` is the type of a context increment (here a program location / call
 * site). Different instances truncate the history of contexts differently:
 *
 *  - {@link concreteTime} (`Cτ`)  — keep the entire unbounded history ⇒ *concrete*.
 *  - {@link kCFATime} (`Kτ k`)   — keep only the most recent `k` ⇒ *k-CFA*.
 *  - {@link zeroCFATime} (`Zτ`)  — keep nothing ⇒ *0-CFA* (context-insensitive).
 */

import type { Keyable } from "./data/key.js";
import { canonicalJson } from "./data/key.js";

/** A time value is a (possibly truncated) list of context increments, newest first. */
export type Time<Ctx> = ReadonlyArray<Ctx>;

/**
 * A time abstraction: the initial time and how a call site advances it. Carries
 * a {@link Keyable} so times can key stores/addresses structurally.
 */
export interface TimeDict<Ctx> {
  readonly name: string;
  readonly tzero: Time<Ctx>;
  readonly tick: (ctx: Ctx, t: Time<Ctx>) => Time<Ctx>;
  readonly key: Keyable<Time<Ctx>>;
  /**
   * True when every address is guaranteed to name exactly one concrete entity
   * (concrete, unbounded time), so mutable object writes may **strong-update**.
   * False for k-CFA/0-CFA, where an address summarizes many objects and writes
   * must **weak-update** (join) to stay sound.
   */
  readonly singletonAddrs: boolean;
}

const timeKey = <Ctx>(kc: Keyable<Ctx>): Keyable<Time<Ctx>> => ({
  key: (t) => t.map(kc.key).join("·"),
});

/**
 * Concrete time (`Cτ`): remember the entire call history. Addresses are never
 * merged, so this recovers a *concrete* interpreter (modulo store-allocated
 * values). Only terminates on programs that terminate.
 */
export function concreteTime<Ctx>(kc: Keyable<Ctx>): TimeDict<Ctx> {
  return {
    name: "concrete (Cτ)",
    tzero: [],
    tick: (ctx, t) => [ctx, ...t],
    key: timeKey(kc),
    singletonAddrs: true,
  };
}

/**
 * k-CFA time (`Kτ k`): remember only the most recent `k` call sites. Finitely
 * many times ⇒ finitely many addresses ⇒ a terminating, sound analysis with
 * `k` levels of calling-context sensitivity.
 */
export function kCFATime<Ctx>(k: number, kc: Keyable<Ctx>): TimeDict<Ctx> {
  if (k < 0 || !Number.isInteger(k)) throw new Error(`k-CFA needs k ≥ 0 integer, got ${k}`);
  return {
    name: `${k}-CFA (Kτ ${k})`,
    tzero: [],
    tick: (ctx, t) => [ctx, ...t].slice(0, k),
    key: timeKey(kc),
    singletonAddrs: false,
  };
}

/**
 * 0-CFA time (`Zτ`): remember nothing. Every allocation of a variable shares one
 * address; the cheapest, least precise, context-insensitive analysis. This is
 * the `k = 0` special case, provided by name for clarity.
 */
export function zeroCFATime<Ctx>(kc: Keyable<Ctx>): TimeDict<Ctx> {
  return {
    name: "0-CFA (Zτ)",
    tzero: [],
    tick: () => [],
    key: timeKey(kc),
    singletonAddrs: false,
  };
}

/** Convenience: a {@link Keyable} for arbitrary context increments via canonical JSON. */
export function jsonCtxKey<Ctx>(): Keyable<Ctx> {
  return { key: (c) => canonicalJson(c) };
}
