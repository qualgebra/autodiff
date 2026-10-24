# Performance investigation (2026-10-24)

This branch adds opt-in instrumentation and experimental search variants to
`Autodiff/`, plus small probe files in this directory. With no environment
variables set, behaviour is the original except for the B8 fix below.

## Running

Probe files are not part of any `lean_lib`; run them directly:

    lake build Autodiff
    AD_STATS=1 lake env lean investigation/Stats.lean
    AD_STATS=1 AD_MODE=ch lake env lean investigation/Stats.lean
    AD_RECS=/tmp/recs.csv lake env lean investigation/Stats2.lean   # per-attempt CSV
    lake env lean investigation/Prof.lean                           # profiler
    lake env lean investigation/Diag.lean                           # unfolding diagnostics

Environment variables (see the comment above `difftac` in `Autodiff/FindTheorems.lean`):

| Variable | Effect |
|---|---|
| `AD_STATS=1` | log apply counts and timings per `difftac` call |
| `AD_RECS=<file>` | append `theorem,success,nanos` per apply attempt |
| `AD_MODE=<flags>` | `c` skip catch-all theorems, `h` filter by head symbol, `r` reducible, `i` instances transparency |
| `AD_KEEPBUG=1` | restore the original `getFullTargetType` call (B8) |
| `AD_DIRECT=1` | add the `CDeriv` with `addDecl` instead of delab/re-elab (incomplete, see B9) |

## Findings (on `test0` from `Test/autodiff_debug.lean`, restricted domain)

- Time is all in `difftac`: ~0.7 s for a universal-domain function, ~2.9 s for `test0`.
- The theorem DB has 118 theorems; building it takes ~1.1 s.
- 2805 `apply` attempts, 2692 failed, costing 2.47 s (~85% of the tactic).
- `set_option diagnostics true`: failed matches unfold `HasDerivAt` / `HasDerivAtFilter`
  ~9k times each, down to filters and real-number internals
  (`Complex.cos/sin/tan`, `Complex.mulAux`, `CauSeq`, `Classical.choice`).
- Catch-all theorems (conclusion `HasDerivAt f …` with `f` a variable) apply to every goal and fail
  below: `HasFPowerSeriesAt.hasDerivAt`, `HasDerivAt.of_isLittleO`, `HasStrictDerivAt.hasDerivAt`,
  `congr_deriv`, `congr_of_eventuallyEq`, `of_local_left_inverse`, `DifferentiableOn.hasDerivAt`,
  `HasFDerivAt.hasDerivAt`, and `CDeriv.proof`.
- The search relies on deep unfolding: `3/x` via `const_mul` + `hasDerivAt_inv` (`/` unfolded to
  `* ⁻¹`); `x ^ 1` via `hasDerivAt_const_mul` after unfolding `npow` to `Real.one * x`.

### B8: `getFullTargetType` bug (fixed on this branch)

In the domain-constraint branch, `let _ ← getFullTargetType` (result unused) calls
`withMainContext` → `getMainGoal`, which throws once the preceding `HasDerivAt` subgoals are
solved. Any theorem whose domain premise follows its `HasDerivAt` premises therefore always
failed (Mathlib's `HasDerivAt.div`, `fun_div`, `HasDerivAt.log`) — likely why `log'`/`tan'`
were restated with swapped premises. The call is now skipped unless `AD_KEEPBUG` is set.

Consequence: 6 `#guard_msgs` outputs in `Test/autodiff_debug.lean` now differ (different,
valid derivations), so `lake test` fails until the expected outputs are updated.

### B9: delab → re-elab round trip (not fixed)

`buildDomainExpr` uses the constant `x` instead of a bound variable and `buildDomainSelector`
uses constant `_` for `And.left/right` implicits; both only work because the final term is
pretty-printed and re-parsed. `↑n` casts (e.g. from `hasDerivAt_pow`) do not survive the round
trip. `AD_DIRECT` fixes the domain but still fails on the `_` selectors.

### Experiments

| Variant | `test0` |
|---|---|
| original | 2805 attempts, tactic 2.9 s |
| B8 fixed | 1970 attempts, tactic 1.9 s |
| B8 + `c` | 860 attempts; all functions differentiated |
| B8 + `ch` | 84 attempts, tactic 0.19 s (~15×); derivations found, but `↑n` outputs then fail B9 |
| `r` / `i` | some functions no longer differentiable |

## Suggested next steps

1. Keep B8 fixed; update the test outputs.
2. Fix B9: build proper `Expr`s and `addDecl` directly (kernel-checked, no round trip).
3. Drop catch-all theorems automatically instead of the hand-written blacklists.
4. Index theorems by head symbol (`DiscrTree`; `ThmDB.lookup` already takes the key).
5. Build the DB once per benchmark process (timed runs currently restart from the post-import
   state and rebuild it), then re-run the benchmark and revisit the heartbeat limit.
