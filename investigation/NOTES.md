# Performance investigation (2026-10-24)

This branch adds opt-in instrumentation and experimental search variants to
`Autodiff/`, plus small probe files in this directory. With no environment
variables set, the search is the original one; B8 and B9 below are fixed.

## Running

Probe files are not part of any `lean_lib`; run them directly:

    lake build Autodiff
    AD_STATS=1 lake env lean investigation/Stats.lean
    AD_STATS=1 AD_LEGACY=1 lake env lean investigation/Stats.lean
    AD_RECS=/tmp/recs.csv lake env lean investigation/Stats2.lean   # per-attempt CSV
    lake env lean investigation/Prof.lean                           # profiler
    lake env lean investigation/Diag.lean                           # unfolding diagnostics

Environment variables (see the comment above `difftac` in `Autodiff/FindTheorems.lean`):

| Variable | Effect |
|---|---|
| `AD_STATS=1` | log apply counts and timings per `difftac` call |
| `AD_RECS=<file>` | append `theorem,success,nanos` per apply attempt |
| `AD_LEGACY=1` | original search: all theorems incl. catch-alls, no head index, hand-written blacklists |
| `AD_HEARTBEATS=<n>` | benchmark only: heartbeat limit (default 200000, Lean's default) |
| `AD_KEEPBUG=1` | restore the original `getFullTargetType` call (B8) |

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

### B9: delab → re-elab round trip (fixed on this branch)

Previously `buildDomainExpr` used the constant `x` instead of a bound variable and
`buildDomainSelector` used constant `_` for `And.left/right` implicits; both only worked
because the final term was pretty-printed and re-parsed, and `↑n` casts (e.g. from
`hasDerivAt_pow`) did not survive the round trip.

Now domain constraints are left as (synthetic opaque) holes during the search and recorded
in the threaded `domain` list (so abandoned branches drop theirs). The command builds the
domain predicate with `mkLambdaFVars`, fills each hole by projecting the domain hypothesis
(`projectConjunct`), and adds the `CDeriv` with `addDecl` (kernel-checked, nested proofs
abstracted as usual, module visibility via `mkDeclName`). No `sorry` is ever introduced.

Visible consequences: casts now appear in outputs (`↑2 * x ^ (2 - 1)` instead of the
re-elaborated literal `2 * …`), and auxiliary proof lemmas are numbered differently;
test expectations were updated. `Main.lean` no longer assumes the proof lemma is `_proof_2`.

### Experiments

| Variant | `test0` |
|---|---|
| original | 2805 attempts, tactic 2.9 s |
| B8 fixed | 1970 attempts, tactic 1.9 s |
| B8 + `c` | 860 attempts; all functions differentiated |
| B8 + `ch` | 84 attempts, tactic 0.19 s (~15×); derivations found, but `↑n` outputs then fail B9 |
| B8 + B9 + `ch` | tactic 0.21 s; all test functions differentiated, kernel-checked, standard axioms only (outputs differ from default mode) |
| `r` / `i` | some functions no longer differentiable |

## Suggested next steps

1. ~~Keep B8 fixed; update the test outputs.~~ Done.
2. ~~Fix B9.~~ Done.
3. Drop catch-all theorems automatically instead of the hand-written blacklists.
4. Index theorems by head symbol (`DiscrTree`; `ThmDB.lookup` already takes the key).
5. Build the DB once per benchmark process (timed runs currently restart from the post-import
   state and rebuild it), then re-run the benchmark and revisit the heartbeat limit.

## B10: implemented

- Catch-all theorems are excluded automatically and the remaining theorems are indexed by the
  head symbol of the differentiated function (`ThmIndex` in `Autodiff/ListThmDB.lean`);
  non-`HasDerivAt` goals fail immediately. This replaces both hand-written blacklists, which
  now only apply under `AD_LEGACY=1`. Test suite: 10-25x fewer apply attempts; computed
  domains unchanged; derivatives use the power/quotient rules directly.
- Benchmark (`Main.lean`):
  - the theorem DB is built once in a warm-up; every timed run starts from that state (A1);
  - only the `differentiate` command is timed (not re-defining the function);
  - the generator is seeded with the test index, so runs are reproducible and comparable (A8);
  - the heartbeat limit is now passed as an option (`AD_HEARTBEATS`). Previously the
    `Core.Context.maxHeartbeats` field was ignored by command elaboration, so the effective
    limit was Lean's default 200000 (A6);
  - failed derivations are reported as `FAIL` instead of panicking;
  - the function is printed on one line (multi-line output broke the CSV).
- Seeded cases 1-5: 26-170 ms per derivative (indexed) vs 96 ms-2.5 s (`AD_LEGACY=1`).

## Constant functions and the generator

- In a first 500-case run, 252/500 generated functions did not mention the variable, and 115
  of those got a domain made only of conditions on constants (e.g. `-46 ≠ 0`), because a
  constant subterm such as `log (-46)` could be differentiated with the logarithm rule.
- Fix in the tool: bodies that do not mention the variable are proved with
  `hasDerivAt_const` (derivative 0, no side conditions), in both search modes.
- Fix in the generator: constant functions are rejected; leaves are a literal or the
  variable; exponents are drawn from 1..10; constructors are uniform; `exp` stays disabled.
