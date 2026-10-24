# Evaluation results: "Automatic Certified Differentiation in Lean" (DATAMOD 2026)

Benchmark of 500 randomly generated functions, each differentiated with the theorem
index (`indexed/`) and without it (`legacy/`, `AD_LEGACY=1`). These are the results
reported in the paper's evaluation (Table 1 and Fig. 7).

## Setup

- Tool: branch `perf-investigation`. `indexed/` was produced with commit 05276f6, `legacy/` with a7e7d90;
  the legacy search is identical in both commits (it ignores the index key).
- Lean 4.33.1, Mathlib v4.33.1; default heartbeat limit (200000).
- AMD Ryzen 7 7730U (8 cores), 40 GB RAM, Linux 7.0.0-38-generic.
- Test case `i` is the `i`-th function of a fixed random sequence of distinct functions
  (see `genTestFunc` in `Main.lean`): expression trees of depth up to 7 over integer literals
  in [-100, 100], `x ^ n` with n in 1..10, `+ - * /`, `sin`, `cos`, `tan` and `log`; each
  function mentions `x` and has an operator or function at the root.
- The theorem database is built once per case in a warm-up. The `differentiate` command
  is then run once untimed and four times timed; each timed run starts from the same state.

## Files

| Path | Contents |
|---|---|
| `indexed/log.txt`, `legacy/log.txt` | one line per case: `index, function, size, depth, t1, t2, t3, t4` (ms), or `FAIL` |
| `indexed/test<i>.txt`, `legacy/test<i>.txt` | the input function and the computed `CDeriv` (derivative, domain, proof), or the error |
| `*/wall.txt` | wall-clock seconds per case, including Lean start-up and imports |
| `results.json` | per-case summary produced by `analyze.py` |
| `analyze.py` | summary statistics: `python3 analyze.py .` |
| `plot.py` | Fig. 7 of the paper: `python3 plot.py . speedup.pdf` (needs matplotlib, Latin Modern fonts) |
| `axioms.txt` | axioms each certified derivative depends on, per case (separate indexed run with commit e5d5827, which records them) |
| `check_domains.py` | checks that domain conjuncts are side conditions `e ≠ 0` and that domains are satisfiable (by sampling) |
| `run.sh` | runs cases: `./run.sh indexed 1 500` and `AD_LEGACY=1 ./run.sh legacy 1 500` (run in empty directories) |

## Summary

- With the index: 500/500 cases completed. Without it: 488/500 (12 reached the heartbeat limit).
- The computed domains are identical in all 488 cases that complete in both configurations.
- Median time per differentiation: 181 ms with the index, 2423 ms without; median per-case
  speedup 8.6x (restricted domains 13.8x, universal domains 5.9x), up to 71x.
- Total time over the 488 common cases: 98 s with the index, 1333 s without.
- Timing varies by about 5% between runs: an earlier indexed run (commit a7e7d90,
  producing identical derivations for all 500 cases) gave a median of 172 ms.
- Every certified derivative depends only on `propext`, `Classical.choice` and `Quot.sound`
  (no `sorryAx`), for all 500 cases (`axioms.txt`).
- Every domain conjunct has the form `e ≠ 0`; 432 of the 433 restricted domains are
  satisfiable (`check_domains.py`). The exception, case 203, has an argument of `log` with
  the factor `84 + -84`, so its domain is empty.
