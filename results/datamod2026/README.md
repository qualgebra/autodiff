# Evaluation results: "Automatic Certified Differentiation in Lean" (DATAMOD 2026)

Benchmark of 500 randomly generated functions, each differentiated with the theorem
index (`indexed/`) and without it (`legacy/`, `AD_LEGACY=1`). These are the results
reported in the paper's evaluation (Table 1 and Fig. 7).

## Setup

- Tool: branch `perf-investigation`, commit a7e7d90 (generator, search and benchmark driver).
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
| `run.sh` | runs cases: `./run.sh indexed 1 500` and `AD_LEGACY=1 ./run.sh legacy 1 500` (run in empty directories) |

## Summary

- With the index: 500/500 cases completed. Without it: 488/500 (12 reached the heartbeat limit).
- The computed domains are identical in all 488 cases that complete in both configurations.
- Median time per differentiation: 172 ms with the index, 2423 ms without; median per-case
  speedup 9.1x (restricted domains 14.5x, universal domains 6.2x), up to 66x.
- Total time over the 488 common cases: 94 s with the index, 1333 s without.
