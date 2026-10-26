# autodiff

A prototype implementation of certified automatic differentiation in Lean, as described in the
paper "Automatic Certified Differentiation in Lean" (DATAMOD 2026). Given a function
`f : ℝ → ℝ`, the `differentiate` command searches Mathlib's derivative theorems and returns a
`CDeriv f` structure with the derivative `f'`, a predicate `domain` on which the derivative is
valid, and a proof, checked by the Lean kernel, that `f'` is the derivative of `f` at every point
of `domain`.

## Directory structure

    autodiff/
    |- Autodiff/ ............. the implementation (derivative search, theorem index, `differentiate` command)
    |- Test/ ................. test cases, checked with `#guard_msgs`
    |- Main.lean ............. the benchmark driver (test function generator, timing, output)
    |- runBenchmark.sh ....... reproduces the paper's evaluation end-to-end
    |- results/datamod2026/ .. the paper's evaluation results, and the scripts that run, analyse and plot them
    |- investigation/ ........ notes and probe files from the performance investigation

## Requirements

- Linux (or macOS with GNU coreutils installed), with `bash`, `bc`, `timeout`, and `realpath`.
- [elan](https://github.com/leanprover/elan), the Lean toolchain manager. The required Lean
  version (4.33.1, see `lean-toolchain`) is installed automatically on the first build.
- Python 3 for the analysis scripts, and matplotlib for the figure (optional; the Latin Modern
  fonts are used if installed, otherwise matplotlib falls back to its default font).

## Building and testing

```sh
lake exe cache get   # download prebuilt Mathlib (v4.33.1); building Mathlib from source takes hours
lake build           # build the library and the benchmark executable
lake test            # run the test cases
```

Each test case differentiates a function, then uses `#print` to display the result and
`#guard_msgs` to compare it with the expected output; `lake test` fails if any result differs.

## Usage

```lean
import Autodiff.Differentiate

noncomputable def f := fun x : ℝ => Real.log (3 / x)
let d := differentiate f
#print d
-- d.f'     = fun x => (0 * x - 3 * 1) / x ^ 2 / (3 / x)
-- d.domain = fun x => x ≠ 0 ∧ 3 / x ≠ 0
-- d.proof  : ∀ (x : ℝ), d.domain x → HasDerivAt f (d.f' x) x
```

See `Test/autodiff_debug.lean` for more examples.

## Reproducing the evaluation

The paper evaluates the tool on 500 generated test functions, each differentiated with the theorem
index and without it (`AD_LEGACY=1`, which tries all derivative theorems in order). The results
reported in the paper are in `results/datamod2026/`; its `README.md` describes the setup and the
files in detail.

### 1. Build

Follow [Building and testing](#building-and-testing) above. `lake test` should pass.

### 2. Quick check (a few minutes)

```sh
./runBenchmark.sh 10 eval-quick
```

This runs the first 10 test cases in both configurations, then prints the summary, the domain
checks, and the axioms, and writes the figure to `eval-quick/speedup.pdf`. The test functions are
deterministic, so `eval-quick/indexed/test<i>.txt` should show the same function and the same
derivative, domain, and proof as `results/datamod2026/indexed/test<i>.txt`.

### 3. Full run

```sh
./runBenchmark.sh 500 eval-out
```

The output directory must be empty or not exist. On the machine used for the paper (AMD Ryzen 7
7730U, 8 cores, 40 GB RAM), the run takes about 35 minutes with the index and about 2.5 hours
without it, including Lean start-up for each test case. Run it on an otherwise idle machine, and do
not run several benchmarks in parallel: the timings are wall-clock times.

The script performs the following steps, which can also be run individually:

```sh
R=results/datamod2026
$R/run.sh eval-out/indexed 1 500                 # with the theorem index
AD_LEGACY=1 $R/run.sh eval-out/legacy 1 500      # without it
python3 $R/analyze.py eval-out                   # Table 1; writes eval-out/results.json
python3 $R/check_domains.py eval-out             # domain checks
grep -h '^Axioms:' eval-out/indexed/test*.txt | sort | uniq -c   # axioms of each certified derivative
python3 $R/plot.py eval-out eval-out/speedup.pdf # Fig. 6
```

`run.sh` takes a range of test cases, so a long run can be split or resumed, e.g. `run.sh
eval-out/indexed 251 500` continues after case 250. For each test case `i`, the benchmark
executable generates the `i`-th test function, builds the theorem database, differentiates the
function once untimed, and then four more times, timing each of those runs.

### 4. Outputs

In each of `eval-out/indexed/` and `eval-out/legacy/`:

- `log.txt`: one line per test case, `index, function, size, depth, t1, t2, t3, t4`, with the four
  timings in milliseconds, or `FAIL` if differentiation failed (e.g., on reaching the heartbeat limit).
- `test<i>.txt`: the input function, the computed `CDeriv` (derivative, domain, proof), and the
  axioms it depends on; or the error message.
- `wall.txt`: the wall-clock time of each test case in seconds, including Lean start-up.

### 5. Expected results

The paper reports (`results/datamod2026/README.md`):

- With the index, all 500 test cases complete; without it, 488 do, and 12 reach Lean's default
  heartbeat limit (200000).
- The computed domains are identical in all 488 test cases that complete in both configurations.
- Median time per differentiation: 181 ms with the index and 2423 ms without; median per-case
  speedup 8.6x (13.8x for restricted domains, 5.9x for universal ones), up to 71x.
- Every certified derivative depends only on the axioms `propext`, `Classical.choice`, and
  `Quot.sound`.
- All conjuncts of the domains have the form `e ≠ 0`, and all but one of the 433 restricted
  domains are satisfiable; the exception (test case 203) contains the factor `84 + -84`.

The test functions, derivatives, domains, proofs, failures, and axioms are deterministic and should
match exactly. Absolute timings depend on the machine and vary between runs (by about 5% on the same
machine), but the speedups and the comparison between the two configurations should be similar.

### Options

Environment variables read by the tool and the benchmark:

| Variable | Effect |
|---|---|
| `AD_LEGACY=1` | search without the theorem index (all theorems, in order) |
| `AD_HEARTBEATS=<n>` | heartbeat limit for each test case (default 200000, Lean's default) |
| `AD_STATS=1` | log the number and duration of theorem application attempts |
| `AD_RECS=<file>` | append one line per theorem application attempt to `<file>` |

See `investigation/NOTES.md` for the performance investigation that led to the theorem index.
