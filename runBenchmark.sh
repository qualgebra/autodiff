#!/bin/bash
# Reproduce the evaluation of "Automatic Certified Differentiation in Lean" (DATAMOD 2026):
# differentiate N generated test functions with the theorem index and without it
# (AD_LEGACY=1), then summarise the results, check the computed domains and the
# axioms of the certified derivatives, and plot the evaluation figure.
#
# usage: ./runBenchmark.sh [N] [OUT]
#   N    number of test cases (default 500, as in the paper)
#   OUT  output directory, must be empty or not exist (default eval-out)
set -e
N=${1:-500}
OUT=$(realpath -m "${2:-eval-out}")
R="$(dirname "$(realpath "$0")")/results/datamod2026"

mkdir -p "$OUT/indexed" "$OUT/legacy"
if [ -n "$(find "$OUT/indexed" "$OUT/legacy" -mindepth 1 | head -1)" ]; then
  echo "error: $OUT already contains results; use an empty directory" >&2
  exit 1
fi

echo "== running $N test cases with the theorem index"
"$R/run.sh" "$OUT/indexed" 1 "$N"
echo "== running $N test cases without the theorem index"
AD_LEGACY=1 "$R/run.sh" "$OUT/legacy" 1 "$N"

echo "== summary (Table 1 of the paper)"
python3 "$R/analyze.py" "$OUT"
echo "== computed domains"
python3 "$R/check_domains.py" "$OUT"
echo "== axioms of the certified derivatives (with the index)"
grep -h '^Axioms:' "$OUT"/indexed/test*.txt | sort | uniq -c
echo "== figure (Fig. 6 of the paper)"
python3 "$R/plot.py" "$OUT" "$OUT/speedup.pdf" && echo "written to $OUT/speedup.pdf" \
  || echo "skipped: plot.py needs matplotlib"
