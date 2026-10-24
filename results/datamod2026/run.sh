#!/bin/bash
# Run benchmark cases <from>..<to>, appending to <outdir>/log.txt (one CSV line per
# case) and <outdir>/wall.txt; each case also writes <outdir>/test<i>.txt.
# usage: run.sh <outdir> <from> <to>   (set AD_LEGACY=1 for the search without the index)
set -e
OUT=$(realpath "$1")
REPO=$(realpath "$(dirname "$0")/../..")
cd "$REPO"
lake build benchmark >/dev/null
LP=$(lake env printenv LEAN_PATH)
TCPATH=$(lake env printenv PATH)
cd "$OUT"
for (( i=$2; i<=$3; i++ )); do
  s=$(date +%s.%N)
  PATH=$TCPATH LEAN_PATH=$LP timeout 900 "$REPO/.lake/build/bin/benchmark" $i 2>>log.txt >/dev/null \
    || echo "$i, EXIT $?" >> log.txt
  echo "$i $(echo "$(date +%s.%N) - $s" | bc)" >> wall.txt
done
