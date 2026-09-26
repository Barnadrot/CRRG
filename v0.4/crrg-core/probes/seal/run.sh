#!/usr/bin/env bash
# Seal probes (review item 7): each before/after pair must produce DIFFERENT seals.
# Run from crrg-core/ after `lake build CRRGTools`.
set -u
status=0
for pair in rename shape; do
  a=$(lake env lean probes/seal/${pair}_before/Probe.lean 2>&1 | grep -oE 'crrg seal [^:]*: [0-9]+')
  b=$(lake env lean probes/seal/${pair}_after/Probe.lean 2>&1 | grep -oE 'crrg seal [^:]*: [0-9]+')
  if [ -n "$a" ] && [ -n "$b" ] && [ "$a" != "$b" ]; then r=DIFFERENT; else r="SAME (FAIL)"; status=1; fi
  echo "seal probe $pair: before [$a] after [$b] -> $r"
done
exit $status
