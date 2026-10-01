#!/usr/bin/env bash
# Clean build of crrg-core and regeneration of BUILD.log. Requires lean/lake v4.30.0 on PATH.
set -u
cd "$(dirname "$0")"
# Pin the toolchain for every lean/lake call, including the runner's, which compiles submissions in temporary
# directories that have no lean-toolchain file (elan would otherwise pick the machine's default toolchain).
export ELAN_TOOLCHAIN="$(cat lean-toolchain)"
rm -rf .lake/build
tmp=$(mktemp)
{
  echo "# crrg-core build log"
  echo "# lean --version: $(lean --version)"
  echo "# lean-toolchain: $(cat lean-toolchain)"
  echo "# dependencies: none (no 'require' in lakefile.lean; Lean core only, no Mathlib)"
  echo "# command: ./build.sh  (clean: .lake/build removed first; then lake build CRRGCore, CRRGTools, CRRGExamples; then the seal probes; then the runner suite)"
  echo
  echo "## lake build CRRGCore"
  lake build CRRGCore 2>&1 | grep -v '^trace'; echo "exit: ${PIPESTATUS[0]}"
  echo
  echo "## lake build CRRGTools"
  lake build CRRGTools 2>&1 | grep -v '^trace'; echo "exit: ${PIPESTATUS[0]}"
  echo
  echo "## families/gen_lean.py --check (the JSON-derived Lean data is up to date with families/demo.json)"
  python3 families/gen_lean.py --check; echo "exit: $?"
  echo
  echo "## lake build CRRGExamples"
  lake build CRRGExamples 2>&1 | grep -v '^trace' | tee "$tmp"; echo "exit: ${PIPESTATUS[0]}"
  echo
  echo "## seal probes (probes/seal/run.sh): each before/after pair must differ"
  probes/seal/run.sh; echo "exit: $?"
  echo
  echo "## runner suite (runner/run_tests.py; details in runner/TESTS.log)"
  python3 runner/run_tests.py | tail -1; echo "exit: ${PIPESTATUS[0]}"
  echo
  echo "## summary"
  echo "headline declarations with #print axioms: $(grep -c 'depends on axioms\|does not depend on any axioms' "$tmp")"
  echo "of which depend on Classical.choice: $(grep 'depends on axioms' "$tmp" | grep -c 'Classical.choice')"
  echo "axiom sets in the report: $(grep 'depends on axioms' "$tmp" | grep -oE '\[[^]]*\]$' | sort -u | tr '\n' ' ')plus $(grep -c 'does not depend on any axioms' "$tmp") declarations with no axioms"
  echo "whole-library axiom audit (CRRGExamples/CoreAxiomAudit.lean): $(grep -oE 'CORE AXIOM AUDIT: .*' "$tmp" | head -1)"
  echo "'sorry' in CRRGCore sources: $(cat CRRGCore/*.lean CRRGCore.lean | grep -c sorry)"
  echo "'import Lean' in the certified library (CRRGCore.lean, CRRGCore/*.lean): $(grep -l '^import Lean' CRRGCore.lean CRRGCore/*.lean | wc -l)"
  echo "imports of CRRGCore modules: $(grep -h '^import' CRRGCore.lean CRRGCore/*.lean | sort -u | tr '\n' ' ')"
  echo "#guard_msgs negative controls in CRRGExamples: $(grep -c '^#guard_msgs' CRRGExamples/*.lean | tr '\n' ' ')"
  echo "'sorry' in CRRGExamples sources: only inside the two #guard_msgs negative controls of Audit.lean (forged-state attempts that must FAIL to elaborate; nothing containing sorry enters the environment): $(grep -n sorry CRRGExamples/*.lean | cut -d: -f1,2 | tr '\n' ' ')"
} > BUILD.log 2>&1
rm -f "$tmp"
tail -8 BUILD.log
