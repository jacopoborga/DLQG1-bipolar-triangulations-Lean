#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# Include the toolchain's bundled nanoda_bin, not only the elan shims.
export PATH="$(lean --print-prefix)/bin:$PATH"
export LEAN_NUM_THREADS=1
lake_args=()
if [[ -n "${DLQG_LAKE_PACKAGES:-}" ]]; then lake_args+=("--packages=$DLQG_LAKE_PACKAGES"); fi
evidence_dir=".lake/palomar-evidence/verify-$(date -u +%Y%m%dT%H%M%SZ)-$$"
mkdir -p "$evidence_dir"
printf 'Palomar evidence: %s\n' "$evidence_dir"
python3 -B verification/test_lexer.py
python3 -B verification/test_challenge_holes.py
python3 -B scripts/check_release.py
# Keep normal comparator sandboxing. Both configurations enable NanoDa.
lake "${lake_args[@]}" comparator --config palomar/comparator-pilot.json > "$evidence_dir/pilot-comparator.log" 2>&1
lake "${lake_args[@]}" comparator --config comparator.json > "$evidence_dir/appendix-comparator.log" 2>&1
lake "${lake_args[@]}" env lean -j1 -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 verification/PalomarPilotAxioms.lean > "$evidence_dir/pilot-axioms.log" 2>&1
python3 -B scripts/check_release.py --axioms PalomarPilot --log "$evidence_dir/pilot-axioms.log"
lake "${lake_args[@]}" env lean -j1 -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 verification/PalomarAppendixAxioms.lean > "$evidence_dir/appendix-axioms.log" 2>&1
python3 -B scripts/check_release.py --axioms PalomarAppendix --log "$evidence_dir/appendix-axioms.log"
