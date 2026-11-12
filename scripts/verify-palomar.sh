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
# Keep normal comparator sandboxing. Every configuration enables NanoDa.
lake "${lake_args[@]}" comparator --config palomar/comparator-pilot.json > "$evidence_dir/pilot-comparator.log" 2>&1
lake "${lake_args[@]}" comparator --config comparator.json > "$evidence_dir/appendix-comparator.log" 2>&1
lake "${lake_args[@]}" comparator --config palomar/principal/boltzmann-distances.json > "$evidence_dir/boltzmann-comparator.log" 2>&1
lake "${lake_args[@]}" env lean -j1 -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 verification/PalomarPilotAxioms.lean > "$evidence_dir/pilot-axioms.log" 2>&1
python3 -B scripts/check_release.py --axioms PalomarPilot --log "$evidence_dir/pilot-axioms.log"
lake "${lake_args[@]}" env lean -j1 -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 verification/PalomarAppendixAxioms.lean > "$evidence_dir/appendix-axioms.log" 2>&1
python3 -B scripts/check_release.py --axioms PalomarAppendix --log "$evidence_dir/appendix-axioms.log"
lake "${lake_args[@]}" env lean -j1 -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 verification/PalomarBoltzmannDistancesAxioms.lean > "$evidence_dir/boltzmann-axioms.log" 2>&1
python3 -B scripts/check_release.py --axioms PalomarBoltzmannDistances --log "$evidence_dir/boltzmann-axioms.log"

# Both finite-cell configurations retain sandboxing and mandatory NanoDa.
lake "${lake_args[@]}" comparator --config palomar/principal/cell-ldp.json > "$evidence_dir/cell-ldp-comparator.log" 2>&1
lake "${lake_args[@]}" env lean -j1 -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 verification/PalomarCellLDPAxioms.lean > "$evidence_dir/cell-ldp-axioms.log" 2>&1
python3 -B scripts/check_release.py --axioms PalomarCellLDP --log "$evidence_dir/cell-ldp-axioms.log"
lake "${lake_args[@]}" comparator --config palomar/principal/cell-sdp.json > "$evidence_dir/cell-sdp-comparator.log" 2>&1
lake "${lake_args[@]}" env lean -j1 -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 verification/PalomarCellSDPAxioms.lean > "$evidence_dir/cell-sdp-axioms.log" 2>&1
python3 -B scripts/check_release.py --axioms PalomarCellSDP --log "$evidence_dir/cell-sdp-axioms.log"

# Actual KMSW/M0 construction, both Busemann modes and all selected helpers.
lake "${lake_args[@]}" comparator --config palomar/principal/busemann.json > "$evidence_dir/busemann-comparator.log" 2>&1
lake "${lake_args[@]}" env lean -j1 -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 verification/PalomarBusemannAxioms.lean > "$evidence_dir/busemann-axioms.log" 2>&1
python3 -B scripts/check_release.py --axioms PalomarBusemann --log "$evidence_dir/busemann-axioms.log"
