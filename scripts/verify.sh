#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
lake_args=()
if [[ -n "${DLQG_LAKE_PACKAGES:-}" ]]; then lake_args+=("--packages=$DLQG_LAKE_PACKAGES"); fi
mkdir -p .lake/release-verification
python3 -B verification/test_lexer.py
python3 -B scripts/check_release.py
lake "${lake_args[@]}" build DirectedDistances
lake "${lake_args[@]}" env lean -j1 -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 verification/Axioms.lean > .lake/release-verification/axioms.log
python3 -B scripts/check_release.py --axioms Axioms --log .lake/release-verification/axioms.log
lake "${lake_args[@]}" env lean -j1 -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 verification/Providers.lean > .lake/release-verification/providers.log
python3 -B scripts/check_release.py --axioms Providers --log .lake/release-verification/providers.log
lake "${lake_args[@]}" env leanchecker --fresh DirectedDistances.DeliveryVerificationRoot > .lake/release-verification/kernel.log 2>&1

mkdir -p .lake/build/lib/lean/verification
lake "${lake_args[@]}" env lean -j1 -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -o .lake/build/lib/lean/verification/ConstantWindow.olean verification/ConstantWindow.lean
lake "${lake_args[@]}" env lean -j1 -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -o .lake/build/lib/lean/verification/ConstantWindowCheck.olean verification/ConstantWindowCheck.lean > .lake/release-verification/constant-window.log
python3 -B scripts/check_release.py --axioms ConstantWindow --log .lake/release-verification/constant-window.log
lake "${lake_args[@]}" env leanchecker --fresh verification.ConstantWindowCheck > .lake/release-verification/constant-window-kernel.log 2>&1

for scope_module in SourceBoundaryDomain SourceBoundaryChanneled; do
  lake "${lake_args[@]}" env lean -j1 -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -o ".lake/build/lib/lean/verification/$scope_module.olean" "verification/$scope_module.lean"
done
lake "${lake_args[@]}" env lean -j1 -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -o .lake/build/lib/lean/verification/SourceScopeCheck.olean verification/SourceScopeCheck.lean > .lake/release-verification/source-domains.log
python3 -B scripts/check_release.py --axioms SourceDomains --log .lake/release-verification/source-domains.log
lake "${lake_args[@]}" env leanchecker --fresh verification.SourceScopeCheck > .lake/release-verification/source-domains-kernel.log 2>&1
