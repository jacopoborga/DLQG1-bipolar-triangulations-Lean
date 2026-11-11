/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceDetermination15

/-! This module exposes the first-admissibility consequence of the intrinsic
selector and records the remaining bridge from that selector to the realized
adjacent ray. It does not assert the selector or paper completion. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PaperProofs.Section4

/-- Helper toward Lemma 5.6: an intrinsically selected departure cannot be
reached at an earlier position of its incoming clockwise scan by any
competing adjacent metric candidate that agrees on the preceding darts. -/
theorem intrinsicallyLeftmostAdjacentRay_noEarlierScanDart
    {M : GeometricSideSubmap} {longest : Bool}
    {v d : ℕ → GeometricSideCell M}
    (hleft : IntrinsicallyLeftmostAdjacentRay M longest v d)
    (i : ℕ) {v' d' : ℕ → GeometricSideCell M}
    (hcandidate : geometricSideAdjacentGeodesicCandidate M longest v' d')
    (hprefix : ∀ j, j < i → d' j = d j) :
    ∃ (a : GeometricSideCell M) (f : ℕ → GeometricSideCell M) (n : ℕ),
      geometricSideRayIncomingCorner M d i a ∧
      geometricSideClockwiseScan M a f n ∧ f n = d i ∧
      ∀ j, j < n → f j ≠ d' i := by
  obtain ⟨a, f, n, ha, hf, hend, hfirst⟩ := hleft.2 i
  exact ⟨a, f, n, ha, hf, hend, hfirst v' d' hcandidate hprefix⟩


































































end DirectedDistances.PaperProofs.Section5
