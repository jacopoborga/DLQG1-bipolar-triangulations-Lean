/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceAmbientSelectorBridge2







public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open Xdp.Sdp

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: each consecutive pair in a side-local clockwise
scan is an ambient clockwise first return among the side's retained geometric
darts. Thus omitted ambient darts do not change the scan order on the side. -/
theorem m0GeodesicSide_clockwiseScan_step_ambientFirstReturn
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide)
    {a : GeometricSideCell (m0GeodesicSide hp P s)}
    {f : ℕ → GeometricSideCell (m0GeodesicSide hp P s)} {n : ℕ}
    (hscan : geometricSideClockwiseScan (m0GeodesicSide hp P s) a f n)
    (j : ℕ) (hj : j < n) :
    ∃ (d e : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp P s).edges}),
      f j = .inr d ∧ f (j + 1) = .inr e ∧
      ∃ r : ℕ, 0 < r ∧
        ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[r]
          (wholePlaneDartι W 0 d.val) = wholePlaneDartι W 0 e.val ∧
        ∀ t : ℕ, 0 < t → t < r →
          ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[t]
            (wholePlaneDartι W 0 d.val) ∉
              wholePlaneDartι W 0 '' {x : ℕ × Bool |
                x.1 ∈ (m0GeodesicSide hp P s).edges} := by
  have hrot := hscan.2 j hj
  cases hnext : f (j + 1) with
  | inl v =>
      cases hcurrent : f j with
      | inl u => simp [hnext, hcurrent, geometricSideRelation] at hrot
      | inr d => simp [hnext, hcurrent, geometricSideRelation] at hrot
  | inr e =>
      cases hcurrent : f j with
      | inl u => simp [hnext, hcurrent, geometricSideRelation] at hrot
      | inr d =>
        have hrot' : geometricSideRelation (m0GeodesicSide hp P s) .rotation
            (.inr e) (.inr d) := by
          simpa [hnext, hcurrent, geometricSideRelation] using hrot
        obtain ⟨r, hr, hend, hskip⟩ :=
          (m0GeodesicSide_clockwiseStep_iff_wholePlane hp P s d e).1 hrot'
        exact ⟨d, e, rfl, rfl, r, hr, hend, hskip⟩







































































end DirectedDistances.PaperProofs.Section5
