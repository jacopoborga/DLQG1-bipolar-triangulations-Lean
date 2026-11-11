/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceAmbientSelectorBridge5

/-! This file records the scan-to-ambient comparison attempt. The intrinsic
selector yields no-earlier scan order, and each consecutive retained dart is
an ambient first return. The remaining step is to turn this encounter order
into the departure-angle comparison defining ambient cut-leftmostness. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open Xdp.Sdp

/-- Helper toward Lemma 5.6: every earlier position in the intrinsic
selector's first-admissible scan is distinct from a qualifying competitor's
first differing dart, and every consecutive scan step is an ambient clockwise
first return among the retained side darts. This records the scan-order input
to the unresolved departure-angle comparison. -/
theorem m0GeodesicSide_intrinsicSelector_competitor_scan_ambientFirstReturns
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))}
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ)
    {v d : ℕ → GeometricSideCell (m0GeodesicSide hp (P k) .left)}
    (hselect : IntrinsicallyLeftmostAdjacentRay
      (m0GeodesicSide hp (P k) .left) longest v d)
    (i : ℕ) {v' d' : ℕ → GeometricSideCell (m0GeodesicSide hp (P k) .left)}
    (hcandidate : geometricSideAdjacentGeodesicCandidate
      (m0GeodesicSide hp (P k) .left) longest v' d')
    (hpref : ∀ j, j < i → d' j = d j) :
    ∃ (a : GeometricSideCell (m0GeodesicSide hp (P k) .left))
      (f : ℕ → GeometricSideCell (m0GeodesicSide hp (P k) .left)) (n : ℕ),
      geometricSideRayIncomingCorner (m0GeodesicSide hp (P k) .left) d i a ∧
      geometricSideClockwiseScan (m0GeodesicSide hp (P k) .left) a f n ∧
      f n = d i ∧
      (∀ j, j < n → f j ≠ d' i) ∧
      (∀ j, j < n →
        ∃ (e e' : {e : ℕ × Bool //
            e.1 ∈ (m0GeodesicSide hp (P k) .left).edges}),
          f j = .inr e ∧ f (j + 1) = .inr e' ∧
          ∃ r : ℕ, 0 < r ∧
            ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[r]
              (wholePlaneDartι W 0 e.val) = wholePlaneDartι W 0 e'.val ∧
            ∀ t : ℕ, 0 < t → t < r →
              ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[t]
                (wholePlaneDartι W 0 e.val) ∉
                  wholePlaneDartι W 0 '' {x : ℕ × Bool |
                    x.1 ∈ (m0GeodesicSide hp (P k) .left).edges}) := by
  obtain ⟨a, f, n, hincoming, hscan, hend, hnotEarlier⟩ :=
    intrinsicallyLeftmostAdjacentRay_competitor_notEarlierInScan
      hselect i hcandidate hpref
  refine ⟨a, f, n, hincoming, hscan, hend, hnotEarlier, ?_⟩
  intro j hj
  exact m0GeodesicSide_clockwiseScan_step_ambientFirstReturn
    hp (P k) .left hscan j hj


















 
/- theorem m0GeodesicSide_intrinsicSelector_is_ambientCutLeftmost
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))}
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k : ℤ,
      Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈
        (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    {v d : ℕ → GeometricSideCell (m0GeodesicSide hp (P k) .left)}
    (hselect : IntrinsicallyLeftmostAdjacentRay
      (m0GeodesicSide hp (P k) .left) longest v d) :
    ∃ Q : M0CutInfiniteGeodesic W H h hLL (k - 1) longest,
      Xdp.CutLeftmostXdp W H h hp hLL longest (k - 1) Q (T (k - 1)) -/



/- theorem m0GeodesicSide_intrinsicSelector_eq_previousRay
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))}
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k : ℤ,
      Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈
        (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices) :
    ∃ v d : ℕ → GeometricSideCell (m0GeodesicSide hp (P k) .left),
      geometricSideAdjacentGeodesicCandidate
        (m0GeodesicSide hp (P k) .left) longest v d ∧
      IntrinsicallyLeftmostAdjacentRay
        (m0GeodesicSide hp (P k) .left) longest v d ∧
      v = m0GeodesicSideAdjacentVertices hp P k hcontain ∧
      d = m0GeodesicSideAdjacentDarts hp P k hcontain -/

end DirectedDistances.PaperProofs.Section5
