/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceAmbientSelectorBridge3

/-! An intrinsically selected adjacent ray has a coherent ambient lift, and the
lift's trace lies in the previous cut region. The remaining bridge is to show
that this lift is itself cut-leftmost, then identify it with the previous ray.
Neither conclusion is assumed here. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open Xdp.Sdp

/-- Helper toward Lemma 5.6: an intrinsically selected adjacent ray has a
coherent ambient lift whose trace lies in the previous cut region. This does
not establish the lift's ambient cut-leftmost property. -/
theorem m0GeodesicSide_intrinsicallySelectedRay_coherentAmbientTrace
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
    ∃ (Q : M0CutInfiniteGeodesic W H h hLL (k - 1) longest)
      (u : ℕ → (m0GeodesicSide hp (P k) .left).vertices)
      (e : ℕ → (m0GeodesicSide hp (P k) .left).edges),
      (∀ n, v n = .inl (u n)) ∧
      (∀ n, d n = .inr ⟨((e n).val, false), (e n).property⟩) ∧
      (∀ n, (Q.codePath.initial n).1.id = (u n).val) ∧
      (∀ n, Q.codePath.edge n = (e n).val) ∧
      pathTrace (WholePlanePastGlueDrawing.glueDrawing W h hp H)
        (fun n => (wholePlaneEdgeι W 0 (Q.codePath.edge n), false)) ⊆
        closedBetween
          (pathTrace (WholePlanePastGlueDrawing.glueDrawing W h hp H)
            (fun n => wholePlaneDartι W 0
              ((P (k - 1)).codePath.edge n, false)))
          (pathTrace (WholePlanePastGlueDrawing.glueDrawing W h hp H)
            (fun n => wholePlaneDartι W 0 ((T (k - 1)).edge n, false))) := by
  exact m0GeodesicSide_candidate_trace_within_previous_cutRegion
    hp P T hleft k hcontain hselect.1





















































































end DirectedDistances.PaperProofs.Section5
