/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceAmbientSelectorBridge6
public import DirectedDistances.PaperProofs.Section5.GeoSliceDetermination10

/-! This module records the established candidate and trace-containment inputs to
side recognition. The remaining selector comparison is left open below. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open Xdp.Sdp

/-- Helper toward Lemma 5.6: the side-coded previous geodesic is an intrinsic
metric candidate, and the coherent ambient lift of that candidate has trace
in the region supplied by the cut-leftmost hypothesis at the previous index.
This packages the candidate with the geometric containment needed for a later
recognition argument; it does not assert an intrinsic scan-order comparison. -/
theorem m0GeodesicSide_previousRay_candidate_and_traceWithinCutRegion
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
    geometricSideAdjacentGeodesicCandidate
        (m0GeodesicSide hp (P k) .left) longest
        (m0GeodesicSideAdjacentVertices hp P k hcontain)
        (m0GeodesicSideAdjacentDarts hp P k hcontain) ∧
      ∃ (Q : M0CutInfiniteGeodesic W H h hLL (k - 1) longest)
        (u : ℕ → (m0GeodesicSide hp (P k) .left).vertices)
        (e : ℕ → (m0GeodesicSide hp (P k) .left).edges),
        (∀ n, m0GeodesicSideAdjacentVertices hp P k hcontain n = .inl (u n)) ∧
        (∀ n, m0GeodesicSideAdjacentDarts hp P k hcontain n =
          .inr ⟨((e n).val, false), (e n).property⟩) ∧
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
  refine ⟨m0GeodesicSide_realized_adjacentCandidate hp P k hcontain, ?_⟩
  exact m0GeodesicSide_candidate_trace_within_previous_cutRegion
    hp P T hleft k hcontain (m0GeodesicSide_realized_adjacentCandidate hp P k hcontain)















/- theorem m0GeodesicSide_adjacentIntrinsicSelector
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
        (m0GeodesicSide hp (P k) .left) longest v d -/

end DirectedDistances.PaperProofs.Section5
