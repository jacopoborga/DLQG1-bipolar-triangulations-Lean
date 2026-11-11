/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceAmbientSelectorBridge
public import DirectedDistances.PaperProofs.Section5.GeoSliceCoherentAmbientLift

/-! The coherent lift lets the ambient cut-leftmost hypothesis be applied to the
actual edge stream of any side candidate. This gives trace containment in the
region bounded by the preceding ambient ray and the supplied reference path.
It does not compare intrinsic scan order with departure-angle order. -/

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

/-- Helper toward Lemma 5.6: every side candidate has a coherent ambient lift,
and its ambient trace lies in the cut-leftmost region bounded by
`P (k - 1)` and `T (k - 1)`. The inclusion uses the existing ambient
cut-leftmost hypothesis; it does not establish leftmostness of the candidate. -/
theorem m0GeodesicSide_candidate_trace_within_previous_cutRegion
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
    (hc : geometricSideAdjacentGeodesicCandidate
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
  obtain ⟨Q, u, e, huv, hde, hQu, hQe⟩ :=
    m0GeodesicLeftSide_adjacentCandidate_coherentAmbientLift hp (P k) hc
  let Qcut := m0CutPathOfPresentPath W H h hLL (k - 1) Q.codePath
  have hQcut : if longest then Qcut.HasLongestSegments
      else Qcut.HasShortestSegments := by
    cases longest with
    | false =>
        exact (Xdp.Sdp.m0Cut_hasShortestSegments_iff W H h hLL (k - 1)
          Q.codePath).2 Q.segments
    | true =>
        exact (m0Cut_hasLongestSegments_iff W H h hLL (k - 1)
          Q.codePath).2 Q.segments
  have htrace := hleft (k - 1) Qcut hQcut
  refine ⟨Q, u, e, huv, hde, hQu, hQe, ?_⟩
  simpa only [Qcut, m0CutPathOfPresentPath] using htrace





























































































end DirectedDistances.PaperProofs.Section5
