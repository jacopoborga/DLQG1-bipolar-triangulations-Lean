/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusActualSideIso4

 

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: an actual retained face step is witnessed by
one complete run-zero creation triangle, and its first dart belongs to one
of the two glued code blocks. This does not assert that the whole triangle
belongs to that block. -/
theorem lMinusActualFaceNext_triangle_with_block_seed
    {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {H : WholePlaneRotationHypothesis W}
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
    {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : k ≤ 0)
    (d e : ℕ × Bool)
    (hde : (m0GeodesicSide hp P .left).faceNext d e) :
    ∃ j : TriangleCreationTime (shiftedStream W 0),
      d ∈ stageTriangleDartList (shiftedStream W 0) j ∧
      (∀ a ∈ stageTriangleDartList (shiftedStream W 0) j,
        a.1 ∈ (m0GeodesicSide hp P .left).edges) ∧
      (d ∈ Set.range (lMinusPrimedDartImage hτ) ∨
        d ∈ Set.range (fun a : {a : ℕ × Bool //
          a.1 ∈ (geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
            renewalTime renewalTime_positiveSuccessTime ThinMapSide.left
            (Subtype.mk (boundaryFutureHattedPath k W) hqMode)).edges} =>
              (boundaryGluingHatEdgeMap W h k hτ a.1.1, a.1.2))) := by
  obtain ⟨j, hd, htriangle⟩ :=
    lMinusActualFaceNext_triangle hp P d e hde
  have hblock := lMinusActualFaceNext_firstDart_in_block
    hτ hp P hqMode Tpath hfin hleft hk d e hde
  exact ⟨j, hd, htriangle, hblock⟩





















































































































end DirectedDistances.PaperProofs.Section5
