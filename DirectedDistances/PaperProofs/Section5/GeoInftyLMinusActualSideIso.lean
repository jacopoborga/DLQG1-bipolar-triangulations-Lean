/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55LeftLawClause
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideWhole10
public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusSideMeasurable5

/-! Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: the actual left-side cells and decoded
left-side cells are equivalent through the inherited gluing. -/
@[expose] noncomputable def lMinusActualSideToDecodedCellEquiv
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
    (hk : k ≤ 0) :
    GeometricSideCell (m0GeodesicSide hp P .left) ≃
      GeometricSideCell (lMinusDecodedSide (W := W) (h := h) (k := k)
        (longest := longest) hτ hqMode hfin) :=
  (lMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk).symm.trans
    (lMinusDecodedToGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk).symm


































end DirectedDistances.PaperProofs.Section5
