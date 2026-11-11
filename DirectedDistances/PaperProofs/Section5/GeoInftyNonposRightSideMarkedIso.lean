/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftySideReader
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSideRotationIff

/-! Marked geometric identification for the nonpositive right side. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: the cell equivalence transports the root mark
on the nonpositive right side. -/
theorem rMinusGluedMarkedIso_root_iff
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
    (u v : Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode)) :
    rMinusGluedIncidenceRelation hτ hqMode .root u v ↔
      geometricSideRelation (m0GeodesicSide hp P .right) .root
        (rMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk u)
        (rMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk v) :=
  rMinusGluedCellEquiv_root_iff hτ hp P hqMode Tpath hfin hleft hk u v

/-- Helper toward Lemma 5.5: the cell equivalence transports directed
orientation and presence on the nonpositive right side. -/
theorem rMinusGluedMarkedIso_oriented_iff
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
    (u v : Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode)) :
    rMinusGluedIncidenceRelation hτ hqMode .oriented u v ↔
      geometricSideRelation (m0GeodesicSide hp P .right) .oriented
        (rMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk u)
        (rMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk v) :=
  rMinusGluedCellEquiv_oriented_iff hτ hp P hqMode Tpath hfin hleft hk u v












































end DirectedDistances.PaperProofs.Section5

