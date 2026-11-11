/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideRotationIff

 

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

section GeometricGluing

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
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

local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "Φ" => lMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the glued cell equivalence transports the vertex tag. -/
theorem lMinusGluedCellEquiv_vertex_transport_iff
    (u v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    lMinusGluedIncidenceRelation hτ hqMode .vertex u v ↔
      geometricSideRelation S .vertex (Φ u) (Φ v) :=
  lMinusGluedCellEquiv_vertex_iff hτ hp P hqMode Tpath hfin hleft hk u v

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the glued cell equivalence transports the root tag. -/
theorem lMinusGluedCellEquiv_root_transport_iff
    (u v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    lMinusGluedIncidenceRelation hτ hqMode .root u v ↔
      geometricSideRelation S .root (Φ u) (Φ v) :=
  lMinusGluedCellEquiv_root_iff hτ hp P hqMode Tpath hfin hleft hk u v

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the glued cell equivalence transports the empty target tag. -/
theorem lMinusGluedCellEquiv_target_transport_iff
    (u v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    lMinusGluedIncidenceRelation hτ hqMode .target u v ↔
      geometricSideRelation S .target (Φ u) (Φ v) :=
  lMinusGluedCellEquiv_target_iff hτ hp P hqMode Tpath hfin hleft hk u v

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the glued cell equivalence transports incidence. -/
theorem lMinusGluedCellEquiv_incident_transport_iff
    (u v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    lMinusGluedIncidenceRelation hτ hqMode .incident u v ↔
      geometricSideRelation S .incident (Φ u) (Φ v) :=
  lMinusGluedCellEquiv_incident_iff hτ hp P hqMode Tpath hfin hleft hk u v

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the glued cell equivalence transports opposite darts. -/
theorem lMinusGluedCellEquiv_opposite_transport_iff
    (u v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    lMinusGluedIncidenceRelation hτ hqMode .opposite u v ↔
      geometricSideRelation S .opposite (Φ u) (Φ v) :=
  lMinusGluedCellEquiv_opposite_iff hτ hp P hqMode Tpath hfin hleft hk u v

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the glued cell equivalence transports orientation. -/
theorem lMinusGluedCellEquiv_oriented_transport_iff
    (u v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    lMinusGluedIncidenceRelation hτ hqMode .oriented u v ↔
      geometricSideRelation S .oriented (Φ u) (Φ v) :=
  lMinusGluedCellEquiv_oriented_iff hτ hp P hqMode Tpath hfin hleft hk u v



































end GeometricGluing

end DirectedDistances.PaperProofs.Section5
