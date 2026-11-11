/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideWhole17

 

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

section ActualToDecodedSide2

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
local notation "D" => lMinusDecodedSide2 (W := W) (h := h) (k := k)
  (longest := longest) hτ hqMode hfin
local notation "E" => lMinusActualSideToDecodedSide2CellEquiv
  hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: the proved vertex, target, and corrected rotation
tags are preserved by the actual-to-decoded cell equivalence. -/
theorem lMinusActualSideToDecodedSide2_known_tags_iff
    (u v : GeometricSideCell S) :
    (geometricSideRelation S .vertex u v ↔
      geometricSideRelation D .vertex (E u) (E v)) ∧
    (geometricSideRelation S .target u v ↔
      geometricSideRelation D .target (E u) (E v)) ∧
    (geometricSideRelation S .rotation u v ↔
      geometricSideRelation D .rotation (E u) (E v)) := by
  exact ⟨lMinusActualSideToDecodedSide2CellEquiv_vertex_iff
      hτ hp P hqMode Tpath hfin hleft hk u v,
    lMinusActualSideToDecodedSide2CellEquiv_target_iff
      hτ hp P hqMode Tpath hfin hleft hk u v,
    lMinusActualSideToDecodedSide2CellEquiv_rotation_iff
      hτ hp P hqMode Tpath hfin hleft hk u v⟩
























































































end ActualToDecodedSide2

end DirectedDistances.PaperProofs.Section5
