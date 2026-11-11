/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideWhole15
public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusActualSideIso4

 

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

/-- Helper toward Lemma 5.5: the actual left-side cells and the corrected
decoded left-side cells are equivalent through the glued cell carrier. -/
@[expose] noncomputable def lMinusActualSideToDecodedSide2CellEquiv :
    GeometricSideCell S ≃ GeometricSideCell
      (lMinusDecodedSide2 (W := W) (h := h) (k := k)
        (longest := longest) hτ hqMode hfin) :=
  (lMinusDecodedSide2ToGeometricCellEquiv hτ hp P hqMode Tpath hfin hleft hk).symm

/-- Helper toward Lemma 5.5: changing only the rotation field leaves the
actual to decoded cell equivalence from Iso unchanged. -/
theorem lMinusActualSideToDecodedSide2CellEquiv_eq_actual
    : lMinusActualSideToDecodedSide2CellEquiv hτ hp P hqMode Tpath hfin hleft hk =
      lMinusActualSideToDecodedCellEquiv hτ hp P hqMode Tpath hfin hleft hk := by
  rfl

/-- Helper toward Lemma 5.5: the vertex-source relation is preserved by the
actual to decoded cell equivalence. -/
theorem lMinusActualSideToDecodedSide2CellEquiv_vertex_iff
    (u v : GeometricSideCell S) :
    geometricSideRelation S .vertex u v ↔
      geometricSideRelation
        (lMinusDecodedSide2 (W := W) (h := h) (k := k)
          (longest := longest) hτ hqMode hfin) .vertex
        (lMinusActualSideToDecodedSide2CellEquiv hτ hp P hqMode Tpath hfin hleft hk u)
        (lMinusActualSideToDecodedSide2CellEquiv hτ hp P hqMode Tpath hfin hleft hk v) := by
  cases u <;> cases v <;> rfl

/-- Helper toward Lemma 5.5: the finite-only target tag is empty on both
whole-side structures. -/
theorem lMinusActualSideToDecodedSide2CellEquiv_target_iff
    (u v : GeometricSideCell S) :
    geometricSideRelation S .target u v ↔
      geometricSideRelation
        (lMinusDecodedSide2 (W := W) (h := h) (k := k)
          (longest := longest) hτ hqMode hfin) .target
        (lMinusActualSideToDecodedSide2CellEquiv hτ hp P hqMode Tpath hfin hleft hk u)
        (lMinusActualSideToDecodedSide2CellEquiv hτ hp P hqMode Tpath hfin hleft hk v) := by
  cases u <;> cases v <;> rfl

/-- Helper toward Lemma 5.5: the corrected decoded rotation is preserved by
the actual to decoded cell equivalence, using the reconnected Whole11 rotation. -/
theorem lMinusActualSideToDecodedSide2CellEquiv_rotation_iff
    (u v : GeometricSideCell S) :
    geometricSideRelation S .rotation u v ↔
      geometricSideRelation
        (lMinusDecodedSide2 (W := W) (h := h) (k := k)
          (longest := longest) hτ hqMode hfin) .rotation
        (lMinusActualSideToDecodedSide2CellEquiv hτ hp P hqMode Tpath hfin hleft hk u)
        (lMinusActualSideToDecodedSide2CellEquiv hτ hp P hqMode Tpath hfin hleft hk v) := by
  let F := lMinusDecodedSide2ToGeometricCellEquiv
    hτ hp P hqMode Tpath hfin hleft hk
  have hr := lMinusDecodedSide2_rotation_iff hτ hp P hqMode Tpath
    hfin hleft hk (F.symm u) (F.symm v)
  simpa [F, lMinusActualSideToDecodedSide2CellEquiv] using hr.symm

end ActualToDecodedSide2





































end DirectedDistances.PaperProofs.Section5
