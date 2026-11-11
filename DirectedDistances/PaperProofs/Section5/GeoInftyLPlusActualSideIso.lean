/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSideMeasurable6
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideRootStar3
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideBoundarySeparation7

/-! Helper toward Lemma 5.5 (`lem-geo-infty-ind`),

This file compares the actual nonnegative left side with the fixed-witness
code-block side. Rotation identification and comparison between witnesses
remain separate obligations. No numbered paper result is asserted. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}
  (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
    (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : 0 ≤ k)

local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "B" => lPlusCodeBlockSide hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: the code-block vertex carrier is exactly the
actual left-side carrier, including the attachment root at index zero. -/
theorem lPlusCodeBlockSide_vertices_eq_actual : (B).vertices = (S).vertices :=
  lPlusBlockVertexImage_range hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: the code-block geometric edge carrier equals
the actual left-side carrier, with both missing edges and multiedge IDs kept. -/
theorem lPlusCodeBlockSide_edges_eq_actual : (B).edges = (S).edges := by
  change {e | ∃ b : Bool, (e, b) ∈ Set.range
    (lPlusBlockDartImage
      (M := lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode) hτ)} = _
  rw [lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk]
  ext e
  exact ⟨fun ⟨_, he⟩ => he, fun he => ⟨false, he⟩⟩

/- Helper toward Lemma 5.5: every nonrotation field agrees with the actual
side. This does not identify the code-block rotation. The displayed record -/
theorem lPlusCodeBlockSide_nonrotation_fields :
    { B with rotation := (S).rotation } = S := by
  have hv := lPlusCodeBlockSide_vertices_eq_actual hτ hp P hqMode Tpath hfin hleft hk
  have he := lPlusCodeBlockSide_edges_eq_actual hτ hp P hqMode Tpath hfin hleft hk
  change { S with vertices := (B).vertices, edges := (B).edges } = S
  rw [hv, he]

/-- Helper toward Lemma 5.5: the actual side and the fixed-witness code
assembly have equivalent cell carriers. This equivalence preserves each
permanent vertex ID, edge ID, and endpoint bit; it asserts no rotation law. -/
@[expose] noncomputable def lPlusActualCodeBlockCellEquiv :
    GeometricSideCell S ≃ GeometricSideCell B :=
  Equiv.sumCongr
    (Set.equivOfEq
      (lPlusCodeBlockSide_vertices_eq_actual hτ hp P hqMode Tpath hfin hleft hk).symm)
    (Set.equivOfEq (show
        {d : ℕ × Bool | d.1 ∈ (S).edges} =
          {d : ℕ × Bool | d.1 ∈ (B).edges} by
      rw [lPlusCodeBlockSide_edges_eq_actual hτ hp P hqMode Tpath hfin hleft hk]))

/-- Helper toward Lemma 5.5: the cell equivalence preserves the permanent
ID of each actual-side vertex. -/
theorem lPlusActualCodeBlockCellEquiv_vertex (v : (S).vertices) :
    lPlusActualCodeBlockCellEquiv hτ hp P hqMode Tpath hfin hleft hk (.inl v) =
      .inl ⟨v.val, by
        rw [lPlusCodeBlockSide_vertices_eq_actual hτ hp P hqMode Tpath hfin hleft hk]
        exact v.property⟩ := rfl

/-- Helper toward Lemma 5.5: the cell equivalence preserves the permanent
edge ID and endpoint bit of each actual-side dart. -/
theorem lPlusActualCodeBlockCellEquiv_dart
    (d : {d : ℕ × Bool // d.1 ∈ (S).edges}) :
    lPlusActualCodeBlockCellEquiv hτ hp P hqMode Tpath hfin hleft hk (.inr d) =
      .inr ⟨d.val, by
        rw [lPlusCodeBlockSide_edges_eq_actual hτ hp P hqMode Tpath hfin hleft hk]
        exact d.property⟩ := rfl






















































































































end DirectedDistances.PaperProofs.Section5
