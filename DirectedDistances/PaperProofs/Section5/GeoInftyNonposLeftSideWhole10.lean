/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideWhole9
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

local notation "w" => shiftedStream W 0
local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "VH" => boundaryGluingHatVertexMap W h k hτ
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode :
  selectedCutCoherentDomain (ite (longest = true) XDP.ldp XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime)
local notation "rL" => decodeLMinus (ite (longest = true) XDP.ldp XDP.sdp) k
  (leftSideObsNonpos (ite (longest = true) XDP.ldp XDP.sdp) k W)
local notation "Q" => geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
  renewalTime renewalTime_positiveSuccessTime ThinMapSide.left qL
local notation "E" => lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "G" => lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "D" => lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "Φ" => lMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "hf" => lMinus_primed_observation_finiteIncidence hτ hfin

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: a vertex cell cannot be the source of a
rotation relation, on either the code splice or the geometric side. -/
theorem lMinusSpliceRotationRelation_vertex_case
    (u : LMinusGluedVertex hτ hqMode)
    (v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    lMinusSpliceRotationRelation hτ hp P hqMode Tpath hfin hleft hk
        (.inl u) v ↔
      geometricSideRelation S .rotation (Φ (.inl u)) (Φ v) := by
  cases v <;> rfl

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the initial-only reconnection and the prescribed
splice have the same value at every dart whose source is not the initial
interface vertex. -/
theorem lMinusCodeInitialSplicedRotation_eq_splice_of_source_ne_initial
    (d : LMinusCodeGluedDart rL Q)
    (hsource : kmswLimitDartVertex w (D d).val ≠ VH 0) :
    lMinusCodeInitialSplicedRotation rL qL hf d =
      lMinusCodeSpliceRotation rL qL hf d := by
  rw [lMinusCodeInitialSplicedRotation_eq_adjusted_outside_initial
    hτ hp P hqMode Tpath hfin hleft hk d hsource]
  apply lMinusCodeInitialAdjustedRotation_apply_of_ne rL qL hf d
  · intro he
    apply hsource
    rw [he]
    change kmswLimitDartVertex w
      (D (lMinusCodeHattedDart rL Q
        ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩)).val = VH 0
    rw [lMinusCodeGluedDartEquiv_hatted, lMinus_hatted_dart_endpoint hτ,
      (lMinus_hatted_boundary_source_iff hqMode 0 false).mpr ⟨rfl, rfl⟩]
  · intro he
    apply hsource
    rw [he, lMinusCodeHattedRotation_initial_predecessor,
      lMinusCodeGluedDartEquiv_hatted, lMinus_hatted_dart_endpoint hτ]
    exact congrArg VH (lMinusHattedRotation_initial_predecessor_vertex _ qL)

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the prescribed splice rotation agrees with the
geometric left-side rotation from each noninitial dart, for every target cell. -/
theorem lMinusSpliceRotationRelation_rotation_iff_noninitial_dart
    (d : LMinusGluedDart hτ hqMode)
    (v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode))
    (hsource : kmswLimitDartVertex w (G d).val ≠ VH 0) :
    lMinusSpliceRotationRelation hτ hp P hqMode Tpath hfin hleft hk
        (.inr d) v ↔
      geometricSideRelation S .rotation (Φ (.inr d)) (Φ v) := by
  cases v with
  | inl v => rfl
  | inr e =>
      have hmap : G d = D ((E).symm d) := by
        have he := lMinusCodeToGluedDartEquiv_equiv
          hτ hp P hqMode Tpath hfin hleft hk ((E).symm d)
        rw [Equiv.apply_symm_apply] at he
        exact he
      have hsourceCode : kmswLimitDartVertex w (D ((E).symm d)).val ≠ VH 0 := by
        rw [← congrArg Subtype.val hmap]
        exact hsource
      have hrotation : lMinusGluedInitialSplicedRotation
          hτ hp P hqMode Tpath hfin hleft hk d =
          lMinusGluedSpliceRotation hτ hp P hqMode Tpath hfin hleft hk d := by
        change E (lMinusCodeInitialSplicedRotation rL qL hf ((E).symm d)) =
          E (lMinusCodeSpliceRotation rL qL hf ((E).symm d))
        exact congrArg E (lMinusCodeInitialSplicedRotation_eq_splice_of_source_ne_initial
          hτ hp P hqMode Tpath hfin hleft hk ((E).symm d) hsourceCode)
      have hiff := lMinusGluedCellEquiv_rotation_iff
        hτ hp P hqMode Tpath hfin hleft hk (.inr d) (.inr e)
      change lMinusGluedInitialSplicedRotation
          hτ hp P hqMode Tpath hfin hleft hk d = e ↔
        geometricSideRelation S .rotation (Φ (.inr d)) (Φ (.inr e)) at hiff
      change lMinusGluedSpliceRotation
          hτ hp P hqMode Tpath hfin hleft hk d = e ↔
        geometricSideRelation S .rotation (Φ (.inr d)) (Φ (.inr e))
      rw [← hrotation]
      exact hiff

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: after splitting vertex and dart cells, the
rotation equivalence holds for every pair whose dart source is noninitial. -/
theorem lMinusSpliceRotationRelation_rotation_iff_noninitial_source
    (u v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode))
    (hsource : ∀ d, u = .inr d →
      kmswLimitDartVertex w (G d).val ≠ VH 0) :
    lMinusSpliceRotationRelation hτ hp P hqMode Tpath hfin hleft hk u v ↔
      geometricSideRelation S .rotation (Φ u) (Φ v) := by
  cases u with
  | inl u =>
      exact lMinusSpliceRotationRelation_vertex_case
        hτ hp P hqMode Tpath hfin hleft hk u v
  | inr d =>
      exact lMinusSpliceRotationRelation_rotation_iff_noninitial_dart
        hτ hp P hqMode Tpath hfin hleft hk d v (hsource d rfl)

/-- Helper toward Lemma 5.5: the boundary correction fixes the initial
interface dart. -/
theorem lMinusBoundaryCorner_initial_fixed :
    lMinusBoundaryCorner (0, false) = (0, false) := rfl

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the raw initial successor is correct precisely
when the hatted rotation fixes the initial boundary dart. -/
theorem lMinusSpliceRotationRelation_initial_root_fixed_iff :
    let d : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
    lMinusSpliceRotationRelation hτ hp P hqMode Tpath hfin hleft hk
      (.inr (E (lMinusCodeBoundaryDart rL qL (0, false))))
      (.inr (E (lMinusCodePrimedDart rL Q (0, true)))) ↔
      lMinusHattedRotation (ite (longest = true) XDP.ldp XDP.sdp) qL d = d := by
  exact lMinusSpliceRotationRelation_initial_root_iff
    hτ hp P hqMode Tpath hfin hleft hk











































end GeometricGluing

end DirectedDistances.PaperProofs.Section5
