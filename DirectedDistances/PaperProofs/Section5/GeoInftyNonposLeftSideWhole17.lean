/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideWhole16

 

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

local notation "X" => (ite (longest = true) XDP.ldp XDP.sdp)
local notation "rL" => decodeLMinus X k (leftSideObsNonpos X k W)
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode :
  selectedCutCoherentDomain X renewalTime renewalTime_positiveSuccessTime)
local notation "Q" => geometricSideSubmap X renewalTime renewalTime_positiveSuccessTime ThinMapSide.left qL
local notation "hf" => lMinus_primed_observation_finiteIncidence hτ hfin
local notation "V" => lMinusCodeToGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "E" => lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "T" => Equiv.sumCongr V E

/-- Helper toward Lemma 5.5: the root relation agrees on intrinsic code and
actual glued cells under the proved vertex identification. -/
theorem lMinusCodeRelation2_root_glued_iff
    (a b : Sum (LMinusCodeGluedVertex rL Q) (LMinusCodeGluedDart rL Q)) :
    lMinusCodeRelation2 X rL qL hf .root a b ↔
      lMinusGluedIncidenceRelation hτ hqMode .root (T a) (T b) := by
  let r₀ : LMinusCodeGluedVertex rL Q :=
    ⟨⟦Sum.inr (Q).root⟧,
      Or.inr ⟨⟨(Q).root, lMinus_hatted_root_mem X qL⟩, rfl⟩⟩
  have hV : V r₀ = (⟦Sum.inr ⟨(Q).root, lMinus_hatted_root_mem X qL⟩⟧ :
      LMinusGluedVertex hτ hqMode) := by
    apply ((V).symm).injective
    rw [Equiv.symm_apply_apply]
    rfl
  have hroot : Setoid.kerLift (lMinusBlockVertexImage hτ hqMode)
      (V r₀) = boundaryGluingHatVertexMap W h k hτ 0 := by
    rw [hV]
    change boundaryGluingHatVertexMap W h k hτ 0 = _
    rw [boundaryGluingHatVertexMap_zero hτ]
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      change (a = r₀) ↔
        Setoid.kerLift (lMinusBlockVertexImage hτ hqMode) (V a) =
          boundaryGluingHatVertexMap W h k hτ 0
      rw [← hroot]
      constructor
      · rintro rfl
        rfl
      · intro hab
        apply (V).injective
        exact Setoid.kerLift_injective (lMinusBlockVertexImage hτ hqMode) hab
    | inr b =>
      change (a = r₀) ↔
        Setoid.kerLift (lMinusBlockVertexImage hτ hqMode) (V a) =
          boundaryGluingHatVertexMap W h k hτ 0
      rw [← hroot]
      constructor
      · rintro rfl
        rfl
      · intro hab
        apply (V).injective
        exact Setoid.kerLift_injective (lMinusBlockVertexImage hτ hqMode) hab
  | inr a => cases b <;> rfl























































































































































































































end ActualToDecodedSide2

end DirectedDistances.PaperProofs.Section5
