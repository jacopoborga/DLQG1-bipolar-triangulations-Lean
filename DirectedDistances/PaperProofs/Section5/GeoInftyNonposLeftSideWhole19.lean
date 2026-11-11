/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideWhole18
public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusFaceClassification

 

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
local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "D" => lMinusDecodedSide2 (W := W) (h := h) (k := k)
  (longest := longest) hτ hqMode hfin
local notation "hf" => lMinus_primed_observation_finiteIncidence hτ hfin
local notation "C" => lMinusCodeSide2 X rL qL hf

/-- Helper toward Lemma 5.5: the exterior left-boundary marking uses a
reversed dart, so no cell carrying that marking can be oriented. -/
theorem m0GeodesicSide_left_boundary_not_oriented
    (i : ℕ) (u v : GeometricSideCell S)
    (hb : geometricSideRelation S (.boundary i) u v) :
    ¬ geometricSideRelation S .oriented u v := by
  cases u with
  | inl a => exact False.elim hb
  | inr d =>
    intro ho
    have hb' : (boundaryOuterEdge (shiftedStream W 0) h (k - 1 - (i : ℤ)), true) =
        d.val := hb
    have hs : d.val.2 = true := (congrArg Prod.snd hb').symm
    have ho' : EdgePresent (shiftedStream W 0) d.val.1 ∧ d.val.2 = false := ho
    rw [hs] at ho'
    exact Bool.noConfusion ho'.2

/-- Helper toward Lemma 5.5: the code side marks a forward hatted interface
dart, and that dart is directed in the hatted block. -/
theorem lMinusCodeSide2_boundary_oriented
    (i : ℕ) :
    ∃ u : GeometricSideCell C,
      geometricSideRelation C (.boundary i) u u ∧
      geometricSideRelation C .oriented u u := by
  let b := lMinusCodeBoundaryDart rL qL (i, false)
  let u := lMinusCodeSide2CellEquiv X rL qL hf (Sum.inr b)
  refine ⟨u, ?_, ?_⟩
  · exact (lMinusCodeSide2CellEquiv_relation_iff X rL qL hf
      (.boundary i) (.inr b) (.inr b)).mpr rfl
  · apply (lMinusCodeSide2CellEquiv_relation_iff X rL qL hf
      .oriented (.inr b) (.inr b)).mpr
    change lMinusCodeEdgePresent rL Q _ b.1 ∧ b.2 = false
    refine ⟨Or.inr ⟨⟨((Q).boundary i).1, lMinus_hatted_boundary_mem X qL i⟩,
      ?_, rfl⟩, rfl⟩
    change EdgePresent (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W)))
      ((Q).boundary i).1
    rw [boundaryGluing_decoded_stream W h k hτ, lMinus_hatted_boundary hτ hqMode i]
    exact hatCodes_edge_present (boundaryGluingFutureStream W h k) hτ _

/-- Helper toward Lemma 5.5: the code-side boundary tag obstructs every
marked isomorphism to the actual exterior-marked left side. -/
theorem boundaryGluing_nonpos_left_not_markedIso_lMinusCodeSide2 :
    ¬ Nonempty (GeometricSideMarkedIso S C) := by
  rintro ⟨phi⟩
  obtain ⟨u, hb, ho⟩ := lMinusCodeSide2_boundary_oriented hτ hqMode hfin 0
  let a := phi.equiv.symm u
  have hb' : geometricSideRelation S (.boundary 0) a a := by
    apply (phi.relation_iff (.boundary 0) a a).mpr
    simpa only [a, Equiv.apply_symm_apply] using hb
  have ho' : geometricSideRelation S .oriented a a := by
    apply (phi.relation_iff .oriented a a).mpr
    simpa only [a, Equiv.apply_symm_apply] using ho
  exact m0GeodesicSide_left_boundary_not_oriented hp P 0 a a hb' ho'

/-- Helper toward Lemma 5.5: equality with the code side transfers the
boundary obstruction to the exact corrected decoder in the recorded target. -/
theorem boundaryGluing_nonpos_left_not_markedIso_lMinusDecodedSide2 :
    ¬ Nonempty (GeometricSideMarkedIso S D) := by
  rw [lMinusDecodedSide2_eq_codeSide2]
  exact boundaryGluing_nonpos_left_not_markedIso_lMinusCodeSide2 hτ hp P hqMode hfin


















































end ActualToDecodedSide2
end DirectedDistances.PaperProofs.Section5
