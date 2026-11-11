module

public import DirectedDistances.PaperProofs.Section4.SelectedCutCodeDistanceLaw
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

import Mathlib.Probability.Independence.Conditional

/-! Supporting lemmas for paper labels `prop-thin-ind` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap
open MeasureTheory ProbabilityTheory
open scoped ENNReal





theorem selectedCutTime_positive_iff_future_negative_ae
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) (hk : 1 ≤ k)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    {p | 0 < selectedCutTime T k p} =ᵐ[conditionedVectorPathLaw 0 0]
      {p | (selectedCutFuture T k p 0).2 < 0} := by
  let μ := conditionedVectorPathLaw 0 0
  let E : PositiveBranchIx k → Set (ℕ → ℤ × ℤ) := fun i =>
    (fun p => conditionedVectorShift
      (conditionedSecondCoordinateFirstHit i.1.2 p).toNat p) ⁻¹'
      firstHitPositiveBranchFuture i.1.1 i.1.2 k
  have hpos := selectedCutTime_positive_event_ae T k hk hT
  have hbranches : ∀ᵐ p ∂μ, ∀ i : PositiveBranchIx k,
      (selectedCutTime T k p = conditionedSecondCoordinateFirstHit i.1.2 p ∧
        conditionedSecondCoordinateFirstHit i.1.2 p < ⊤ ∧
        (p (conditionedSecondCoordinateFirstHit i.1.2 p).toNat).1 =
          (i.1.1 : ℤ)) ↔
        (conditionedSecondCoordinateFirstHit i.1.2 p < ⊤ ∧ p ∈ E i) := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [selectedCutTime_positiveBranch_event_ae T k i.1.2 i.1.1
      i.2.1 i.2.2 hT] with p hp
    exact Iff.of_eq hp
  have hfinite : ∀ᵐ p ∂μ, ∀ i : PositiveBranchIx k,
      conditionedSecondCoordinateFirstHit i.1.2 p < ⊤ :=
    ae_all_iff.mpr fun i => firstHitPastMap_finite_hit_ae i.1.2 i.2.1
  filter_upwards [hpos, hbranches, hfinite, conditionedVectorPathLaw_ae_legal]
    with p hp hb hf hlegal
  apply propext
  constructor
  · intro hs
    have hpUnion : p ∈ ⋃ i, E i := (Iff.of_eq hp).mp hs
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpUnion
    have hsrc := (hb i).mpr ⟨hf i, hi⟩
    obtain ⟨hsel, _, _⟩ := hsrc
    have hfuture : selectedCutFuture T k p 0 =
        conditionedVectorShift
          (conditionedSecondCoordinateFirstHit i.1.2 p).toNat p 0 := by
      change conditionedVectorShift (selectedCutTime T k p).toNat p 0 = _
      rw [hsel]
    have hpoint :
        conditionedVectorShift
            (conditionedSecondCoordinateFirstHit i.1.2 p).toNat p 0 =
          ((i.1.1 : ℤ), -(i.1.2 : ℤ)) := by
      change _ ∈ firstHitPositiveBranchFuture i.1.1 i.1.2 k at hi
      exact hi.2
    rw [hfuture, hpoint]
    exact neg_lt_zero.mpr (Int.natCast_pos.mpr i.2.1)
  · intro hn
    by_contra hnot
    have hle : selectedCutTime T k p ≤ 0 := le_of_not_gt hnot
    have hzero : selectedCutTime T k p = 0 := le_antisymm hle bot_le
    have hfuture : selectedCutFuture T k p 0 = p 0 := by
      simp [selectedCutFuture, hzero, conditionedVectorShift]
    rw [hfuture, hlegal.1] at hn
    exact (lt_irrefl 0 hn)





theorem selectedCutCodeDistance_measurable_positiveSet_representative
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) (hk : 1 ≤ k)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    ∃ B' : (ℕ → ℤ × ℤ) → (ℕ → ℤ × ℤ) × ℕ,
      Measurable B' ∧
      B' =ᵐ[conditionedVectorPathLaw 0 0]
        selectedCutCodeDistanceConditioning x T k ∧
      {p | 0 < selectedCutTime T k p} =ᵐ[conditionedVectorPathLaw 0 0]
        {p | ((B' p).1 0).2 < 0} ∧
      MeasurableSet[MeasurableSpace.comap B' inferInstance]
        {p | ((B' p).1 0).2 < 0} := by
  let μ := conditionedVectorPathLaw 0 0
  let B := selectedCutCodeDistanceConditioning x T k
  have hB : AEMeasurable B μ :=
    aemeasurable_selectedCutCodeDistanceConditioning x T k hT
  let B' := hB.mk B
  have hcoord : Measurable (fun b : (ℕ → ℤ × ℤ) × ℕ => (b.1 0).2) :=
    measurable_snd.comp ((measurable_pi_apply 0).comp measurable_fst)
  have htest : MeasurableSet {b : (ℕ → ℤ × ℤ) × ℕ | (b.1 0).2 < 0} :=
    hcoord (measurableSet_Iio)
  have hrep : {p | ((B' p).1 0).2 < 0} =ᵐ[μ]
      {p | (selectedCutFuture T k p 0).2 < 0} := by
    have hfun : ∀ᵐ p ∂μ, B p = B' p := hB.ae_eq_mk
    filter_upwards [hfun] with p hp
    change B p = B' p at hp
    rw [← hp]
    rfl
  refine ⟨B', hB.measurable_mk, hB.ae_eq_mk.symm, ?_, ?_⟩
  · exact (selectedCutTime_positive_iff_future_negative_ae T k hk hT).trans
      hrep.symm
  · apply MeasurableSpace.measurableSet_comap.mpr
    refine ⟨{b : (ℕ → ℤ × ℤ) × ℕ | (b.1 0).2 < 0}, htest, ?_⟩
    rfl




theorem selectedCutCodeDistance_positive_conditionalIndependence_measurableVersion
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) (hk : 1 ≤ k)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (B' : (ℕ → ℤ × ℤ) → (ℕ → ℤ × ℤ) × ℕ)
    (hB' : B' =ᵐ[conditionedVectorPathLaw 0 0]
      selectedCutCodeDistanceConditioning x T k) :
    let ν := (conditionedVectorPathLaw 0 0).restrict
      {p | 0 < selectedCutTime T k p}
    let C := selectedCutPastCuts x T k
    condDistrib C B' ν =ᵐ[ν.map B'] fun b =>
      (condDistrib (fun p => (C p).1) B' ν b).prod
        (condDistrib (fun p => (C p).2) B' ν b) := by
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let S := {p | 0 < selectedCutTime T k p}
  let ν := μ.restrict S
  let B := selectedCutCodeDistanceConditioning x T k
  let C := selectedCutPastCuts x T k
  have hBν : B' =ᵐ[ν] B := ae_restrict_of_ae hB'
  have hmap : ν.map B' = ν.map B := Measure.map_congr hBν
  have hcond := selectedCutCodeDistance_positive_conditionalIndependence
    x T k hk hT
  have hcond' : condDistrib C B' ν =ᵐ[ν.map B]
      fun b => (condDistrib (fun p => (C p).1) B' ν b).prod
        (condDistrib (fun p => (C p).2) B' ν b) := by
    filter_upwards [hcond] with b hb
    have hleft := condDistrib_congr_right (mβ := inferInstance)
      (X := B') (X' := B) (Y := C) hBν
    have hfst := condDistrib_congr_right (mβ := inferInstance) (X := B') (X' := B)
      (Y := fun p => (C p).1) hBν
    have hsnd := condDistrib_congr_right (mβ := inferInstance) (X := B') (X' := B)
      (Y := fun p => (C p).2) hBν
    rw [hleft, hfst, hsnd]
    exact hb
  rw [hmap]
  exact hcond'




theorem selectedCutCodeDistance_ambient_indicator_factorization
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) (hk : 1 ≤ k)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (B' : (ℕ → ℤ × ℤ) → (ℕ → ℤ × ℤ) × ℕ) (hB'm : Measurable B')
    (hB' : B' =ᵐ[conditionedVectorPathLaw 0 0]
      selectedCutCodeDistanceConditioning x T k)
    (A B : Set (Option (Σ s : ℕ, KMSW.AllBoltzmannSpace s)))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (E : Set (ℕ → ℤ × ℤ))
    (hE : MeasurableSet[MeasurableSpace.comap B' inferInstance] E)
    (hES : E ⊆ {p | ((B' p).1 0).2 < 0}) :
    let μ := conditionedVectorPathLaw 0 0
    let F := MeasurableSpace.comap B' inferInstance
    let C := selectedCutPastCuts x T k
    let A' := (fun p => (C p).1) ⁻¹' A
    let B'' := (fun p => (C p).2) ⁻¹' B
    μ[(A' ∩ B'').indicator (1 : (ℕ → ℤ × ℤ) → ℝ) | F] * E.indicator 1 =ᵐ[μ]
      μ[A'.indicator (1 : (ℕ → ℤ × ℤ) → ℝ) | F] *
        μ[B''.indicator (1 : (ℕ → ℤ × ℤ) → ℝ) | F] * E.indicator 1 := by
  classical
  let m0 : MeasurableSpace (ℕ → ℤ × ℤ) := inferInstance
  let μ := conditionedVectorPathLaw 0 0
  let S := {p | 0 < selectedCutTime T k p}
  let S' := {p | ((B' p).1 0).2 < 0}
  let ν := μ.restrict S'
  let C := selectedCutPastCuts x T k
  let A' := (fun p => (C p).1) ⁻¹' A
  let B'' := (fun p => (C p).2) ⁻¹' B
  have hF : (MeasurableSpace.comap B' inferInstance) ≤ m0 := hB'm.comap_le
  have hS' : MeasurableSet[(MeasurableSpace.comap B' inferInstance)] S' := by
    have hc : Measurable (fun b : (ℕ → ℤ × ℤ) × ℕ => (b.1 0).2) :=
      measurable_snd.comp ((measurable_pi_apply 0).comp measurable_fst)
    exact ⟨{b | (b.1 0).2 < 0}, hc measurableSet_Iio, rfl⟩
  have hrep : S' =ᵐ[μ] {p | (selectedCutFuture T k p 0).2 < 0} := by
    filter_upwards [hB'] with p hp
    change B' p = selectedCutCodeDistanceConditioning x T k p at hp
    change (((B' p).1 0).2 < 0) = ((selectedCutFuture T k p 0).2 < 0)
    rw [hp]
    rfl
  have hS : S =ᵐ[μ] S' :=
    (selectedCutTime_positive_iff_future_negative_ae T k hk hT).trans hrep.symm
  have hν : μ.restrict S = ν := Measure.restrict_congr_set hS
  have hC : Measurable C := measurable_selectedCutPastCuts x T k hT
  let κ := condDistrib (fun p => (C p).1) B' ν ×ₖ
    condDistrib (fun p => (C p).2) B' ν
  have hFactor : condDistrib C B' ν =ᵐ[ν.map B'] κ := by
    have hp := selectedCutCodeDistance_positive_conditionalIndependence_measurableVersion
      x T k hk hT B' hB'
    change condDistrib C B' (μ.restrict S) =ᵐ[(μ.restrict S).map B']
      (fun b => (condDistrib (fun p => (C p).1) B' (μ.restrict S) b).prod
        (condDistrib (fun p => (C p).2) B' (μ.restrict S) b)) at hp
    simp only [hν] at hp
    filter_upwards [hp] with b hb
    change condDistrib C B' ν b =
      (condDistrib (fun p => (C p).1) B' ν ×ₖ
        condDistrib (fun p => (C p).2) B' ν) b
    rw [Kernel.prod_apply]
    exact hb
  have hPair := (condDistrib_ae_eq_iff_measure_eq_compProd
    hB'm.aemeasurable hC.aemeasurable κ).mp hFactor
  have hJoint : ν.map (fun p => (B' p, C p)) =
      (Kernel.id ×ₖ (condDistrib (fun p => (C p).1) B' ν ×ₖ
        condDistrib (fun p => (C p).2) B' ν)) ∘ₘ ν.map B' := by
    rw [← Measure.compProd_eq_comp_prod]
    exact hPair
  have hind : CondIndepFun (MeasurableSpace.comap B' inferInstance) hF
      (fun p => (C p).1) (fun p => (C p).2) ν :=
    (condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
      (μ := ν) hC.fst hC.snd hB'm).2 hJoint
  have hfac : ν[(A' ∩ B'').indicator (1 : (ℕ → ℤ × ℤ) → ℝ) |
      MeasurableSpace.comap B' inferInstance] =ᵐ[ν]
      ν[A'.indicator (1 : (ℕ → ℤ × ℤ) → ℝ) |
      MeasurableSpace.comap B' inferInstance] *
        ν[B''.indicator (1 : (ℕ → ℤ × ℤ) → ℝ) |
      MeasurableSpace.comap B' inferInstance] :=
    (condIndepFun_iff_condExp_inter_preimage_eq_mul
      (mΩ := m0) hC.fst hC.snd).mp hind A B hA hB
  have hAm : MeasurableSet[m0] A' := hC.fst hA
  have hBm : MeasurableSet[m0] B'' := hC.snd hB
  have hleft := condExp_restrict_ae_eq_restrict (m0 := m0) (μ := μ) hF hS'
    ((integrable_const (1 : ℝ)).indicator hAm)
  have hright := condExp_restrict_ae_eq_restrict (m0 := m0) (μ := μ) hF hS'
    ((integrable_const (1 : ℝ)).indicator hBm)
  have hinter := condExp_restrict_ae_eq_restrict (m0 := m0) (μ := μ) hF hS'
    ((integrable_const (1 : ℝ)).indicator (hAm.inter hBm))
  have hamb : μ[(A' ∩ B'').indicator (1 : (ℕ → ℤ × ℤ) → ℝ) |
      MeasurableSpace.comap B' inferInstance] =ᵐ[ν]
      μ[A'.indicator (1 : (ℕ → ℤ × ℤ) → ℝ) |
      MeasurableSpace.comap B' inferInstance] *
        μ[B''.indicator (1 : (ℕ → ℤ × ℤ) → ℝ) |
      MeasurableSpace.comap B' inferInstance] := by
    exact hinter.symm.trans (hfac.trans (hleft.mul hright))
  have honE := ae_restrict_of_ae_restrict_of_subset hES hamb
  have hall := (ae_restrict_iff' (hF E hE)).mp honE
  change μ[(A' ∩ B'').indicator (1 : (ℕ → ℤ × ℤ) → ℝ) |
      MeasurableSpace.comap B' inferInstance] * E.indicator 1 =ᵐ[μ]
    μ[A'.indicator (1 : (ℕ → ℤ × ℤ) → ℝ) |
      MeasurableSpace.comap B' inferInstance] *
      μ[B''.indicator (1 : (ℕ → ℤ × ℤ) → ℝ) |
      MeasurableSpace.comap B' inferInstance] * E.indicator 1
  filter_upwards [hall] with p hp
  by_cases he : p ∈ E
  · simp only [Pi.mul_apply, Set.indicator_of_mem he, Pi.one_apply, mul_one]
    exact hp he
  · simp only [Pi.mul_apply, Set.indicator_of_notMem he, mul_zero]

end DirectedDistances.PaperProofs.Section4
