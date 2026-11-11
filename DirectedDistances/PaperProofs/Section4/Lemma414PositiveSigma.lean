module

public import DirectedDistances.PaperProofs.Section4.SelectedCutCodeDistanceLaw
public import DirectedDistances.PaperProofs.Section4.ThinIndRenewalProvider
public import Mathlib.Probability.Independence.Conditional

import DirectedDistances.PaperProofs.Section4.SelectedCutAmbientFactorization

/-! Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
selected-time restriction and uses a measurable version of the future and code-distance
observation. It does not include the zero-time branch or identify the source submaps. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open MeasureTheory ProbabilityTheory

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
the two selected-cut past outputs are conditionally independent given a measurable
version of the future and code-distance observation. -/
theorem selectedCutPastCuts_positive_condIndepFun_sigma
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) (hk : 1 ≤ k)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    let μ := conditionedVectorPathLaw 0 0
    let ν := μ.restrict {p | 0 < selectedCutTime T k p}
    let B := selectedCutCodeDistanceConditioning x T k
    let B' := (aemeasurable_selectedCutCodeDistanceConditioning x T k hT).mk B
    let C := selectedCutPastCuts x T k
    ProbabilityTheory.CondIndepFun (MeasurableSpace.comap B' inferInstance)
      ((aemeasurable_selectedCutCodeDistanceConditioning x T k hT).measurable_mk.comap_le)
      (fun p => (C p).1) (fun p => (C p).2) ν := by
  classical
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let ν := μ.restrict {p | 0 < selectedCutTime T k p}
  let B := selectedCutCodeDistanceConditioning x T k
  let hB : AEMeasurable B μ :=
    aemeasurable_selectedCutCodeDistanceConditioning x T k hT
  let B' := hB.mk B
  let C := selectedCutPastCuts x T k
  have hB'm : Measurable B' := hB.measurable_mk
  have hB' : B' =ᵐ[μ] B := hB.ae_eq_mk.symm
  have hC : Measurable C := measurable_selectedCutPastCuts x T k hT
  let κ := condDistrib (fun p => (C p).1) B' ν ×ₖ
    condDistrib (fun p => (C p).2) B' ν
  have hFactor : condDistrib C B' ν =ᵐ[ν.map B'] κ := by
    have hp := selectedCutCodeDistance_positive_conditionalIndependence_measurableVersion
      x T k hk hT B' hB'
    change condDistrib C B' (μ.restrict {p | 0 < selectedCutTime T k p}) =ᵐ[
      (μ.restrict {p | 0 < selectedCutTime T k p}).map B']
      (fun b =>
        (condDistrib (fun p => (C p).1) B' (μ.restrict
          {p | 0 < selectedCutTime T k p}) b).prod
        (condDistrib (fun p => (C p).2) B' (μ.restrict
          {p | 0 < selectedCutTime T k p}) b)) at hp
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
  exact (ProbabilityTheory.condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
    (μ := ν) (f := fun p => (C p).1) (g := fun p => (C p).2)
    hC.fst hC.snd hB'm).2 hJoint

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
conditional-independence statement for the canonical renewal-time selector. -/
theorem renewalTime_selectedCutPastCuts_positive_condIndepFun_sigma
    (x : XDP) (k : ℕ) (hk : 1 ≤ k) :
    let T := DirectedDistances.Paper.Section4.renewalTime
    let hT := DirectedDistances.PaperProofs.Section4.renewalTime_positiveSuccessTime
    let μ := conditionedVectorPathLaw 0 0
    let ν := μ.restrict {p | 0 < selectedCutTime T k p}
    let B := selectedCutCodeDistanceConditioning x T k
    let B' := (aemeasurable_selectedCutCodeDistanceConditioning x T k hT).mk B
    let C := selectedCutPastCuts x T k
    ProbabilityTheory.CondIndepFun (MeasurableSpace.comap B' inferInstance)
      ((aemeasurable_selectedCutCodeDistanceConditioning x T k hT).measurable_mk.comap_le)
      (fun p => (C p).1) (fun p => (C p).2) ν := by
  exact selectedCutPastCuts_positive_condIndepFun_sigma x
    DirectedDistances.Paper.Section4.renewalTime k hk
    DirectedDistances.PaperProofs.Section4.renewalTime_positiveSuccessTime

end DirectedDistances.PaperProofs.Section4
