module

public import DirectedDistances.PaperProofs.Section4.Lemma414PositiveSigma
public import DirectedDistances.PaperProofs.Section4.Lemma414FiltrationBridge
public import DirectedDistances.PaperProofs.Section4.Lemma414SideCarrier
public import DirectedDistances.PaperProofs.Section4.SelectedCutAmbientFactorization

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.PlanarMap
open MeasureTheory ProbabilityTheory

local notation "Ω" => (ℕ → ℤ × ℤ)
local notation "μ" => conditionedVectorPathLaw 0 0
local notation "T" => (fun m p => DirectedDistances.Paper.Section4.renewalTime m p)
local notation "hT" => renewalTime_positiveSuccessTime

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
conditioning variable agrees almost surely with the source observation. -/
theorem sourceCutObservation_ae_eq_measurableConditioningVersion
    (x : XDP) (k : ℕ) (hk : 1 ≤ k) :
    let B := selectedCutCodeDistanceConditioning x T k
    let hB := aemeasurable_selectedCutCodeDistanceConditioning x T k hT
    sourceCutObservation x k =ᵐ[μ] hB.mk B := by
  let B := selectedCutCodeDistanceConditioning x T k
  let hB := aemeasurable_selectedCutCodeDistanceConditioning x T k hT
  have hraw := sourceCutObservation_ae_eq x k hk
  exact hraw.trans hB.ae_eq_mk

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
a representative measurable in the existing source cut filtration. -/
theorem selectedCutPositiveSet_sourceCutFiltration_measurable
    (x : XDP) (k : ℕ) (hk : 1 ≤ k) :
    ∃ E : Set Ω, MeasurableSet[sourceCutFiltration x k] E ∧
      {p | 0 < selectedCutTime T k p} =ᵐ[μ] E := by
  let E : Set Ω := {p | ((sourceCutObservation x k p).1 0).2 < 0}
  refine ⟨E, ?_, ?_⟩
  · change MeasurableSet[MeasurableSpace.comap (sourceCutObservation x k)
      inferInstance] E
    refine ⟨{z : Ω × ℕ | (z.1 0).2 < 0}, ?_, rfl⟩
    have hc : Measurable (fun z : Ω × ℕ => (z.1 0).2) :=
      measurable_snd.comp ((measurable_pi_apply 0).comp measurable_fst)
    exact hc measurableSet_Iio
  · have hpos := selectedCutTime_positive_iff_future_negative_ae T k hk hT
    have hobs := sourceCutObservation_ae_eq x k hk
    filter_upwards [hpos, hobs] with p hp ho
    change (0 < selectedCutTime T k p) =
      (((sourceCutObservation x k p).1 0).2 < 0)
    apply propext
    rw [ho]
    exact Iff.of_eq hp

end DirectedDistances.PaperProofs.Section4
