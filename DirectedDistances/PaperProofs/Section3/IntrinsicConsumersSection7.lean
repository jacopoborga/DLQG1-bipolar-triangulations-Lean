/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumers14To18
public import DirectedDistances.PaperProofs.Section3.IntrinsicStageIdentification
public import DirectedDistances.PaperProofs.Section3.UIBOTLawStatementsSection7

/-! # Section 7 consumers on sampled intrinsic maps

104–111,227–238,287–292`. This module exposes the shared Section 7 cut,
the representative-wide intrinsic sequence identification, and the stopped
stage transport together with fluctuation bounds for the sampled intrinsic
sequences. The intrinsic geometric qualifier is not removed. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open MeasureTheory Filter DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7

local instance intrinsicConsumersSection7MeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance intrinsicConsumersSection7BorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

/-- Helper toward Proposition 3.9: the one shared-cut event for all four
Section 7 consumers, retaining the complete cut identification and all four
source conclusions under the UIBOT law. -/
abbrev intrinsicConsumersSection7_sharedCut := uibotLawSection7_sharedCut

/-- Helper toward Proposition 3.9: the complete Lemma 7.1 source statement
under the UIBOT law, alongside its intrinsic stopped-stage identification. -/
abbrev intrinsicConsumersSection7_longPath := uibotLawSection7_longPath

/-- Helper toward Proposition 3.9: the complete Lemma 7.3 source statement
under the UIBOT law, including its single uniform fluctuation constant. -/
abbrev intrinsicConsumersSection7_ldpFluctuationSource :=
  uibotLawSection7_ldpFluctuation

/-- Helper toward Proposition 3.9: the complete Lemma 7.5 source statement
under the UIBOT law, preserving its edge, root, missing-edge and distance
identifications. -/
abbrev intrinsicConsumersSection7_sdpTriSource := uibotLawSection7_sdpTri

/-- Helper toward Proposition 3.9: the complete Lemma 7.7 source statement
under the UIBOT law, preserving the threshold quantifier order. -/
abbrev intrinsicConsumersSection7_sdpFluctuationSource :=
  uibotLawSection7_sdpFluctuation

/-- Helper toward Proposition 3.9: on one iid conull event, every
representative has the unique intrinsic cut and both full sampled intrinsic
Busemann sequences satisfy their characterizations on that cut. -/
abbrev intrinsicConsumersSection7_intrinsicSequences :=
  intrinsicConsumers_cut_sequences_ae

/-- Helper toward Proposition 3.9: the unique intrinsic cut's boundary
labels are the images of the source boundary labels for every representative
and every produced isomorphism. -/
abbrev intrinsicConsumersSection7_intrinsicLabels :=
  uibotCut2_sample_unique_realization

/-- Helper toward Proposition 3.9: both entire sampled intrinsic sequences
equal the identified code sequences on one iid conull event. -/
abbrev intrinsicConsumersSection7_sampledSequenceIdentification :=
  sampledIntrinsicSequence_identification_ae

/-- Helper toward Proposition 3.9: the recovered code and both complete
geometric Busemann observables equal their iid code versions on one event. -/
abbrev intrinsicConsumersSection7_recoveryAndObservables :=
  uibotSection7b_transport_ae

/-- Helper toward Proposition 3.9: the law's single shared-cut event pulled
back to the iid sample through the proved measurable class map. -/
abbrev intrinsicConsumersSection7_sharedCutOnIid :=
  ae_of_ae_map
    (μ := wholePlaneIIDCodeMeasure)
    (measurable_uibotMeasurableWholePlaneClassMap
      uibotDeterministicComparison_proved).aemeasurable
    intrinsicConsumersSection7_sharedCut

/-- Helper toward Proposition 3.9: on one iid conull event, every
representative and every produced isomorphism receives the KMSW stopped
stages, first-hit times, and Lemma 7.1 stage paths. -/
abbrev intrinsicConsumersSection7_stoppedStages :=
  ae_intrinsicStage_identification

/-- Helper toward Proposition 3.9: one iid conull event supports the
shared Section 7 cut, every representative's intrinsic sequences, both
sampled-sequence identifications, and every transported stopped stage. -/
abbrev intrinsicConsumersSection7_jointIidEvent :=
  ((intrinsicConsumersSection7_sharedCutOnIid).and
    intrinsicConsumersSection7_intrinsicSequences).and
  ((intrinsicConsumersSection7_recoveryAndObservables.and
    intrinsicConsumersSection7_sampledSequenceIdentification).and
    (intrinsicConsumersSection7_intrinsicLabels.and
      intrinsicConsumersSection7_stoppedStages))

/-- Helper toward Proposition 3.9: Lemma 7.3's shared constant works for
the sampled intrinsic LDP sequence with the source quantifier order. -/
theorem intrinsicConsumersSection7_ldpFluctuation :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, 1 < A →
      1 - C * A ^ (-(2 / 3 : ℝ)) ≤
        wholePlaneIIDCodeMeasure.real {U | ∀ l : ℤ,
          -(k : ℤ) ≤ l → l ≤ k →
          |(sampledIntrinsicSequence true U l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)} := by
  obtain ⟨C, hC, htail⟩ := DirectedDistances.Paper.Section7.lem_ldp_fluctuation.2
  refine ⟨C, hC, ?_⟩
  intro k hk A hA
  have heq :
      wholePlaneIIDCodeMeasure.real {U | ∀ l : ℤ,
        -(k : ℤ) ≤ l → l ≤ k →
        |(sampledIntrinsicSequence true U l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)} =
      wholePlaneIIDCodeMeasure.real {U | ∀ l : ℤ,
        -(k : ℤ) ≤ l → l ≤ k →
        |(identifiedLDPBusemann U l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)} := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [sampledIntrinsicSequence_identification_ae] with U hU
    simp only [hU.2.2]
  rw [heq]
  exact htail k hk A hA

/-- Helper toward Proposition 3.9: one threshold per delta works uniformly
in every positive size for the sampled intrinsic SDP sequence, in the source
order `∀ δ > 0, ∃ A₀ > 1, ∀ k ≥ 1, ∀ A ≥ A₀`. -/
theorem intrinsicConsumersSection7_sdpFluctuation :
    ∀ delta : ℝ, 0 < delta → ∃ A0 : ℝ, 1 < A0 ∧
      ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, A0 ≤ A →
        1 - delta ≤ wholePlaneIIDCodeMeasure.real {U | ∀ l : ℤ,
          -(k : ℤ) ≤ l → l ≤ k →
          |(sampledIntrinsicSequence false U l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 4 : ℝ)} := by
  intro delta hdelta
  obtain ⟨A0, hA0, htail⟩ := DirectedDistances.Paper.Section7.lem_sdp_fluctuation.2
    delta hdelta
  refine ⟨A0, hA0, ?_⟩
  intro k hk A hA
  have heq :
      wholePlaneIIDCodeMeasure.real {U | ∀ l : ℤ,
        -(k : ℤ) ≤ l → l ≤ k →
        |(sampledIntrinsicSequence false U l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 4 : ℝ)} =
      wholePlaneIIDCodeMeasure.real {U | ∀ l : ℤ,
        -(k : ℤ) ≤ l → l ≤ k →
        |(identifiedSDPBusemann U l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 4 : ℝ)} := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [sampledIntrinsicSequence_identification_ae] with U hU
    simp only [hU.2.1]
  rw [heq]
  exact htail k hk A hA

end DirectedDistances.PaperProofs.Section3
end
