/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.ConditionalProbability

/-! # Conditioning and measurable pushforward

Generic measure identities used in the deterministic-time full-vector
regeneration step of Lemma 4.9 (`lem-renewal`), original
source law or assert regeneration. Actual probability interpretations require
positive conditioning masses, supplied separately by the relevant producers. -/

public section
namespace DirectedDistances.Probability
open MeasureTheory ProbabilityTheory

/-- Conditioning a measurable pushforward on an event is the pushforward
of the original measure conditioned on the event's preimage. No finiteness
or positive-mass assumption is needed for this algebraic measure identity. -/
theorem cond_map_eq_map_cond_preimage
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) (hf : Measurable f)
    (B : Set β) (hB : MeasurableSet B) :
    cond (μ.map f) B = (cond μ (f ⁻¹' B)).map f := by
  unfold ProbabilityTheory.cond
  rw [Measure.map_apply hf hB, Measure.restrict_map hf hB,
    Measure.map_smul _ hf.aemeasurable]

/-- Condition on a past event, map to a future, condition that future, and
then map again: this is conditioning on the actual pulled-back joint event
and taking the composed measurable map. The equality does not assume any
conditional-law identification or positivity conclusion. -/
theorem cond_map_cond_eq_map_cond_inter
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) [IsFiniteMeasure μ]
    (C : Set α) (hC : MeasurableSet C)
    (f : α → β) (hf : Measurable f) (B : Set β) (hB : MeasurableSet B)
    (g : β → γ) (hg : Measurable g) :
    (cond ((cond μ C).map f) B).map g =
      (cond μ (C ∩ f ⁻¹' B)).map (g ∘ f) := by
  rw [cond_map_eq_map_cond_preimage (cond μ C) f hf B hB,
    cond_cond_eq_cond_inter hC (hB.preimage hf) μ,
    Measure.map_map hg hf]

end DirectedDistances.Probability
