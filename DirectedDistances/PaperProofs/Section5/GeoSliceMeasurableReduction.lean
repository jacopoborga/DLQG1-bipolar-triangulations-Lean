/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceLemma56Assembly
public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusMeasurableDescent

/-! Helper toward Lemma 5.6. Almost-everywhere factorization through a standard
Borel observation, and the remaining measurable-reconstruction boundary. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory

/-- Helper toward Lemma 5.6. An almost-everywhere measurable function that
is almost everywhere a function of a standard Borel observation admits a
measurable factor through that observation. -/
theorem exists_measurable_ae_factorization
    {Ω Z β : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace Z] [StandardBorelSpace Z] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Y : Ω → Z} {G : Ω → β} {g : Z → β}
    (hY : AEMeasurable Y μ) (hG : AEMeasurable G μ)
    (hfactor : G =ᵐ[μ] g ∘ Y) :
    ∃ F : Z → β, Measurable F ∧ G =ᵐ[μ] F ∘ Y := by
  have hcomp : AEMeasurable (g ∘ Y) μ := hG.congr hfactor
  have hdesc := aemeasurable_map_of_aemeasurable_comp μ hY hcomp
  refine ⟨hdesc.mk g, hdesc.measurable_mk, ?_⟩
  have hgf : (g ∘ Y) =ᵐ[μ] (hdesc.mk g ∘ Y) :=
    ae_eq_comp hY hdesc.ae_eq_mk
  exact hfactor.trans hgf

/-- Helper toward Lemma 5.6. The same factorization applies when the
almost-everywhere determining function is supplied only by existence. -/
theorem exists_measurable_ae_factorization_of_exists
    {Ω Z β : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace Z] [StandardBorelSpace Z] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Y : Ω → Z} {G : Ω → β}
    (hY : AEMeasurable Y μ) (hG : AEMeasurable G μ)
    (hfactor : ∃ g : Z → β, G =ᵐ[μ] g ∘ Y) :
    ∃ F : Z → β, Measurable F ∧ G =ᵐ[μ] F ∘ Y := by
  obtain ⟨g, hg⟩ := hfactor
  exact exists_measurable_ae_factorization μ hY hG hg










































end DirectedDistances.PaperProofs.Section5
