/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeometricSideClass
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55NonnegPresentationIndependence
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55NonposPresentationIndependence
public import Mathlib.Probability.Independence.Basic

/-! This module transfers independence and laws across measurable presentations
and almost-everywhere equal geometric-side class maps. It records, but does
not assume or prove, the remaining source identifications. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory

/-- Helper toward Lemma 5.5: independence passes from independent measurable
presentations to almost-everywhere equal geometric-side class maps. -/
theorem indepFun_of_ae_eq_comp_geometricSideClass
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) {X : Ω → α} {Y : Ω → β}
    (F : α → GeometricSideClass) (G : β → GeometricSideClass)
    (hF : Measurable F) (hG : Measurable G) (hXY : IndepFun X Y μ)
    {A B : Ω → GeometricSideClass}
    (hA : A =ᵐ[μ] F ∘ X) (hB : B =ᵐ[μ] G ∘ Y) : IndepFun A B μ := by
  exact (hXY.comp hF hG).congr hA.symm hB.symm

/-- Helper toward Lemma 5.5: almost-everywhere equality to a measurable
presentation transfers its pushforward law. -/
theorem map_eq_map_comp_of_ae_eq
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) {X : Ω → α} (hX : AEMeasurable X μ)
    (F : α → β) (hF : Measurable F) {A : Ω → β}
    (hA : A =ᵐ[μ] F ∘ X) : μ.map A = (μ.map X).map F := by
  calc
    μ.map A = μ.map (F ∘ X) := Measure.map_congr hA
    _ = (μ.map X).map F := (hF.aemeasurable.map_map_of_aemeasurable hX).symm


























































end DirectedDistances.PaperProofs.Section5
