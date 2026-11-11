/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Kernel.CondDistrib

/-! # Conditional laws from history-tested pushforwards

Generic finite-measure algebra for the conditional-law interpretation of
source application must produce the tested identities. No renewal time,
history, future, or source law is defined or characterized here. -/

public section

namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory

/-- Measurable history tests determine the whole joint measure. The measure
on the domain is finite but need not be normalized or have positive mass. -/
theorem map_pair_eq_prod_of_restrict_map_eq_smul
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) [IsFiniteMeasure μ]
    (ρ : Measure γ) [IsFiniteMeasure ρ]
    (H : α → β) (F : α → γ) (hH : Measurable H) (hF : Measurable F)
    (htest : ∀ A : Set β, MeasurableSet A →
      (μ.restrict (H ⁻¹' A)).map F = μ (H ⁻¹' A) • ρ) :
    μ.map (fun x => (H x, F x)) = (μ.map H).prod ρ := by
  apply Measure.ext_prod
  intro A B hA hB
  have hpiece := congrArg (fun η : Measure γ => η B) (htest A hA)
  rw [Measure.map_apply hF hB, Measure.restrict_apply (hB.preimage hF)] at hpiece
  rw [Measure.map_apply (hH.prodMk hF) (hA.prod hB),
    Measure.prod_prod, Measure.map_apply hH hA]
  have hpre : (fun x => (H x, F x)) ⁻¹' (A ×ˢ B) =
      (F ⁻¹' B) ∩ (H ⁻¹' A) := by
    ext x
    exact and_comm
  rw [hpre]
  exact hpiece

/-- History-tested pushforwards produce one simultaneous almost-everywhere
equality of conditional probability measures, including when `μ = 0`.
The tested law is an input to this generic helper, to be proved by each
source application rather than inserted into a paper theorem. -/
theorem condDistrib_ae_eq_const_of_restrict_map_eq_smul
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [StandardBorelSpace γ] [Nonempty γ]
    (μ : Measure α) [IsFiniteMeasure μ]
    (ρ : Measure γ) [IsProbabilityMeasure ρ]
    (H : α → β) (F : α → γ) (hH : Measurable H) (hF : Measurable F)
    (htest : ∀ A : Set β, MeasurableSet A →
      (μ.restrict (H ⁻¹' A)).map F = μ (H ⁻¹' A) • ρ) :
    condDistrib F H μ =ᵐ[μ.map H] Kernel.const β ρ := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hH hF
  rw [Measure.compProd_const]
  exact map_pair_eq_prod_of_restrict_map_eq_smul μ ρ H F hH hF htest

end DirectedDistances.Probability
