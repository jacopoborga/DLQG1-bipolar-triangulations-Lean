 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.BoltzmannLawDefinition

/-!
# Definition 3.14 (`def-boltzmann-lr`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/





public section
namespace DirectedDistances.Paper.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap MeasureTheory
open scoped ENNReal BigOperators ProbabilityTheory

 
theorem def_boltzmann_lr (ell r : ℕ)
    (hell : 1 ≤ ell) (hr : 1 ≤ r) :
    (boltzmannPartition ell r =
      ∑' m : BoltzmannSpace ell r, (1 / 3 : ℝ≥0∞) ^ m.1) ∧
    (0 < boltzmannPartition ell r ∧ boltzmannPartition ell r < ⊤) ∧
    IsProbabilityMeasure (boltzmannLaw ell r
      (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
      (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2) ∧
    (∀ m : BoltzmannSpace ell r,
      boltzmannLaw ell r
        (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
        (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2 {m} =
        (1 / 3 : ℝ≥0∞) ^ m.1 / boltzmannPartition ell r) ∧
    (rightBoltzmannLaw r
      (rightBoltzmannPartition_pos_lt_top r hr).1
      (rightBoltzmannPartition_pos_lt_top r hr).2)[|
        {q : AllBoltzmannSpace r | q.1 = ell}] =
      (boltzmannLaw ell r
        (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
        (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2).map
        (β := AllBoltzmannSpace r)
        (fun m => (⟨ell, m⟩ : AllBoltzmannSpace r)) ∧
    (∀ μ : Measure (BoltzmannSpace ell r),
      (∀ m, μ {m} = (1 / 3 : ℝ≥0∞) ^ m.1 / boltzmannPartition ell r) →
      μ = boltzmannLaw ell r
        (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
        (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.def_boltzmann_lr_provider ell r hell hr
 
 

end DirectedDistances.Paper.Section3
 
