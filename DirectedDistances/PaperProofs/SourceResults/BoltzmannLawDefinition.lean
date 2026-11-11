/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section1.BoltzmannLawDefinition

/-! Supporting lemmas for paper labels `def-boltzmann-lr`, `def-boltzmann-right` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.PaperProofs.SourceResults

open DirectedDistances.KMSW DirectedDistances.PlanarMap MeasureTheory
open scoped ENNReal BigOperators ProbabilityTheory

 
theorem def_boltzmann_right_provider (r : ℕ) (hr : 1 ≤ r) :
    (rightBoltzmannPartition r =
      ∑' q : AllBoltzmannSpace r, (1 / 3 : ℝ≥0∞) ^ q.2.1) ∧
    (rightVertexMarkedPartition r =
      ∑' q : AllBoltzmannSpace r,
        ((q.1 + 1 : ℕ) : ℝ≥0∞) * (1 / 3 : ℝ≥0∞) ^ q.2.1) ∧
    (0 < rightBoltzmannPartition r ∧ rightBoltzmannPartition r < ⊤) ∧
    (0 < rightVertexMarkedPartition r ∧ rightVertexMarkedPartition r < ⊤) ∧
    IsProbabilityMeasure (rightBoltzmannLaw r
      (rightBoltzmannPartition_pos_lt_top r hr).1
      (rightBoltzmannPartition_pos_lt_top r hr).2) ∧
    IsProbabilityMeasure (rightVertexMarkedBoltzmannLaw r) ∧
    (∀ q : AllBoltzmannSpace r,
      rightBoltzmannLaw r
        (rightBoltzmannPartition_pos_lt_top r hr).1
        (rightBoltzmannPartition_pos_lt_top r hr).2 {q} =
        (1 / 3 : ℝ≥0∞) ^ q.2.1 / rightBoltzmannPartition r) ∧
    (∀ p : RightVertexMarkedBoltzmannSpace r,
      rightVertexMarkedBoltzmannLaw r {p} =
        (1 / 3 : ℝ≥0∞) ^ p.1.2.1 / rightVertexMarkedPartition r) ∧
    (∀ q : AllBoltzmannSpace r,
      (rightVertexMarkedBoltzmannLaw r).map
          (fun p : RightVertexMarkedBoltzmannSpace r => p.1) {q} =
        ((q.1 + 1 : ℕ) : ℝ≥0∞) * (1 / 3 : ℝ≥0∞) ^ q.2.1 /
          rightVertexMarkedPartition r) ∧
    (∀ μ : Measure (AllBoltzmannSpace r),
      (∀ q, μ {q} = (1 / 3 : ℝ≥0∞) ^ q.2.1 / rightBoltzmannPartition r) →
      μ = rightBoltzmannLaw r
        (rightBoltzmannPartition_pos_lt_top r hr).1
        (rightBoltzmannPartition_pos_lt_top r hr).2) ∧
    (∀ μ : Measure (RightVertexMarkedBoltzmannSpace r),
      (∀ p, μ {p} = (1 / 3 : ℝ≥0∞) ^ p.1.2.1 / rightVertexMarkedPartition r) →
      μ = rightVertexMarkedBoltzmannLaw r) := by
  exact DirectedDistances.PaperProofs.Section1.def_1_10_boltzmann_right_provider r hr

 
theorem def_boltzmann_lr_provider (ell r : ℕ)
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
        (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2) := by
  exact DirectedDistances.PaperProofs.Section1.def_3_14_boltzmann_lr_provider ell r hell hr

end DirectedDistances.PaperProofs.SourceResults
