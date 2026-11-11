 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.BoltzmannLawDefinition

/-!
# Definition 1.10 (`def-boltzmann-right`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/






public section
namespace DirectedDistances.Paper.Section1

open DirectedDistances.KMSW DirectedDistances.PlanarMap MeasureTheory
open scoped ENNReal BigOperators ProbabilityTheory

 
theorem def_boltzmann_right (r : ℕ) (hr : 1 ≤ r) :
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
      μ = rightVertexMarkedBoltzmannLaw r) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.def_boltzmann_right_provider r hr
 
 

end DirectedDistances.Paper.Section1
 
