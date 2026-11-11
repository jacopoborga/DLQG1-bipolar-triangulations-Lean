/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ConditionedVectorTrajectory








public section
namespace DirectedDistances.PaperProofs.Section4

open MeasureTheory DirectedDistances.RandomWalk
open scoped ENNReal




theorem cond_walk_rn_law (x : ℕ) (y : ℤ) :
    IsProbabilityMeasure (conditionedVectorPathLaw x y) ∧
      (∀ n : ℕ, (conditionedVectorPathLaw x y).map
          (fun q => fun j : Fin (n + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0)) ∧
      ∀ μ : Measure (ℕ → ℤ × ℤ), IsProbabilityMeasure μ →
        (∀ n : ℕ, μ.map (fun q => fun j : Fin (n + 1) => q j.val) =
          ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
            (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
            (fun q => if ∀ j, 0 ≤ (q j).1 then
              ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0)) →
        μ = conditionedVectorPathLaw x y := by
  refine ⟨inferInstance, conditionedVectorPathLaw_map_prefix x y, ?_⟩
  intro μ hμ hRN
  exact conditioned_vector_law_unique x y μ (conditionedVectorPathLaw x y) hRN
    (conditionedVectorPathLaw_map_prefix x y)

end DirectedDistances.PaperProofs.Section4
