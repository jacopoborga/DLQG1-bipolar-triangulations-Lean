/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ConditionedVectorFactorization
import Mathlib.Tactic.Positivity








public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Every full source word has positive conditioned atom mass exactly on the
whole nonnegative-prefix event, including the horizon-zero empty word. -/
theorem conditionedTwoDimensionalPrefix_atom_pos_iff (n x : ℕ) (y : ℤ)
    (w : Fin n → Fin 3) :
    0 < (((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
      (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
        (fun q => if ∀ j, 0 ≤ (q j).1 then
          ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0))
      {lazyTwoDimensionalPrefix (x : ℤ) y w} ↔
      ∀ j, 0 ≤ (lazyTwoDimensionalPrefix (x : ℤ) y w j).1 := by
  classical
  rw [conditionedTwoDimensionalPrefix_atom]
  by_cases h : ∀ j, 0 ≤ (lazyTwoDimensionalPrefix (x : ℤ) y w j).1
  · simp only [h, forall_const, ↓reduceIte, iff_true]
    have hend : 0 ≤ ((lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1 : ℝ) :=
      Int.cast_nonneg (h (Fin.last n))
    have hnum : 0 < ((lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1 : ℝ) + 1 :=
      add_pos_of_nonneg_of_pos hend zero_lt_one
    have hden : 0 < (x : ℝ) + 1 := by positivity
    have hweight : 0 < ENNReal.ofReal
        ((((lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1 : ℝ) + 1) /
          ((x : ℝ) + 1)) := ENNReal.ofReal_pos.mpr (div_pos hnum hden)
    have hword : 0 < ((3 : ℝ≥0∞) ^ n)⁻¹ :=
      bot_lt_iff_ne_bot.mpr (ENNReal.inv_ne_zero.mpr (by finiteness))
    exact ENNReal.mul_pos hweight.ne' hword.ne'
  · simp only [h, ↓reduceIte, zero_mul, lt_self_iff_false]

/-- The literal all-horizon RN definition gives the same positive-support
characterization for actual full-process cylinders. -/
theorem conditionedSource_prefix_atom_pos_iff
    (x : ℕ) (y : ℤ) (ν : Measure (ℕ → ℤ × ℤ))
    (hRN : ∀ n : ℕ,
      ν.map (fun q => fun j : Fin (n + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0))
    (n : ℕ) (w : Fin n → Fin 3) :
    0 < ν {p | (fun j : Fin (n + 1) => p j.val) =
      lazyTwoDimensionalPrefix (x : ℤ) y w} ↔
      ∀ j, 0 ≤ (lazyTwoDimensionalPrefix (x : ℤ) y w j).1 := by
  have h := congrArg
    (fun μ : Measure (Fin (n + 1) → ℤ × ℤ) =>
      μ {lazyTwoDimensionalPrefix (x : ℤ) y w}) (hRN n)
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at h
  change ν {p | (fun j : Fin (n + 1) => p j.val) =
    lazyTwoDimensionalPrefix (x : ℤ) y w} = _ at h
  rw [h]
  exact conditionedTwoDimensionalPrefix_atom_pos_iff n x y w

end DirectedDistances.RandomWalk
