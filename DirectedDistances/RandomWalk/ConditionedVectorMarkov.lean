/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ConditionedVectorFactorization
public import DirectedDistances.RandomWalk.LazyVectorConcatenation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Supporting lemmas for paper labels `lem-renewal` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Full two-dimensional finite source RN atoms factor at a deterministic
word boundary. `hX` merely represents the actual endpoint by a natural state;
illegal earlier prefixes still have probability zero on both sides. -/
theorem conditionedTwoDimensionalPrefix_atom_append
    (n m x X : ℕ) (y : ℤ) (w : Fin n → Fin 3) (v : Fin m → Fin 3)
    (hX : (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1 = (X : ℤ)) :
    (((Measure.uniformOfFinset (Finset.univ : Finset (Fin (n + m) → Fin 3))).map
      (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
        (fun q => if ∀ j, 0 ≤ (q j).1 then
          ENNReal.ofReal ((((q (Fin.last (n + m))).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0))
      {lazyTwoDimensionalPrefix (x : ℤ) y (Fin.append w v)} =
      ((((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
        (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0))
        {lazyTwoDimensionalPrefix (x : ℤ) y w}) *
      ((((Measure.uniformOfFinset (Finset.univ : Finset (Fin m → Fin 3))).map
        (lazyTwoDimensionalPrefix (X : ℤ)
          (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).2)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last m)).1 : ℝ) + 1) / ((X : ℝ) + 1)) else 0))
        {lazyTwoDimensionalPrefix (X : ℤ)
          (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).2 v}) := by
  classical
  rw [conditionedTwoDimensionalPrefix_atom,
    conditionedTwoDimensionalPrefix_atom,
    conditionedTwoDimensionalPrefix_atom]
  have hbar := lazyTwoDimensionalPrefix_append_nonnegative_iff (x : ℤ) y w v
  rw [hX] at hbar
  have hend := lazyTwoDimensionalPrefix_append_right (x : ℤ) y w v (Fin.last m)
  rw [hX] at hend
  have hlast :
      (⟨n + (Fin.last m).val, by omega⟩ : Fin (n + m + 1)) =
        Fin.last (n + m) := by
    apply Fin.ext
    rfl
  rw [hlast] at hend
  simp only [hbar, hend, hX]
  by_cases hw : ∀ j, 0 ≤ (lazyTwoDimensionalPrefix (x : ℤ) y w j).1
  · by_cases hv : ∀ j, 0 ≤ (lazyTwoDimensionalPrefix (X : ℤ)
        (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).2 v j).1
    · simp only [hw, hv, forall_const, true_and, ↓reduceIte, Int.cast_natCast]
      have htel (z : ℝ) :
          (((X : ℝ) + 1) / ((x : ℝ) + 1)) * (z / ((X : ℝ) + 1)) =
            z / ((x : ℝ) + 1) := by
        have hden : (X : ℝ) + 1 ≠ 0 := by positivity
        field_simp
      have hprod (z : ℝ) :
          ENNReal.ofReal (((X : ℝ) + 1) / ((x : ℝ) + 1)) *
              ENNReal.ofReal (z / ((X : ℝ) + 1)) =
            ENNReal.ofReal (z / ((x : ℝ) + 1)) := by
        rw [← ENNReal.ofReal_mul (by positivity), htel]
      have hpow : ((3 : ℝ≥0∞) ^ (n + m))⁻¹ =
          ((3 : ℝ≥0∞) ^ n)⁻¹ * ((3 : ℝ≥0∞) ^ m)⁻¹ := by
        rw [pow_add]
        exact ENNReal.mul_inv (Or.inl (pow_ne_zero n (by norm_num)))
          (Or.inr (pow_ne_zero m (by norm_num)))
      rw [hpow]
      calc
        _ = (ENNReal.ofReal (((X : ℝ) + 1) / ((x : ℝ) + 1)) *
              ENNReal.ofReal
                ((((lazyTwoDimensionalPrefix (X : ℤ)
                  (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).2 v
                    (Fin.last m)).1 : ℝ) + 1) / ((X : ℝ) + 1))) *
            (((3 : ℝ≥0∞) ^ n)⁻¹ * ((3 : ℝ≥0∞) ^ m)⁻¹) := by rw [hprod]
        _ = _ := by ring
    · simp only [hw, hv, and_false, ↓reduceIte, zero_mul, mul_zero]
  · simp only [hw, false_and, ↓reduceIte, zero_mul]

end DirectedDistances.RandomWalk
