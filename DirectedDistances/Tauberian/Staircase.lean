/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.AbelSine
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Finite cosine integrals of the Abel staircase

Infrastructure for `eq:int-repr` in `lem:abel`
The floor index is justified on each open mesh cell, so endpoint discontinuities
do not change an interval integral. These are bounded-interval identities and
convergence along mesh endpoints; arbitrary-cutoff improper convergence is a
separate obligation. -/

public section
namespace DirectedDistances.Tauberian

open Set Finset MeasureTheory Filter
open scoped Topology Interval

/-- The natural floor is constant on a positive mesh cell. All points considered
are nonnegative, so this is also the manuscript's integer floor. -/
theorem floor_div_eq_on_mesh_cell {t : ℝ} (ht : 0 < t) (k : ℕ) {u : ℝ}
    (hu : u ∈ Ioo ((k : ℝ) * t) (((k + 1 : ℕ) : ℝ) * t)) : ⌊u / t⌋₊ = k := by
  apply Nat.floor_eq_on_Ico k (u / t)
  constructor
  · exact (le_div_iff₀ ht).2 hu.1.le
  · apply (div_lt_iff₀ ht).2
    simpa only [Nat.cast_add, Nat.cast_one] using hu.2

/-- The staircase weight is constant inside a mesh cell. -/
theorem staircase_cos_eqOn_cell (S : ℕ → ℝ) {t : ℝ} (ht : 0 < t) (k : ℕ) :
    EqOn (fun u : ℝ => S (⌊u / t⌋₊ + 1) * Real.cos u)
      (fun u : ℝ => S (k + 1) * Real.cos u)
      (Ioo ((k : ℝ) * t) (((k + 1 : ℕ) : ℝ) * t)) := by
  intro u hu
  change S (⌊u / t⌋₊ + 1) * Real.cos u = S (k + 1) * Real.cos u
  rw [floor_div_eq_on_mesh_cell ht k hu]

/-- Each finite mesh cell has an integrable staircase-cosine product, with no
summability or monotonicity assumption on the sequence of cell weights. -/
theorem intervalIntegrable_staircase_cos_cell (S : ℕ → ℝ) {t : ℝ} (ht : 0 < t) (k : ℕ) :
    IntervalIntegrable (fun u : ℝ => S (⌊u / t⌋₊ + 1) * Real.cos u) volume
      ((k : ℝ) * t) (((k + 1 : ℕ) : ℝ) * t) := by
  have hle : (k : ℝ) * t ≤ ((k + 1 : ℕ) : ℝ) * t :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Nat.le_succ k)) ht.le
  have heq := staircase_cos_eqOn_cell S ht k
  rw [← uIoo_of_le hle] at heq
  apply (intervalIntegrable_congr_uIoo heq).2
  exact (continuous_const.mul Real.continuous_cos).intervalIntegrable _ _

/-- Integrating one cell gives the exact sine difference used by Appendix A.5. -/
theorem integral_staircase_cos_cell (S : ℕ → ℝ) {t : ℝ} (ht : 0 < t) (k : ℕ) :
    (∫ u in ((k : ℝ) * t)..(((k + 1 : ℕ) : ℝ) * t),
      S (⌊u / t⌋₊ + 1) * Real.cos u) =
      S (k + 1) * (Real.sin (((k + 1 : ℕ) : ℝ) * t) - Real.sin ((k : ℝ) * t)) := by
  have hle : (k : ℝ) * t ≤ ((k + 1 : ℕ) : ℝ) * t :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Nat.le_succ k)) ht.le
  rw [intervalIntegral.integral_congr_Ioo_of_le hle (staircase_cos_eqOn_cell S ht k),
    intervalIntegral.integral_const_mul, integral_cos]

/-- Finite-cell integrability assembles to every interval ending at a mesh point. -/
theorem intervalIntegrable_staircase_cos_mesh (S : ℕ → ℝ) {t : ℝ} (ht : 0 < t) (N : ℕ) :
    IntervalIntegrable (fun u : ℝ => S (⌊u / t⌋₊ + 1) * Real.cos u) volume 0 ((N : ℝ) * t) := by
  have h := IntervalIntegrable.trans_iterate (a := fun k : ℕ => (k : ℝ) * t)
    (n := N) (fun k _ => intervalIntegrable_staircase_cos_cell S ht k)
  simpa only [Nat.cast_zero, zero_mul] using h

/-- The integral up to a mesh point is the finite ordered Abel sum. -/
theorem integral_staircase_cos_mesh (S : ℕ → ℝ) {t : ℝ} (ht : 0 < t) (N : ℕ) :
    (∫ u in 0..((N : ℝ) * t), S (⌊u / t⌋₊ + 1) * Real.cos u) =
      ∑ k ∈ range N, S (k + 1) *
        (Real.sin (((k + 1 : ℕ) : ℝ) * t) - Real.sin ((k : ℝ) * t)) := by
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) * t) (n := N)
    (fun k _ => intervalIntegrable_staircase_cos_cell S ht k)
  rw [Nat.cast_zero, zero_mul] at h
  rw [← h]
  exact Finset.sum_congr rfl (fun k _ => integral_staircase_cos_cell S ht k)

/-- The staircase integral converges along mesh endpoints to the sine transform.
This is not yet an arbitrary-cutoff improper integral theorem. -/
theorem tendsto_integral_tail_cos_mesh (f : ℕ → ℝ) (hf : Summable f)
    (hn : ∀ k, 0 ≤ f k) {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun N : ℕ => ∫ u in 0..((N : ℝ) * t),
        (∑' j, f (j + (⌊u / t⌋₊ + 1))) * Real.cos u)
      atTop (𝓝 (∑' k, f k * Real.sin ((k : ℝ) * t))) := by
  simp_rw [integral_staircase_cos_mesh (fun k => ∑' j, f (j + k)) ht]
  exact tendsto_sum_tail_sin_sub f hf hn t

end DirectedDistances.Tauberian
