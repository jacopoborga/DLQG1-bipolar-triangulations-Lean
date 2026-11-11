/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.Staircase
import Mathlib.Analysis.Normed.Ring.Lemmas

/-! # Arbitrary-cutoff improper Abel integral

Deterministic analytic infrastructure for `eq:int-repr` of `lem:abel`
expressed as a limit of finite interval integrals. No absolute integrability on
the half-line is asserted. The source's nonnegative power-tail assumptions -/

public section
namespace DirectedDistances.Tauberian

open Set MeasureTheory Filter
open scoped Topology Interval

/-- The last partial mesh cell has a constant staircase weight on its interior. -/
theorem staircase_cos_eqOn_final_cell (S : ℕ → ℝ) {t : ℝ} (ht : 0 < t) (R : ℝ) :
    EqOn (fun u : ℝ => S (⌊u / t⌋₊ + 1) * Real.cos u)
      (fun u : ℝ => S (⌊R / t⌋₊ + 1) * Real.cos u)
      (Ioo ((⌊R / t⌋₊ : ℝ) * t) R) := by
  have hupper : R < (((⌊R / t⌋₊ + 1 : ℕ) : ℝ) * t) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (div_lt_iff₀ ht).1 (Nat.lt_floor_add_one (R / t))
  intro u hu
  exact staircase_cos_eqOn_cell S ht ⌊R / t⌋₊ ⟨hu.1, hu.2.trans hupper⟩

/-- The integrand is integrable on the last partial cell, including a cell of
length zero when the cutoff is a mesh point. -/
theorem intervalIntegrable_staircase_cos_final_cell (S : ℕ → ℝ) {t : ℝ}
    (ht : 0 < t) {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (fun u : ℝ => S (⌊u / t⌋₊ + 1) * Real.cos u) volume
      ((⌊R / t⌋₊ : ℝ) * t) R := by
  have hle : (⌊R / t⌋₊ : ℝ) * t ≤ R :=
    (le_div_iff₀ ht).1 (Nat.floor_le (div_nonneg hR ht.le))
  have heq := staircase_cos_eqOn_final_cell S ht R
  rw [← uIoo_of_le hle] at heq
  apply (intervalIntegrable_congr_uIoo heq).2
  exact (continuous_const.mul Real.continuous_cos).intervalIntegrable _ _

/-- The exact integral of the final partial cell is a bounded sine increment
times its tail weight. -/
theorem integral_staircase_cos_final_cell (S : ℕ → ℝ) {t : ℝ}
    (ht : 0 < t) {R : ℝ} (hR : 0 ≤ R) :
    (∫ u in ((⌊R / t⌋₊ : ℝ) * t)..R, S (⌊u / t⌋₊ + 1) * Real.cos u) =
      S (⌊R / t⌋₊ + 1) * (Real.sin R - Real.sin ((⌊R / t⌋₊ : ℝ) * t)) := by
  have hle : (⌊R / t⌋₊ : ℝ) * t ≤ R :=
    (le_div_iff₀ ht).1 (Nat.floor_le (div_nonneg hR ht.le))
  rw [intervalIntegral.integral_congr_Ioo_of_le hle (staircase_cos_eqOn_final_cell S ht R),
    intervalIntegral.integral_const_mul, integral_cos]

/-- The staircase-cosine product is integrable up to every finite nonnegative
cutoff. This does not assert integrability over the infinite half-line. -/
theorem intervalIntegrable_staircase_cos (S : ℕ → ℝ) {t : ℝ}
    (ht : 0 < t) {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (fun u : ℝ => S (⌊u / t⌋₊ + 1) * Real.cos u) volume 0 R :=
  (intervalIntegrable_staircase_cos_mesh S ht ⌊R / t⌋₊).trans
    (intervalIntegrable_staircase_cos_final_cell S ht hR)

/-- An arbitrary nonnegative cutoff splits into complete cells and one exact
partial cell. -/
theorem integral_staircase_cos_partial (S : ℕ → ℝ) {t : ℝ}
    (ht : 0 < t) {R : ℝ} (hR : 0 ≤ R) :
    (∫ u in 0..R, S (⌊u / t⌋₊ + 1) * Real.cos u) =
      (∫ u in 0..((⌊R / t⌋₊ : ℝ) * t), S (⌊u / t⌋₊ + 1) * Real.cos u) +
        S (⌊R / t⌋₊ + 1) * (Real.sin R - Real.sin ((⌊R / t⌋₊ : ℝ) * t)) := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_staircase_cos_mesh S ht ⌊R / t⌋₊)
    (intervalIntegrable_staircase_cos_final_cell S ht hR)
  rw [integral_staircase_cos_final_cell S ht hR] at h
  exact h.symm

/-- The index of the last mesh cell tends to infinity with the real cutoff. -/
theorem tendsto_floor_div_atTop {t : ℝ} (ht : 0 < t) :
    Tendsto (fun R : ℝ => ⌊R / t⌋₊) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop ((n : ℝ) * t)] with R hR
  exact Nat.le_floor ((le_div_iff₀ ht).2 hR)

/-- The improper staircase integral, with arbitrary real cutoffs, equals the
sine transform of a summable nonnegative sequence. The proof uses bounded
oscillatory remainders; it never replaces this limit by a half-line Bochner integral. -/
theorem tendsto_integral_tail_cos (f : ℕ → ℝ) (hf : Summable f)
    (hn : ∀ k, 0 ≤ f k) {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun R : ℝ => ∫ u in 0..R, (∑' j, f (j + (⌊u / t⌋₊ + 1))) * Real.cos u)
      atTop (𝓝 (∑' k, f k * Real.sin ((k : ℝ) * t))) := by
  have hfloor := tendsto_floor_div_atTop ht
  have hmesh := tendsto_integral_tail_cos_mesh f hf hn ht
  have htail : Tendsto (fun R : ℝ => ∑' j, f (j + (⌊R / t⌋₊ + 1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_sum_nat_add f).comp ((tendsto_add_atTop_nat 1).comp hfloor)
  have hbound : IsBoundedUnder (· ≤ ·) atTop
      (fun R : ℝ => ‖Real.sin R - Real.sin ((⌊R / t⌋₊ : ℝ) * t)‖) := by
    apply isBoundedUnder_of
    refine ⟨1 + 1, fun R => ?_⟩
    apply (norm_sub_le _ _).trans
    exact add_le_add (by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one R)
      (by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one ((⌊R / t⌋₊ : ℝ) * t))
  have hrem := htail.zero_mul_isBoundedUnder_le hbound
  have htotal : Tendsto
      (fun R : ℝ =>
        (∫ u in 0..((⌊R / t⌋₊ : ℝ) * t), (∑' j, f (j + (⌊u / t⌋₊ + 1))) * Real.cos u) +
          (∑' j, f (j + (⌊R / t⌋₊ + 1))) *
            (Real.sin R - Real.sin ((⌊R / t⌋₊ : ℝ) * t)))
      atTop (𝓝 (∑' k, f k * Real.sin ((k : ℝ) * t))) := by
    simpa only [add_zero, Function.comp_apply] using (hmesh.comp hfloor).add hrem
  apply htotal.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  exact (integral_staircase_cos_partial (fun k => ∑' j, f (j + k)) ht hR).symm

end DirectedDistances.Tauberian
