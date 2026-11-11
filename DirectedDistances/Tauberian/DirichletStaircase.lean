/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.DirichletTail
public import DirectedDistances.Tauberian.ImproperAbel

/-! # Oscillatory tails of a decreasing staircase

Dependencies of revised Appendix A.4 (`lem:bound-im-part`). The improper value
in the final helper is supplied by an actual convergence theorem, and its tail
bound is derived here from finite summation by parts. No infinite absolute
remainder estimate is asserted. -/

public section
namespace DirectedDistances.Tauberian

open Set Finset MeasureTheory Filter
open scoped Topology Interval

/-- Uniform cancellation of every finite block of sine increments against a
decreasing nonnegative sequence, with coefficient independent of the scale. -/
theorem norm_sum_shifted_antitone_sin_sub_le (S : ℕ → ℝ)
    (hS : Antitone S) (hn : ∀ k, 0 ≤ S k) (t : ℝ) (K N : ℕ) :
    ‖∑ k ∈ range N, S (k + K + 1) *
      (Real.sin (((k + K + 1 : ℕ) : ℝ) * t) -
        Real.sin (((k + K : ℕ) : ℝ) * t))‖ ≤ 2 * S (K + 1) := by
  have hh := norm_sum_antitone_mul_sub_current_le
    (fun k => S (k + K + 1)) (fun k => Real.sin (((k + K : ℕ) : ℝ) * t))
    (fun a b hab => hS (Nat.add_le_add_right (Nat.add_le_add_right hab K) 1))
    (fun k => hn (k + K + 1))
    (B := 1) (by
      intro k
      simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (((k + K : ℕ) : ℝ) * t)) N
  simpa only [Nat.zero_add, Nat.add_zero, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm, mul_one] using hh

/-- A mesh interval inherits the finite Dirichlet bound. -/
theorem norm_integral_staircase_cos_mesh_sub_le (S : ℕ → ℝ)
    (hS : Antitone S) (hn : ∀ k, 0 ≤ S k) {t : ℝ} (ht : 0 < t) (K N : ℕ) :
    ‖(∫ u : ℝ in 0..(((N + K : ℕ) : ℝ) * t),
        S (⌊u / t⌋₊ + 1) * Real.cos u) -
      ∫ u : ℝ in 0..((K : ℝ) * t), S (⌊u / t⌋₊ + 1) * Real.cos u‖ ≤
        2 * S (K + 1) := by
  rw [integral_staircase_cos_mesh S ht, integral_staircase_cos_mesh S ht,
    Nat.add_comm N K, sum_range_add, add_sub_cancel_left]
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    norm_sum_shifted_antitone_sin_sub_le S hS hn t K N

/-- The tail of a genuine improper staircase integral obeys the same sharp
bound. The convergence input is supplied by its consumer's proved existence
theorem; this ordinary helper is not itself a numbered paper result. -/
theorem norm_improper_staircase_cos_sub_mesh_le (S : ℕ → ℝ)
    (hS : Antitone S) (hn : ∀ k, 0 ≤ S k) {t L : ℝ} (ht : 0 < t)
    (hL : Tendsto (fun R : ℝ => ∫ u : ℝ in 0..R,
      S (⌊u / t⌋₊ + 1) * Real.cos u) atTop (𝓝 L)) (K : ℕ) :
    ‖L - ∫ u : ℝ in 0..((K : ℝ) * t), S (⌊u / t⌋₊ + 1) * Real.cos u‖ ≤
      2 * S (K + 1) := by
  have hR : Tendsto (fun N : ℕ => ((N + K : ℕ) : ℝ) * t) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat K)).atTop_mul_const ht
  apply le_of_tendsto ((hL.comp hR).sub_const
    (∫ u : ℝ in 0..((K : ℝ) * t), S (⌊u / t⌋₊ + 1) * Real.cos u)).norm
  exact Eventually.of_forall (norm_integral_staircase_cos_mesh_sub_le S hS hn ht K)

/-- An arbitrary nonnegative cutoff differs from its preceding mesh point by
one bounded sine increment. Together with the mesh tail estimate this gives
a bound uniform in the cutoff and in the positive scale. -/
theorem norm_improper_staircase_cos_sub_cutoff_le (S : ℕ → ℝ)
    (hS : Antitone S) (hn : ∀ k, 0 ≤ S k) {t L A : ℝ} (ht : 0 < t) (hA : 0 ≤ A)
    (hL : Tendsto (fun R : ℝ => ∫ u : ℝ in 0..R,
      S (⌊u / t⌋₊ + 1) * Real.cos u) atTop (𝓝 L)) :
    ‖L - ∫ u : ℝ in 0..A, S (⌊u / t⌋₊ + 1) * Real.cos u‖ ≤
      4 * S (⌊A / t⌋₊ + 1) := by
  have hmesh := norm_improper_staircase_cos_sub_mesh_le S hS hn ht hL ⌊A / t⌋₊
  have hs : ‖Real.sin A - Real.sin ((⌊A / t⌋₊ : ℝ) * t)‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by
      have h1 : ‖Real.sin A‖ ≤ 1 := by
        simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one A
      have h2 : ‖Real.sin ((⌊A / t⌋₊ : ℝ) * t)‖ ≤ 1 := by
        simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one ((⌊A / t⌋₊ : ℝ) * t)
      linarith only [h1, h2])
  rw [integral_staircase_cos_partial S ht hA, ← sub_sub]
  calc
    _ ≤ ‖L - ∫ u : ℝ in 0..((⌊A / t⌋₊ : ℝ) * t),
        S (⌊u / t⌋₊ + 1) * Real.cos u‖ +
        ‖S (⌊A / t⌋₊ + 1) * (Real.sin A - Real.sin ((⌊A / t⌋₊ : ℝ) * t))‖ :=
      norm_sub_le _ _
    _ ≤ 2 * S (⌊A / t⌋₊ + 1) + 2 * S (⌊A / t⌋₊ + 1) := by
      apply add_le_add hmesh
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hn _)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hs (hn (⌊A / t⌋₊ + 1))
    _ = 4 * S (⌊A / t⌋₊ + 1) := by ring

end DirectedDistances.Tauberian
