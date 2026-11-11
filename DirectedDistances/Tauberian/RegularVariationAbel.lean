/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.RegularVariationStaircase
public import DirectedDistances.Tauberian.DirichletStaircase
public import DirectedDistances.Tauberian.UniformCutoff
public import DirectedDistances.Tauberian.MellinCos

/-! # Abelian scaling with actual monotone tails

Analytic closure for revised Appendix A.4 (`lem:bound-im-part`). Compact
dominated convergence and a uniform Dirichlet bound control different parts
of the integral. This avoids integrating a bare little-o remainder absolutely
on the half-line. This ordinary analytic provider takes an actual improper
limit, which the paper-facing consumer must produce rather than assume. -/

public section
namespace DirectedDistances.Tauberian

open Set MeasureTheory Filter
open scoped Topology Interval

/-- A regularly varying decreasing nonnegative staircase has the stated
power-normalized oscillatory limit. The only integral input is its actual
arbitrary-cutoff convergence, supplied independently by the Abel identity. -/
theorem tendsto_scaled_improper_staircase_cos (S : ℕ → ℝ) (F : ℝ → ℝ)
    (hS : Antitone S) (hn : ∀ k, 0 ≤ S k) {c ν : ℝ}
    (hν₀ : 0 < ν) (hν₁ : ν < 1)
    (hlim : Tendsto (fun n : ℕ => S n / (n : ℝ) ^ (-ν)) atTop (𝓝 c))
    (hF : ∀ t : ℝ, 0 < t → Tendsto (fun R : ℝ => ∫ u : ℝ in 0..R,
      S (⌊u / t⌋₊ + 1) * Real.cos u) atTop (𝓝 (F t))) :
    Tendsto (fun t : ℝ => t ^ (-ν) * F t) (𝓝[>] 0)
      (𝓝 (c * (Real.Gamma (1 - ν) * Real.sin (Real.pi * ν / 2)))) := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_power_normalized_sequence S hlim
  apply tendsto_of_uniform_rpow_cutoff_bound hν₀
    (G := fun A t => ∫ u : ℝ in 0..A,
      (t ^ (-ν) * S (⌊u / t⌋₊ + 1)) * Real.cos u)
    (H := fun A => ∫ u : ℝ in 0..A, u ^ (-ν) * Real.cos u)
    (tendsto_integral_power_cos_gamma hν₀ hν₁)
  · intro A hA
    have hh := tendsto_integral_scaled_staircase_cos_cutoff S hν₀.le hν₁ hA.le hlim
    simpa only [mul_assoc, intervalIntegral.integral_const_mul] using hh
  · refine ⟨4 * C, mul_pos (by norm_num) hC, ?_⟩
    intro t ht A hA
    have heq : (∫ u : ℝ in 0..A, (t ^ (-ν) * S (⌊u / t⌋₊ + 1)) * Real.cos u) =
        t ^ (-ν) * ∫ u : ℝ in 0..A, S (⌊u / t⌋₊ + 1) * Real.cos u := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u _hu
      ring
    have hp := Real.rpow_pos_of_pos ht (-ν)
    have htail := norm_improper_staircase_cos_sub_cutoff_le S hS hn ht hA.le (hF t ht)
    calc
      _ = t ^ (-ν) * ‖F t - ∫ u : ℝ in 0..A,
          S (⌊u / t⌋₊ + 1) * Real.cos u‖ := by
        rw [heq, ← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_pos hp]
      _ ≤ t ^ (-ν) * (4 * S (⌊A / t⌋₊ + 1)) :=
        mul_le_mul_of_nonneg_left htail hp.le
      _ = 4 * ‖t ^ (-ν) * S (⌊A / t⌋₊ + 1)‖ := by
        rw [norm_mul]
        simp only [Real.norm_eq_abs, abs_of_pos hp, abs_of_nonneg (hn _)]
        ring
      _ ≤ 4 * (C * A ^ (-ν)) := mul_le_mul_of_nonneg_left
        (norm_scaled_staircase_le S hν₀.le hC.le hbound ht hA) (by norm_num)
      _ = (4 * C) * A ^ (-ν) := by ring

end DirectedDistances.Tauberian
