/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.PowerError
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Uniform scaled staircase error for Appendix A.6

Analytic infrastructure for revised `LeanVersion/tex/tauberian.tex`,
`lem:riemann`, the estimate after splitting at `u = t`.
The coefficient depends only on `ν` and works for every positive `t`. -/

public section
namespace DirectedDistances.Tauberian

open Set MeasureTheory Filter Asymptotics
open scoped Topology

/-- Positive dilation preserves absolute integrability of the staircase error. -/
theorem integrableOn_scaled_power_staircase_error {ν t : ℝ}
    (hν₀ : 0 < ν) (hν₁ : ν < 1) (ht : 0 < t) :
    IntegrableOn (fun u : ℝ => (((⌊u / t⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) -
      (u / t) ^ (-ν)) (Ioi 0) := by
  simpa only [← div_eq_mul_inv] using
    (integrableOn_Ioi_comp_mul_right_iff
      (fun x : ℝ => (((⌊x⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - x ^ (-ν)) 0
      (inv_pos.2 ht)).2 (by simpa only [zero_mul] using
        integrableOn_power_staircase_error hν₀ hν₁)

/-- The change of variables `u = t*x` gives the exact L¹ scaling identity. -/
theorem integral_norm_scaled_power_staircase_error (ν : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ u : ℝ in Ioi 0, ‖(((⌊u / t⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) -
      (u / t) ^ (-ν)‖) =
      t * ∫ x : ℝ in Ioi 0, ‖(((⌊x⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - x ^ (-ν)‖ := by
  simpa only [zero_mul, inv_inv, smul_eq_mul, ← div_eq_mul_inv, zero_div] using
    integral_comp_mul_right_Ioi
      (fun x : ℝ => ‖(((⌊x⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - x ^ (-ν)‖)
      0 (inv_pos.2 ht)

/-- One coefficient `1/(1-ν)+1` controls every positive scale. -/
theorem integral_norm_scaled_power_staircase_error_le {ν t : ℝ}
    (hν₀ : 0 < ν) (hν₁ : ν < 1) (ht : 0 < t) :
    (∫ u : ℝ in Ioi 0, ‖(((⌊u / t⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) -
      (u / t) ^ (-ν)‖) ≤ t * (1 / (1 - ν) + 1) := by
  rw [integral_norm_scaled_power_staircase_error ν ht]
  exact mul_le_mul_of_nonneg_left (integral_norm_power_staircase_error_le hν₀ hν₁) ht.le

/-- Multiplication by cosine preserves absolute integrability of the error. -/
theorem integrableOn_scaled_power_staircase_error_cos {ν t : ℝ}
    (hν₀ : 0 < ν) (hν₁ : ν < 1) (ht : 0 < t) :
    IntegrableOn (fun u : ℝ =>
      ((((⌊u / t⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - (u / t) ^ (-ν)) * Real.cos u)
      (Ioi 0) := by
  apply (integrableOn_scaled_power_staircase_error hν₀ hν₁ ht).mul_bdd
    Real.continuous_cos.aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one x)

/-- The oscillatory error has the same explicit bound as its L¹ majorant. -/
theorem norm_integral_scaled_power_staircase_error_cos_le {ν t : ℝ}
    (hν₀ : 0 < ν) (hν₁ : ν < 1) (ht : 0 < t) :
    ‖∫ u : ℝ in Ioi 0,
      ((((⌊u / t⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - (u / t) ^ (-ν)) * Real.cos u‖ ≤
      t * (1 / (1 - ν) + 1) := by
  apply (norm_integral_le_integral_norm _).trans
  apply le_trans _ (integral_norm_scaled_power_staircase_error_le hν₀ hν₁ ht)
  apply integral_mono_ae
    (integrableOn_scaled_power_staircase_error_cos hν₀ hν₁ ht).norm
    (integrableOn_scaled_power_staircase_error hν₀ hν₁ ht).norm
  exact ae_of_all _ (fun x => by
    dsimp only
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left
      (show ‖Real.cos x‖ ≤ 1 by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one x)
      (norm_nonneg _)).trans_eq (mul_one _))

/-- A linear error is of smaller order than `t^ν` at zero when `ν < 1`. -/
theorem id_isLittleO_rpow_nhdsGT_zero {ν : ℝ} (hν : ν < 1) :
    (fun t : ℝ => t) =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ ν) := by
  have hpos : 0 < 1 - ν := sub_pos.2 hν
  apply isLittleO_of_tendsto'
    (eventually_mem_nhdsWithin.mono (fun t ht hz =>
      False.elim ((Real.rpow_pos_of_pos ht ν).ne' hz)))
  have hh : Tendsto (fun t : ℝ => t ^ (1 - ν)) (𝓝[>] (0 : ℝ))
      (𝓝 ((0 : ℝ) ^ (1 - ν))) :=
    (Real.continuousAt_rpow_const 0 (1 - ν) (Or.inr hpos.le)).tendsto.mono_left
      nhdsWithin_le_nhds
  rw [Real.zero_rpow hpos.ne'] at hh
  apply hh.congr'
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  exact (Real.rpow_sub ht 1 ν).trans (by rw [Real.rpow_one])

/-- The absolutely integrable oscillatory error is `O(t)` with the same
single coefficient used in the source approximation. -/
theorem scaled_power_staircase_error_cos_isBigO {ν : ℝ}
    (hν₀ : 0 < ν) (hν₁ : ν < 1) :
    (fun t : ℝ => ∫ u : ℝ in Ioi 0,
      ((((⌊u / t⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - (u / t) ^ (-ν)) * Real.cos u)
      =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t) := by
  apply IsBigO.of_bound (1 / (1 - ν) + 1)
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  simpa only [Real.norm_eq_abs, abs_of_pos ht, mul_comm] using
    norm_integral_scaled_power_staircase_error_cos_le hν₀ hν₁ ht

/-- The error is `o(t^ν)`, without evaluating the oscillatory power integral. -/
theorem scaled_power_staircase_error_cos_isLittleO {ν : ℝ}
    (hν₀ : 0 < ν) (hν₁ : ν < 1) :
    (fun t : ℝ => ∫ u : ℝ in Ioi 0,
      ((((⌊u / t⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - (u / t) ^ (-ν)) * Real.cos u)
      =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ ν) :=
  (scaled_power_staircase_error_cos_isBigO hν₀ hν₁).trans_isLittleO
    (id_isLittleO_rpow_nhdsGT_zero hν₁)

end DirectedDistances.Tauberian
