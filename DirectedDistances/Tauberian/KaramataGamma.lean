/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.ComplexLaplace

/-! # Actual Gamma-weighted moments for the Laplace Tauberian construction

Producer dependencies of the external Tauberian step used in revised Appendix
A.2/A.3. These are actual integrability and normalization theorems for positive
shape; no Gamma law is constructed before its mass is proved to be one. -/

public section
namespace DirectedDistances.Tauberian

open Set MeasureTheory

/-- Combining the damping factors gives the actual weighted Gamma integrand. -/
theorem gamma_weighted_integrand_eq (τ k x : ℝ) :
    Real.exp (-k * x) * x ^ (τ - 1) * Real.exp (-x) / Real.Gamma τ =
      (x ^ (τ - 1) * Real.exp (-((k + 1) * x))) / Real.Gamma τ := by
  have he : Real.exp (-k * x) * Real.exp (-x) = Real.exp (-((k + 1) * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = x ^ (τ - 1) * (Real.exp (-k * x) * Real.exp (-x)) / Real.Gamma τ := by ring
    _ = _ := by rw [he]

/-- Every nonnegative real Laplace moment of the Gamma density is integrable. -/
theorem integrableOn_gamma_weighted_moment {τ k : ℝ} (hτ : 0 < τ) (hk : 0 ≤ k) :
    IntegrableOn (fun x : ℝ =>
      Real.exp (-k * x) * x ^ (τ - 1) * Real.exp (-x) / Real.Gamma τ) (Ioi 0) := by
  simp_rw [gamma_weighted_integrand_eq]
  exact (integrableOn_rpow_mul_exp_neg (a := τ - 1) (by linarith only [hτ])
    (by linarith only [hk] : 0 < k + 1)).div_const (Real.Gamma τ)

/-- Actual Gamma-weighted Laplace moments, with their normalization explicit. -/
theorem integral_gamma_weighted_moment {τ k : ℝ} (hτ : 0 < τ) (hk : 0 ≤ k) :
    (∫ x : ℝ in Ioi 0,
      Real.exp (-k * x) * x ^ (τ - 1) * Real.exp (-x) / Real.Gamma τ) =
        (k + 1) ^ (-τ) := by
  have hr : 0 < k + 1 := by linarith only [hk]
  have hΓ : Real.Gamma τ ≠ 0 := (Real.Gamma_pos_of_pos hτ).ne'
  simp_rw [gamma_weighted_integrand_eq]
  rw [integral_div, Real.integral_rpow_mul_exp_neg_mul_Ioi hτ hr,
    mul_div_cancel_right₀ _ hΓ, one_div, Real.inv_rpow hr.le, Real.rpow_neg hr.le]

/-- The undamped Gamma density has genuine integrability and mass one. -/
theorem gamma_density_integrable_mass_one {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun x : ℝ => x ^ (τ - 1) * Real.exp (-x) / Real.Gamma τ) (Ioi 0) ∧
      (∫ x : ℝ in Ioi 0, x ^ (τ - 1) * Real.exp (-x) / Real.Gamma τ) = 1 := by
  constructor
  · simpa only [neg_zero, zero_mul, Real.exp_zero, one_mul] using
      integrableOn_gamma_weighted_moment hτ (le_refl (0 : ℝ))
  · simpa only [neg_zero, zero_mul, Real.exp_zero, one_mul, zero_add, Real.one_rpow] using
      integral_gamma_weighted_moment hτ (le_refl (0 : ℝ))

/-- The density is nonnegative on its actual positive carrier. -/
theorem gamma_density_nonneg {τ x : ℝ} (hτ : 0 < τ) (hx : 0 < x) :
    0 ≤ x ^ (τ - 1) * Real.exp (-x) / Real.Gamma τ :=
  div_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le)
    (Real.Gamma_pos_of_pos hτ).le

end DirectedDistances.Tauberian
