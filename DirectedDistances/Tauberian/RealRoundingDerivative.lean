/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.RealRoundingCharacteristic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Derivative of the bounded rounding characteristic error

The difference has a derivative at zero without assuming either unrounded or
rounded first moments. This alone does not establish the higher-order A3 error. -/

public section
namespace DirectedDistances.Tauberian
open MeasureTheory Filter Asymptotics
open scoped Topology

private theorem angle_difference_bound (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a - b| := by
  have heq : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I) =
      Complex.exp ((b : ℂ) * Complex.I) *
        (Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1) := by
    have ha : (b : ℂ) * Complex.I + (((a - b : ℝ) : ℂ) * Complex.I) =
        (a : ℂ) * Complex.I := by push_cast; ring
    rw [mul_sub, mul_one, ← Complex.exp_add, ha]
  rw [heq, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa only [mul_comm Complex.I, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b))

private theorem angle_difference_deriv (a b : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (((t * a : ℝ) : ℂ) * Complex.I) -
      Complex.exp (((t * b : ℝ) : ℂ) * Complex.I)) (((a - b : ℝ) : ℂ) * Complex.I) 0 := by
  have ha := (((hasDerivAt_id (0 : ℝ)).mul_const a).ofReal_comp.mul_const Complex.I).cexp
  have hb := (((hasDerivAt_id (0 : ℝ)).mul_const b).ofReal_comp.mul_const Complex.I).cexp
  simpa only [id_eq, zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_mul,
    Complex.ofReal_sub, sub_mul, Pi.sub_apply] using! ha.sub hb

/-- The actual lag is integrable even when neither original first moment is known. -/
theorem integrable_floor_abs_lag {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (hX₀ : ∀ᵐ ω ∂μ, 0 ≤ X ω) :
    Integrable (fun ω => X ω - (Nat.floor |X ω| : ℝ)) μ := by
  have hY : Measurable (fun ω => (Nat.floor |X ω| : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_floor_abs hX)
  apply (integrable_const (1 : ℝ)).mono' (hX.sub hY).aestronglyMeasurable
  filter_upwards [ae_floor_abs_lag hX₀] with ω hω
  change |X ω - (Nat.floor |X ω| : ℝ)| ≤ 1
  rw [abs_of_nonneg hω.1]
  exact hω.2.le

/-- Bounded dominated convergence gives the derivative of the actual characteristic
expectation difference at zero, without an EX or EY moment premise. -/
theorem hasDerivAt_CFroundingdifference {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (hX₀ : ∀ᵐ ω ∂μ, 0 ≤ X ω) :
    HasDerivAt (fun t : ℝ =>
      (∫ ω, Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I) ∂μ) -
      (∫ ω, Complex.exp (((t * (Nat.floor |X ω| : ℝ) : ℝ) : ℂ) * Complex.I) ∂μ))
      ((((∫ ω, X ω - (Nat.floor |X ω| : ℝ) ∂μ) : ℝ) : ℂ) * Complex.I) 0 := by
  let Y : Ω → ℝ := fun ω => (Nat.floor |X ω| : ℝ)
  let U : Ω → ℝ := fun ω => X ω - Y ω
  let D : ℝ → Ω → ℂ := fun t ω =>
    Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I) -
      Complex.exp (((t * Y ω : ℝ) : ℂ) * Complex.I)
  have hY : Measurable Y :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_floor_abs hX)
  have hU : Integrable U μ := integrable_floor_abs_lag hX hX₀
  have hDi (t : ℝ) : Integrable (D t) μ :=
    (integrable_real_characteristic hX t).sub (integrable_real_characteristic hY t)
  have hb : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), ∀ᵐ ω ∂μ, ‖t⁻¹ • D t ω‖ ≤ 1 := by
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
    filter_upwards [ae_floor_abs_lag hX₀] with ω hω
    have hlag : |X ω - Y ω| ≤ 1 := by rw [abs_of_nonneg hω.1]; exact hω.2.le
    rw [norm_smul, Real.norm_eq_abs, abs_inv]
    calc
      _ ≤ |t|⁻¹ * |t * X ω - t * Y ω| :=
        mul_le_mul_of_nonneg_left (angle_difference_bound _ _) (inv_nonneg.mpr (abs_nonneg t))
      _ = |X ω - Y ω| := by rw [← mul_sub, abs_mul, inv_mul_cancel_left₀ (abs_ne_zero.mpr ht0)]
      _ ≤ 1 := hlag
  have hl : ∀ᵐ ω ∂μ, Tendsto (fun t : ℝ => t⁻¹ • D t ω)
      (𝓝[≠] (0 : ℝ)) (𝓝 ((U ω : ℂ) * Complex.I)) := by
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [zero_add, sub_zero, zero_mul, Complex.ofReal_zero,
        zero_mul, Complex.exp_zero, sub_self, sub_zero] using
        (angle_difference_deriv (X ω) (Y ω)).tendsto_slope_zero
  have hdct := tendsto_integral_filter_of_dominated_convergence (fun _ : Ω => (1 : ℝ))
    (Filter.Eventually.of_forall (fun t : ℝ => ((hDi t).smul t⁻¹).aestronglyMeasurable))
    hb (integrable_const 1) hl
  have hval : (∫ ω, (U ω : ℂ) * Complex.I ∂μ) = ((∫ ω, U ω ∂μ : ℝ) : ℂ) * Complex.I := by
    rw [integral_mul_const, integral_complex_ofReal]
  rw [hval] at hdct
  apply hasDerivAt_iff_tendsto_slope.mpr
  convert hdct using 1
  ext t
  simp only [Pi.smul_apply]
  rw [integral_smul, integral_sub (integrable_real_characteristic hX t)
    (integrable_real_characteristic hY t)]
  simp only [slope_def_module, sub_zero, zero_mul, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero, integral_const, measureReal_def,
    measure_univ, ENNReal.toReal_one, sub_self, sub_zero]
  rfl

end DirectedDistances.Tauberian
