/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.RealRoundingDerivative
import DirectedDistances.Tauberian.NormalizedBoundary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Quadratic centered rounding error

The finite rounded first moment is an explicit ordinary helper input, to be
produced from the characteristic derivative before this helper is consumed. -/

public section
namespace DirectedDistances.Tauberian
open MeasureTheory Filter Asymptotics
open scoped Topology

private theorem centered_angle_difference_bound {u y t : ℝ}
    (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) (hy : 0 ≤ y) (ht : |t| ≤ 1) :
    ‖Complex.exp (((t * (y + u) : ℝ) : ℂ) * Complex.I) -
      Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) -
        ((u : ℂ) * Complex.I) * (t : ℂ)‖ ≤ |t| ^ 2 * (1 + y) := by
  let a : ℂ := ((t * y : ℝ) : ℂ) * Complex.I
  let b : ℂ := ((t * u : ℝ) : ℂ) * Complex.I
  have heq : Complex.exp (((t * (y + u) : ℝ) : ℂ) * Complex.I) -
      Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) -
        ((u : ℂ) * Complex.I) * (t : ℂ) =
      Complex.exp a * (Complex.exp b - 1 - b) + (Complex.exp a - 1) * b := by
    have hx : (((t * (y + u) : ℝ) : ℂ) * Complex.I) = a + b := by
      dsimp [a, b]; push_cast; ring
    rw [hx, Complex.exp_add]
    dsimp [a, b]
    push_cast
    ring
  have hnb : ‖b‖ = |t| * u := by
    simp only [b, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one, abs_of_nonneg hu₀]
  have hnb1 : ‖b‖ ≤ 1 := by rw [hnb]; nlinarith [abs_nonneg t]
  have hquad := Complex.norm_exp_sub_one_sub_id_le hnb1
  have hlin : ‖Complex.exp a - 1‖ ≤ |t| * y := by
    simpa only [a, mul_comm _ Complex.I, Real.norm_eq_abs, abs_mul, abs_of_nonneg hy] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * y))
  rw [heq]
  calc
    _ ≤ ‖Complex.exp a * (Complex.exp b - 1 - b)‖ + ‖(Complex.exp a - 1) * b‖ := norm_add_le _ _
    _ = ‖Complex.exp b - 1 - b‖ + ‖Complex.exp a - 1‖ * ‖b‖ := by
      rw [norm_mul, norm_mul, show ‖Complex.exp a‖ = 1 by exact Complex.norm_exp_ofReal_mul_I _, one_mul]
    _ ≤ (|t| * u) ^ 2 + (|t| * y) * (|t| * u) := by
      rw [← hnb]
      exact add_le_add hquad (mul_le_mul_of_nonneg_right hlin (norm_nonneg b))
    _ ≤ |t| ^ 2 * (1 + y) := by
      have hu2 : u ^ 2 ≤ 1 := by nlinarith only [hu₀, hu₁]
      have h1 := mul_nonneg (sq_nonneg |t|) (sub_nonneg.mpr hu2)
      have h2 := mul_nonneg (mul_nonneg (sq_nonneg |t|) hy) (sub_nonneg.mpr hu₁)
      nlinarith only [h1, h2]

private theorem centered_integral_identity {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (hU : Integrable (fun ω => X ω - Y ω) μ) (t : ℝ) :
    (∫ ω, Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I) -
      Complex.exp (((t * Y ω : ℝ) : ℂ) * Complex.I) -
      ((((X ω - Y ω : ℝ) : ℂ) * Complex.I) * (t : ℂ)) ∂μ) =
    (∫ ω, Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I) ∂μ) -
      (∫ ω, Complex.exp (((t * Y ω : ℝ) : ℂ) * Complex.I) ∂μ) -
      ((((∫ ω, X ω - Y ω ∂μ : ℝ) : ℂ) * Complex.I) * (t : ℂ)) := by
  have hdiff : Integrable (fun ω => Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I) -
      Complex.exp (((t * Y ω : ℝ) : ℂ) * Complex.I)) μ := by
    simpa only [Pi.sub_apply] using! (integrable_real_characteristic hX t).sub
      (integrable_real_characteristic hY t)
  erw [integral_sub hdiff
    ((hU.ofReal.mul_const Complex.I).mul_const (t : ℂ)),
    integral_sub (integrable_real_characteristic hX t) (integrable_real_characteristic hY t),
    integral_mul_const, integral_mul_const, integral_complex_ofReal]
  simp only [Algebra.algebraMap_self_apply]

/-- The centered rounding characteristic error is quadratic when the actual rounded
first moment is integrable. This conditional ordinary input must be produced upstream. -/
theorem CFrounding_centered_isBigO_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (hX₀ : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hYI : Integrable (fun ω => (Nat.floor |X ω| : ℝ)) μ) :
    (fun t : ℝ =>
      (∫ ω, Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I) ∂μ) -
      (∫ ω, Complex.exp (((t * (Nat.floor |X ω| : ℝ) : ℝ) : ℂ) * Complex.I) ∂μ) -
      ((((∫ ω, X ω - (Nat.floor |X ω| : ℝ) ∂μ : ℝ) : ℂ) * Complex.I) * (t : ℂ)))
      =O[𝓝 (0 : ℝ)] (fun t : ℝ => |t| ^ 2) := by
  let Y : Ω → ℝ := fun ω => (Nat.floor |X ω| : ℝ)
  let U : Ω → ℝ := fun ω => X ω - Y ω
  have hY : Measurable Y :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_floor_abs hX)
  have hU : Integrable U μ := integrable_floor_abs_lag hX hX₀
  have hYnonneg (ω : Ω) : 0 ≤ Y ω := Nat.cast_nonneg _
  apply IsBigO.of_bound (1 + ∫ ω, Y ω ∂μ)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with t ht
  have ht1 : |t| ≤ 1 := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using (show dist t 0 ≤ 1 from ht.le)
  rw [← centered_integral_identity hX hY hU t]
  have hb : ∀ᵐ ω ∂μ,
      ‖Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((t * Y ω : ℝ) : ℂ) * Complex.I) -
        ((((X ω - Y ω : ℝ) : ℂ) * Complex.I) * (t : ℂ))‖ ≤
          |t| ^ 2 * (1 + Y ω) := by
    filter_upwards [ae_floor_abs_lag hX₀] with ω hω
    have hu₀ : 0 ≤ X ω - Y ω := hω.1
    have hu₁ : X ω - Y ω ≤ 1 := hω.2.le
    have h := centered_angle_difference_bound hu₀ hu₁ (hYnonneg ω) ht1
    rw [show Y ω + (X ω - Y ω) = X ω by ring] at h
    exact h
  have hbi : Integrable (fun ω => |t| ^ 2 * (1 + Y ω)) μ :=
    ((integrable_const 1).add hYI).const_mul _
  calc
    _ ≤ ∫ ω, |t| ^ 2 * (1 + Y ω) ∂μ := norm_integral_le_of_norm_le hbi hb
    _ = (1 + ∫ ω, Y ω ∂μ) * ‖|t| ^ 2‖ := by
      rw [integral_const_mul, integral_add (integrable_const 1) hYI]
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one, Real.norm_eq_abs,
        abs_pow, abs_abs]
      ring

/-- The centered rounding error is below the source A3 scale after the rounded
first moment has genuinely been produced. -/
theorem CFrounding_centered_isLittleO_abs_rpow_one_add {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (hX₀ : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hYI : Integrable (fun ω => (Nat.floor |X ω| : ℝ)) μ)
    {ν : ℝ} (_hν₀ : 0 < ν) (hν₁ : ν < 1) :
    (fun t : ℝ =>
      (∫ ω, Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I) ∂μ) -
      (∫ ω, Complex.exp (((t * (Nat.floor |X ω| : ℝ) : ℝ) : ℂ) * Complex.I) ∂μ) -
      ((((∫ ω, X ω - (Nat.floor |X ω| : ℝ) ∂μ : ℝ) : ℂ) * Complex.I) * (t : ℂ)))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => |t| ^ (1 + ν)) :=
  ((CFrounding_centered_isBigO_sq hX hX₀ hYI).mono nhdsWithin_le_nhds).trans_isLittleO
    (abs_sq_isLittleO_abs_rpow_one_add hν₁)

end DirectedDistances.Tauberian
