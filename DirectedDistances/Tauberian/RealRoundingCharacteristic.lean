/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.RealCharacteristicBasic
public import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Characteristic-function error of nonnegative real rounding

Original Appendix A permits nonnegative real random variables. Rounding by
`Nat.floor |X|` preserves the sublinear characteristic expansion without any
moment premise. -/

public section
namespace DirectedDistances.Tauberian
open MeasureTheory Filter Asymptotics
open scoped Topology

private theorem exp_angle_difference_bound (a b : ℝ) :
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

private theorem floor_abs_lag {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x - (Nat.floor |x| : ℝ) ∧ x - (Nat.floor |x| : ℝ) < 1 := by
  rw [abs_of_nonneg hx]
  exact ⟨sub_nonneg.mpr (Nat.floor_le hx), by linarith [Nat.lt_floor_add_one x]⟩

private theorem integrable_exp_angle {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) (t : ℝ) :
    Integrable (fun ω => Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I)) μ :=
  integrable_real_characteristic hX t

private theorem abs_id_isLittleO_abs_rpow {ν : ℝ} (hν : ν < 1) :
    (fun t : ℝ => |t|) =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => |t| ^ ν) := by
  have hp : 0 < 1 - ν := sub_pos.mpr hν
  have ht : Tendsto (fun t : ℝ => |t| ^ (1 - ν)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 (1 - ν) (Or.inr hp.le)).tendsto.comp
      (show Tendsto (fun t : ℝ => |t|) (𝓝[≠] (0 : ℝ)) (𝓝 0) from
        by simpa only [abs_zero] using
          (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds)
    simpa only [Function.comp_def, Real.zero_rpow hp.ne'] using h
  apply isLittleO_of_tendsto'
    (eventually_mem_nhdsWithin.mono (fun t ht hz => by
      have ht0 : t ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
      exact False.elim ((Real.rpow_pos_of_pos (abs_pos.mpr ht0) _).ne' hz)))
  apply ht.congr'
  filter_upwards [eventually_mem_nhdsWithin] with t ht0
  have htne : t ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht0
  rw [Real.rpow_sub (abs_pos.mpr htne), Real.rpow_one]

private theorem integral_exp_angle_difference_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (hlag : ∀ᵐ ω ∂μ, |X ω - Y ω| ≤ 1) (t : ℝ) :
    ‖(∫ ω, Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I) ∂μ) -
      (∫ ω, Complex.exp (((t * Y ω : ℝ) : ℂ) * Complex.I) ∂μ)‖ ≤ |t| := by
  rw [← integral_sub (integrable_exp_angle μ hX t) (integrable_exp_angle μ hY t)]
  have hb : ∀ᵐ ω ∂μ,
      ‖Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((t * Y ω : ℝ) : ℂ) * Complex.I)‖ ≤ |t| := by
    filter_upwards [hlag] with ω hω
    calc
      _ ≤ |t * X ω - t * Y ω| := exp_angle_difference_bound _ _
      _ = |t| * |X ω - Y ω| := by rw [← mul_sub, abs_mul]
      _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hω (abs_nonneg t)
      _ = |t| := mul_one _
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hb

/-- The actual rounded magnitude is a measurable natural-valued variable. -/
theorem measurable_floor_abs {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ}
    (hX : Measurable X) : Measurable (fun ω => Nat.floor |X ω|) :=
  Nat.measurable_floor.comp (continuous_abs.measurable.comp hX)

/-- Nonnegative real values have a genuine unit lag from their rounded magnitude. -/
theorem ae_floor_abs_lag {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (hX₀ : ∀ᵐ ω ∂μ, 0 ≤ X ω) :
    ∀ᵐ ω ∂μ, 0 ≤ X ω - (Nat.floor |X ω| : ℝ) ∧
      X ω - (Nat.floor |X ω| : ℝ) < 1 := hX₀.mono fun _ h => floor_abs_lag h

/-- Genuine characteristic expectations differ by at most the frequency after rounding.
No first moment of either variable is assumed. -/
theorem CFroundingdifference_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (hX₀ : ∀ᵐ ω ∂μ, 0 ≤ X ω) (t : ℝ) :
    Integrable (fun ω => Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I)) μ ∧
    Integrable (fun ω => Complex.exp (((t * (Nat.floor |X ω| : ℝ) : ℝ) : ℂ) * Complex.I)) μ ∧
    ‖(∫ ω, Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I) ∂μ) -
      (∫ ω, Complex.exp (((t * (Nat.floor |X ω| : ℝ) : ℝ) : ℂ) * Complex.I) ∂μ)‖ ≤ |t| := by
  have hY : Measurable (fun ω => (Nat.floor |X ω| : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_floor_abs hX)
  refine ⟨integrable_real_characteristic hX t, integrable_real_characteristic hY t, ?_⟩
  apply integral_exp_angle_difference_bound μ hX hY
  filter_upwards [ae_floor_abs_lag hX₀] with ω hω
  rw [abs_of_nonneg hω.1]
  exact hω.2.le

/-- Rounding a nonnegative real variable does not change its sublinear characteristic
expansion, on the two-sided punctured neighborhood of zero. -/
theorem CFroundingdifference_isLittleO_abs_rpow {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (hX₀ : ∀ᵐ ω ∂μ, 0 ≤ X ω) {ν : ℝ}
    (_hν₀ : 0 < ν) (hν₁ : ν < 1) :
    (fun t : ℝ => (∫ ω, Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I) ∂μ) -
      (∫ ω, Complex.exp (((t * (Nat.floor |X ω| : ℝ) : ℝ) : ℂ) * Complex.I) ∂μ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => |t| ^ ν) := by
  have hb : (fun t : ℝ => (∫ ω, Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I) ∂μ) -
      (∫ ω, Complex.exp (((t * (Nat.floor |X ω| : ℝ) : ℝ) : ℂ) * Complex.I) ∂μ))
      =O[𝓝[≠] (0 : ℝ)] (fun t : ℝ => |t|) := by
    apply IsBigO.of_bound 1
    exact Filter.Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs, abs_abs, one_mul] using
        (CFroundingdifference_bound hX hX₀ t).2.2
  exact hb.trans_isLittleO (abs_id_isLittleO_abs_rpow hν₁)

end DirectedDistances.Tauberian
