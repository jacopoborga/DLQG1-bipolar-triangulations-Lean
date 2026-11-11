/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.PowerIntegrals
public import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Absolute integrability of the power-staircase difference

Infrastructure for `lem:riemann`, Appendix A.6
not be absolutely integrable individually. Their difference is integrable;
both integrability and the explicit norm bound are proved, with one coefficient
`1 / (1 - ν) + 1` for the full positive half-line. -/

public section
namespace DirectedDistances.Tauberian

open Set MeasureTheory
open scoped Interval

/-- The staircase difference is measurable, including its countable jump set. -/
theorem measurable_power_staircase_error (ν : ℝ) :
    Measurable (fun x : ℝ => (((⌊x⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - x ^ (-ν)) :=
  ((measurable_of_countable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-ν))).comp
    Nat.measurable_floor).sub (measurable_id.pow_const (-ν))

/-- Integrability near zero uses `ν < 1`, and the comparison includes `x = 1`. -/
theorem integrableOn_power_staircase_error_initial {ν : ℝ} (hν₀ : 0 ≤ ν) (hν₁ : ν < 1) :
    IntegrableOn (fun x : ℝ => (((⌊x⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - x ^ (-ν)) (Ioc 0 1) := by
  have hp : IntegrableOn (fun x : ℝ => x ^ (-ν)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 (intervalIntegrable_rpow_neg hν₁)
  apply hp.mono' (measurable_power_staircase_error ν).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  change ‖(((⌊x⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - x ^ (-ν)‖ ≤ x ^ (-ν)
  rw [Real.norm_eq_abs]
  exact abs_floor_rpow_neg_sub_le_rpow hν₀ hx.1

/-- Integrability at infinity uses the sharper derivative bound and `ν > 0`. -/
theorem integrableOn_power_staircase_error_tail {ν : ℝ} (hν : 0 < ν) :
    IntegrableOn (fun x : ℝ => (((⌊x⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - x ^ (-ν)) (Ioi 1) := by
  have hp := (integrableOn_rpow_neg_sub_one hν).const_mul ν
  apply hp.mono' (measurable_power_staircase_error ν).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change ‖(((⌊x⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - x ^ (-ν)‖ ≤ ν * x ^ (-ν - 1)
  rw [Real.norm_eq_abs]
  exact abs_floor_rpow_neg_sub_le hν.le hx.le

/-- The difference, rather than either separate power term, is absolutely
integrable on the positive half-line. -/
theorem integrableOn_power_staircase_error {ν : ℝ} (hν₀ : 0 < ν) (hν₁ : ν < 1) :
    IntegrableOn (fun x : ℝ => (((⌊x⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - x ^ (-ν)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  exact (integrableOn_power_staircase_error_initial hν₀.le hν₁).union
    (integrableOn_power_staircase_error_tail hν₀)

/-- The unit-scale L¹ error has one explicit bound depending only on `ν`. -/
theorem integral_norm_power_staircase_error_le {ν : ℝ} (hν₀ : 0 < ν) (hν₁ : ν < 1) :
    (∫ x : ℝ in Ioi 0, ‖(((⌊x⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - x ^ (-ν)‖) ≤
      1 / (1 - ν) + 1 := by
  have hi := (integrableOn_power_staircase_error_initial hν₀.le hν₁).norm
  have ht := (integrableOn_power_staircase_error_tail hν₀).norm
  have hd : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := by
    apply disjoint_left.2
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1),
    setIntegral_union hd measurableSet_Ioi hi ht]
  apply add_le_add
  · have hp : IntegrableOn (fun x : ℝ => x ^ (-ν)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 (intervalIntegrable_rpow_neg hν₁)
    calc
      (∫ x : ℝ in Ioc 0 1, ‖(((⌊x⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - x ^ (-ν)‖) ≤
          ∫ x : ℝ in Ioc 0 1, x ^ (-ν) := by
        apply integral_mono_ae hi hp
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        change ‖(((⌊x⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - x ^ (-ν)‖ ≤ x ^ (-ν)
        rw [Real.norm_eq_abs]
        exact abs_floor_rpow_neg_sub_le_rpow hν₀.le hx.1
      _ = 1 / (1 - ν) :=
        (intervalIntegral.integral_of_le zero_le_one).symm.trans (integral_rpow_neg_zero_one hν₁)
  · have hp := (integrableOn_rpow_neg_sub_one hν₀).const_mul ν
    calc
      (∫ x : ℝ in Ioi 1, ‖(((⌊x⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - x ^ (-ν)‖) ≤
          ∫ x : ℝ in Ioi 1, ν * x ^ (-ν - 1) := by
        apply integral_mono_ae ht hp
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        change ‖(((⌊x⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - x ^ (-ν)‖ ≤ ν * x ^ (-ν - 1)
        rw [Real.norm_eq_abs]
        exact abs_floor_rpow_neg_sub_le hν₀.le hx.le
      _ = 1 := integral_mul_rpow_neg_sub_one hν₀

end DirectedDistances.Tauberian
