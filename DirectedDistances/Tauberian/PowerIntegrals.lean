/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.PowerStaircase
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith

/-! # Integrals of the A.6 power majorants

Infrastructure for `lem:riemann`
majorant value retain all factors of `ν`; the latter contributes exactly one
after multiplication by the pointwise coefficient `ν`. Integrability is stated
separately from integral values to rule out Bochner default-zero reasoning. -/

public section
namespace DirectedDistances.Tauberian

open Set MeasureTheory
open scoped Interval

/-- The power singularity at zero is locally integrable exactly on the side of
the source exponent used here. -/
theorem intervalIntegrable_rpow_neg {ν a b : ℝ} (hν : ν < 1) :
    IntervalIntegrable (fun x : ℝ => x ^ (-ν)) volume a b :=
  intervalIntegral.intervalIntegrable_rpow' (neg_lt_neg hν)

/-- The initial-cell majorant has the exact scale `t/(1-ν)`. -/
theorem initial_power_integral {ν t : ℝ} (hν : ν < 1) (ht : 0 < t) :
    t ^ ν * (∫ u in (0 : ℝ)..t, u ^ (-ν)) = t / (1 - ν) := by
  have he : -ν + 1 = 1 - ν := by rw [sub_eq_add_neg, add_comm]
  have hne : -ν + 1 ≠ 0 := by
    rw [he]
    exact (sub_pos.2 hν).ne'
  rw [integral_rpow (Or.inl (neg_lt_neg hν)), Real.zero_rpow hne, sub_zero,
    ← mul_div_assoc, ← Real.rpow_add ht, add_neg_cancel_left, Real.rpow_one, he]

/-- The corresponding unit-interval integral. -/
theorem integral_rpow_neg_zero_one {ν : ℝ} (hν : ν < 1) :
    (∫ u in (0 : ℝ)..1, u ^ (-ν)) = 1 / (1 - ν) := by
  simpa only [Real.one_rpow, one_mul] using initial_power_integral hν zero_lt_one

/-- The tail derivative majorant is integrable for every strictly positive `ν`. -/
theorem integrableOn_rpow_neg_sub_one {ν : ℝ} (hν : 0 < ν) :
    IntegrableOn (fun x : ℝ => x ^ (-ν - 1)) (Ioi (1 : ℝ)) := by
  apply integrableOn_Ioi_rpow_of_lt (hc := zero_lt_one)
  linarith only [hν]

/-- The unscaled tail majorant has value `1/ν`, with the denominator explicit. -/
theorem integral_rpow_neg_sub_one {ν : ℝ} (hν : 0 < ν) :
    (∫ x : ℝ in Ioi 1, x ^ (-ν - 1)) = 1 / ν := by
  have hexp : -ν - 1 < -1 := by linarith only [hν]
  rw [integral_Ioi_rpow_of_lt hexp zero_lt_one, Real.one_rpow,
    sub_add_cancel, neg_div_neg_eq]

/-- With the explicit pointwise coefficient `ν`, the tail majorant contributes
exactly one, rather than suppressing a factor in a generic constant. -/
theorem integral_mul_rpow_neg_sub_one {ν : ℝ} (hν : 0 < ν) :
    (∫ x : ℝ in Ioi 1, ν * x ^ (-ν - 1)) = 1 := by
  rw [integral_const_mul, integral_rpow_neg_sub_one hν, one_div, mul_inv_cancel₀ hν.ne']

end DirectedDistances.Tauberian
