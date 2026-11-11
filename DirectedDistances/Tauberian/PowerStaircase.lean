/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-! # Pointwise power-staircase error

Infrastructure for the mean-value bound in `lem:riemann`, Appendix A.6
for every `x ≥ 1`; no size-dependent constants are introduced. This file does
not evaluate an improper oscillatory integral or prove the full A.6 asymptotic. -/

public section
namespace DirectedDistances.Tauberian

open Set

/-- A negative power varies by at most its left-end derivative bound over an
interval of length at most one. -/
theorem abs_rpow_neg_sub_le {ν x y : ℝ} (hν : 0 ≤ ν) (hx : 0 < x)
    (hxy : x ≤ y) (hgap : y - x ≤ 1) :
    |x ^ (-ν) - y ^ (-ν)| ≤ ν * x ^ (-ν - 1) := by
  have hexp : -ν - 1 ≤ 0 := sub_nonpos.2 ((neg_nonpos.2 hν).trans zero_le_one)
  have hC : 0 ≤ ν * x ^ (-ν - 1) := mul_nonneg hν (Real.rpow_nonneg hx.le _)
  have hd : ∀ z ∈ Icc x y,
      HasDerivWithinAt (fun z : ℝ => z ^ (-ν))
        (-ν * z ^ (-ν - 1)) (Icc x y) z := by
    intro z hz
    exact (Real.hasDerivAt_rpow_const (Or.inl (hx.trans_le hz.1).ne')).hasDerivWithinAt
  have hb : ∀ z ∈ Ico x y, ‖-ν * z ^ (-ν - 1)‖ ≤ ν * x ^ (-ν - 1) := by
    intro z hz
    have hzpos : 0 < z := hx.trans_le hz.1
    calc
      ‖-ν * z ^ (-ν - 1)‖ = ν * z ^ (-ν - 1) := by
        rw [norm_mul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hν,
          Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hzpos.le _)]
      _ ≤ ν * x ^ (-ν - 1) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx hz.1 hexp) hν
  have hm := norm_image_sub_le_of_norm_deriv_le_segment' hd hb y ⟨hxy, le_rfl⟩
  have hm' : |x ^ (-ν) - y ^ (-ν)| ≤ (ν * x ^ (-ν - 1)) * (y - x) := by
    simpa only [Real.norm_eq_abs, abs_sub_comm] using hm
  exact hm'.trans ((mul_le_mul_of_nonneg_left hgap hC).trans_eq (mul_one _))

/-- The source's mean-value staircase bound holds with the single explicit
coefficient `ν`, uniformly for all `x ≥ 1`. -/
theorem abs_floor_rpow_neg_sub_le {ν x : ℝ} (hν : 0 ≤ ν) (hx : 1 ≤ x) :
    |(((⌊x⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - x ^ (-ν)| ≤ ν * x ^ (-ν - 1) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hxy : x ≤ ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one x).le
  have hgap : ((⌊x⌋₊ + 1 : ℕ) : ℝ) - x ≤ 1 := by
    rw [Nat.cast_add, Nat.cast_one, sub_le_iff_le_add, add_comm (1 : ℝ) x]
    exact add_le_add (Nat.floor_le hxpos.le) (le_refl (1 : ℝ))
  exact (abs_sub_comm _ _).trans_le (abs_rpow_neg_sub_le hν hxpos hxy hgap)

/-- A coarse bound valid at every positive argument, including the upper endpoint
of the initial cell. The sharper derivative bound controls the infinite tail. -/
theorem abs_floor_rpow_neg_sub_le_rpow {ν x : ℝ} (hν : 0 ≤ ν) (hx : 0 < x) :
    |(((⌊x⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - x ^ (-ν)| ≤ x ^ (-ν) := by
  have hxy : x ≤ ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one x).le
  have hpow := Real.rpow_le_rpow_of_nonpos hx hxy (neg_nonpos.2 hν)
  rw [abs_of_nonpos (sub_nonpos.2 hpow), neg_sub]
  exact sub_le_self _ (Real.rpow_nonneg (hx.le.trans hxy) _)

/-- On the initial open cell the singular power itself bounds the error.
Zero is excluded: for `ν > 0` Lean's negative-power value there would make this
inequality false. The excluded endpoint is null in integration. -/
theorem abs_floor_rpow_neg_sub_le_initial {ν x : ℝ} (hν : 0 ≤ ν)
    (hx : 0 < x) (hx1 : x < 1) :
    |(((⌊x⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - x ^ (-ν)| ≤ x ^ (-ν) := by
  have hfloor : ⌊x⌋₊ = 0 := by
    apply (Nat.floor_eq_iff hx.le).2
    constructor
    · simpa only [Nat.cast_zero] using hx.le
    · simpa only [Nat.cast_zero, zero_add] using hx1
  have hpow : 1 ≤ x ^ (-ν) := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow_of_nonpos hx hx1.le (neg_nonpos.2 hν)
  rw [hfloor, Nat.zero_add, Nat.cast_one, Real.one_rpow,
    abs_of_nonpos (sub_nonpos.2 hpow), neg_sub]
  exact sub_le_self _ zero_le_one

end DirectedDistances.Tauberian
