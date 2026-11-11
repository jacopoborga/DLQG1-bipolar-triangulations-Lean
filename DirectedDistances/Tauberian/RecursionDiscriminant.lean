/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Algebra for the common Section 6 quadratic

The polynomial in `recursive.tex`, equations `eq:quadratic-new` and
`eq:quadratic`, is shared by the LDP and SDP computations. These are algebraic
dependencies of Lemma 6.7 (`lem:nonreal2`), not a formalization of its source
random variable or of the recursive distribution equations. -/

public section
namespace DirectedDistances.Tauberian

/-- Exact factorization of the discriminant used in Lemma 6.7. -/
theorem recursion_discriminant_factorization (F : ℝ) :
    (3 * F - 1) ^ 2 - 4 * F ^ 3 = -(F - 1) ^ 2 * (4 * F - 1) := by
  ring

/-- The common discriminant is strictly negative above `1/4`, except at `1`.
This replaces the printed Taylor estimate by an exact polynomial identity. -/
theorem recursion_discriminant_neg {F : ℝ} (hF : 1 / 4 < F) (hF1 : F ≠ 1) :
    (3 * F - 1) ^ 2 - 4 * F ^ 3 < 0 := by
  rw [recursion_discriminant_factorization]
  have hs : 0 < (F - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hF1)
  have hp : 0 < 4 * F - 1 := by linarith only [hF]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hs) hp

/-- Any root of the common quadratic has nonzero imaginary part when its
actual real coefficient lies above `1/4` and differs from `1`. -/
theorem im_ne_zero_of_recursion_quadratic {F : ℝ} {z : ℂ}
    (hF : 1 / 4 < F) (hF1 : F ≠ 1)
    (hq : (F : ℂ) ^ 2 * z ^ 2 + (3 * (F : ℂ) - 1) * z + (F : ℂ) = 0) :
    z.im ≠ 0 := by
  intro hz
  have hr := congrArg Complex.re hq
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.zero_re, pow_two, hz, mul_zero, zero_mul, sub_zero,
    add_zero] at hr
  have hd : discrim (F ^ 2) (3 * F - 1) F =
      (2 * F ^ 2 * z.re + (3 * F - 1)) ^ 2 :=
    discrim_eq_sq_of_quadratic_eq_zero (by nlinarith only [hr])
  have hn := recursion_discriminant_neg hF hF1
  have he : discrim (F ^ 2) (3 * F - 1) F = (3 * F - 1) ^ 2 - 4 * F ^ 3 := by
    unfold discrim
    ring
  rw [he] at hd
  exact (not_lt_of_ge (hd.symm ▸ sq_nonneg (2 * F ^ 2 * z.re + (3 * F - 1)))) hn

end DirectedDistances.Tauberian
