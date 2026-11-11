/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Basic

/-! # Cubic identity from the complex characteristic quadratic

Algebra step in the proofs of Propositions 6.2 and 6.8: taking the imaginary
resp. `eq:quadratic` (`756–758`), with `re F̂⁻ = (F - K)/2`
(`eq:real-part-fhat`, `385–388`; `eq:real-part-fhat2`, `776–779`) and nonzero
imaginary part, yields `eq:third-ord2` (`395–400`) resp. `eq:third-ord` (`786–793`). -/

public section
namespace DirectedDistances.Recursive

theorem characteristic_cubic_identity_of_quadratic
    (F K : ℝ) (z : ℂ)
    (hreal : z.re = (F - K) / 2)
    (himag : z.im ≠ 0)
    (hquad :
      (F : ℂ) ^ 2 * z ^ 2 + (3 * (F : ℂ) - 1) * z + (F : ℂ) = 0) :
    F ^ 3 - K * F ^ 2 + 3 * F - 1 = 0 := by
  have h := congrArg Complex.im hquad
  simp [pow_two, Complex.mul_im, Complex.mul_re, Complex.sub_im, Complex.sub_re,
    Complex.add_im] at h
  have h2 : z.im * (F ^ 3 - K * F ^ 2 + 3 * F - 1) = 0 := by
    rw [hreal] at h
    linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 himag
  · exact h3

end DirectedDistances.Recursive
