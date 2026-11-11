/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Vanishing for the negative-support convolution recurrence

degenerate case of Lemma 6.6 (`lem:Y-not-const`) to a convolution recurrence.
With `a n = g (-(n + 1))`, its negative-support recurrence has the form below.
This module proves only the sequence algebra; it neither constructs the source
Busemann law nor proves that the source law satisfies the recurrence. -/

public section
namespace DirectedDistances.Tauberian

/-- The convolution induction in the proof of Lemma 6.6: a zero first term
forces every term to vanish. This is internal sequence algebra, with the
recurrence as an explicit hypothesis, not the paper's source-law result. -/
theorem convolution_eq_zero_of_zero_initial (a : ℕ → ℝ) (h0 : a 0 = 0)
    (hrec : ∀ n, 3 * a (n + 1) =
      ∑ j ∈ Finset.range (n + 1), a j * a (n - j)) :
    ∀ n, a n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact h0
    | succ n =>
      have hs : (∑ j ∈ Finset.range (n + 1), a j * a (n - j)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [ih j (Finset.mem_range.mp hj), zero_mul]
      exact (mul_eq_zero.mp ((hrec n).trans hs)).resolve_left three_ne_zero

end DirectedDistances.Tauberian
