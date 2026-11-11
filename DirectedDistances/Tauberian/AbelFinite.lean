/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.NoncommRing

/-! # The finite Abel identity with its endpoint term

Algebraic infrastructure for `lem:abel`, Appendix A.5, specifically the displayed
keeps the initial term; the manuscript sine specialization has initial value
zero. Infinite ordered convergence and the improper integral are separate
obligations and are not supplied by this finite identity. -/

public section
namespace DirectedDistances.Tauberian

open Finset

universe u
variable {R : Type u} [Ring R]

/-- Finite summation by parts for a difference of successive tails. Both endpoint
terms are retained, including at `N = 0`. Multiplication order is unchanged. -/
theorem sum_range_succ_tail_mul (S g : ℕ → R) (N : ℕ) :
    (∑ k ∈ range (N + 1), (S k - S (k + 1)) * g k) =
      S 0 * g 0 + (∑ k ∈ range N, S (k + 1) * (g (k + 1) - g k)) -
        S (N + 1) * g N := by
  induction N with
  | zero => simp only [Nat.zero_add, sum_range_one, sum_range_zero, add_zero, sub_mul]
  | succ N ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    noncomm_ring

/-- When the test sequence starts at zero, the initial endpoint term vanishes. -/
theorem sum_range_succ_tail_mul_of_zero (S g : ℕ → R) (hg : g 0 = 0) (N : ℕ) :
    (∑ k ∈ range (N + 1), (S k - S (k + 1)) * g k) =
      (∑ k ∈ range N, S (k + 1) * (g (k + 1) - g k)) -
        S (N + 1) * g N := by
  rw [sum_range_succ_tail_mul, hg, mul_zero, zero_add]

/-- The finite manuscript identity once the tail-difference relation is proved.
The relation is an explicit input to this algebraic helper, not a probability
theorem or a completed version of Appendix A.5. -/
theorem sum_range_succ_of_tail_difference (f S g : ℕ → R)
    (hS : ∀ k, f k = S k - S (k + 1)) (hg : g 0 = 0) (N : ℕ) :
    (∑ k ∈ range (N + 1), f k * g k) =
      (∑ k ∈ range N, S (k + 1) * (g (k + 1) - g k)) -
        S (N + 1) * g N := by
  simp_rw [hS]
  exact sum_range_succ_tail_mul_of_zero S g hg N

end DirectedDistances.Tauberian
