/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.AbelSine

/-! # Uniform Dirichlet tail bounds

Infrastructure for the repaired proof of Appendix A.4 (`lem:bound-im-part`),
The remainder is a difference of two decreasing tails. Small pointwise
remainders alone do not justify cancellation of an oscillatory infinite sum;
the separate monotone bounds here supply that missing control. -/

public section
namespace DirectedDistances.Tauberian

open Finset Filter
open scoped Topology

/-- Finite summation by parts bounds every weighted increment sum by twice
the initial weight times a uniform bound for the primitive. Both endpoints
are retained, including the empty sum. -/
theorem norm_sum_antitone_mul_sub_le (S g : ℕ → ℝ)
    (hS : Antitone S) (hn : ∀ k, 0 ≤ S k) {B : ℝ}
    (hg : ∀ k, ‖g k‖ ≤ B) (N : ℕ) :
    ‖∑ k ∈ range N, S (k + 1) * (g (k + 1) - g k)‖ ≤ 2 * B * S 0 := by
  have hd (k : ℕ) : 0 ≤ S k - S (k + 1) :=
    sub_nonneg.mpr (hS (Nat.le_succ k))
  have hf : ‖∑ k ∈ range (N + 1), (S k - S (k + 1)) * g k‖ ≤
      B * (S 0 - S (N + 1)) := by
    calc
      _ ≤ ∑ k ∈ range (N + 1), B * (S k - S (k + 1)) := by
        apply norm_sum_le_of_le
        intro k _
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hd k)]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hg k) (hd k)
      _ = B * (S 0 - S (N + 1)) := by
        rw [← mul_sum]
        congr 1
        induction N with
        | zero => simp
        | succ N ih => rw [sum_range_succ, ih]; ring
  have heq := sum_range_succ_tail_mul S g N
  have hnorm (k j : ℕ) : ‖S k * g j‖ ≤ B * S k := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hn k)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hg j) (hn k)
  have heq' : (∑ k ∈ range N, S (k + 1) * (g (k + 1) - g k)) =
      ((∑ k ∈ range (N + 1), (S k - S (k + 1)) * g k) - S 0 * g 0) +
        S (N + 1) * g N := by
    linarith only [heq]
  rw [heq']
  calc
    _ ≤ (‖∑ k ∈ range (N + 1), (S k - S (k + 1)) * g k‖ +
        ‖S 0 * g 0‖) + ‖S (N + 1) * g N‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (B * (S 0 - S (N + 1)) + B * S 0) + B * S (N + 1) :=
      add_le_add (add_le_add hf (hnorm 0 0)) (hnorm (N + 1) N)
    _ = 2 * B * S 0 := by ring

/-- The same estimate indexed by the current weight. Extending that sequence
one place to the left keeps its first weight, so no larger initial value is
introduced. -/
theorem norm_sum_antitone_mul_sub_current_le (S g : ℕ → ℝ)
    (hS : Antitone S) (hn : ∀ k, 0 ≤ S k) {B : ℝ}
    (hg : ∀ k, ‖g k‖ ≤ B) (N : ℕ) :
    ‖∑ k ∈ range N, S k * (g (k + 1) - g k)‖ ≤ 2 * B * S 0 := by
  have hh := norm_sum_antitone_mul_sub_le (fun k => S (k - 1)) g
    (fun a b hab => hS (Nat.sub_le_sub_right hab 1)) (fun k => hn (k - 1)) hg N
  simpa only [Nat.add_sub_cancel, Nat.zero_sub] using hh

end DirectedDistances.Tauberian
