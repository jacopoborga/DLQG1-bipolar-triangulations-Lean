/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.AbelFinite
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Normed.Ring.Lemmas

/-! # Ordered Abel summation for a sine transform

Infrastructure for the first equality of `lem:abel`, Appendix A.5
sum of an explicitly summable sequence. The transformed series is expressed
through ordered partial sums, not `tsum`: absolute summability of the transformed
series is neither assumed nor concluded. No improper-integral identity is claimed. -/

public section
namespace DirectedDistances.Tauberian

open Finset Filter
open scoped Topology

/-- The difference of actual successive tails recovers a summable sequence. -/
theorem eq_tsum_tail_sub (f : ℕ → ℝ) (hf : Summable f) (k : ℕ) :
    f k = (∑' j, f (j + k)) - ∑' j, f (j + (k + 1)) := by
  have hk : Summable (fun j => f (j + k)) := (summable_nat_add_iff k).2 hf
  apply (eq_sub_iff_add_eq).2
  simpa only [sum_range_one, Nat.zero_add, Nat.add_assoc, Nat.add_comm 1 k] using
    hk.sum_add_tsum_nat_add 1

/-- Multiplication by a bounded sine factor preserves summability of a
nonnegative summable sequence. -/
theorem summable_mul_sin (f : ℕ → ℝ) (hf : Summable f)
    (hn : ∀ k, 0 ≤ f k) (t : ℝ) : Summable (fun k => f k * Real.sin ((k : ℝ) * t)) := by
  apply hf.of_norm_bounded
  intro k
  calc
    ‖f k * Real.sin ((k : ℝ) * t)‖ = f k * |Real.sin ((k : ℝ) * t)| := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hn k)]
    _ ≤ f k * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (hn k)
    _ = f k := mul_one _

/-- The Abel boundary term vanishes. No asymptotic rate or positive `t` is needed. -/
theorem tendsto_tail_mul_sin_zero (f : ℕ → ℝ) (hf : Summable f) (t : ℝ) :
    Tendsto (fun N : ℕ => (∑' j, f (j + (N + 1))) * Real.sin ((N : ℝ) * t))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => ∑' j, f (j + (N + 1))) atTop (𝓝 0) :=
    by
      have heq (N : ℕ) : (∑' j, f (j + (N + 1))) =
          (∑' j, f j) - ∑ k ∈ range (N + 1), f k :=
        (eq_sub_iff_add_eq').2 (hf.sum_add_tsum_nat_add (N + 1))
      simp_rw [heq]
      simpa only [sub_self, Function.comp_apply] using
        (tendsto_const_nhds (x := (∑' j, f j))).sub
          (hf.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))
  exact ht.zero_mul_isBoundedUnder_le
    (isBoundedUnder_of ⟨1, fun N => Real.abs_sin_le_one ((N : ℝ) * t)⟩)

/-- Ordered partial sums of the tail-weighted sine differences converge to the
sine transform. This supplies the series step of Appendix A.5 on a summable
nonnegative sequence; it does not supply the subsequent improper-integral step. -/
theorem tendsto_sum_tail_sin_sub (f : ℕ → ℝ) (hf : Summable f)
    (hn : ∀ k, 0 ≤ f k) (t : ℝ) :
    Tendsto
      (fun N : ℕ => ∑ k ∈ range N, (∑' j, f (j + (k + 1))) *
        (Real.sin (((k + 1 : ℕ) : ℝ) * t) - Real.sin ((k : ℝ) * t)))
      atTop (𝓝 (∑' k, f k * Real.sin ((k : ℝ) * t))) := by
  have hF := ((summable_mul_sin f hf hn t).hasSum.tendsto_sum_nat).comp
    (tendsto_add_atTop_nat 1)
  have hB := tendsto_tail_mul_sin_zero f hf t
  have heq (N : ℕ) :
      (∑ k ∈ range N, (∑' j, f (j + (k + 1))) *
        (Real.sin (((k + 1 : ℕ) : ℝ) * t) - Real.sin ((k : ℝ) * t))) =
      (∑ k ∈ range (N + 1), f k * Real.sin ((k : ℝ) * t)) +
        (∑' j, f (j + (N + 1))) * Real.sin ((N : ℝ) * t) := by
    have hN := sum_range_succ_of_tail_difference f (fun k => ∑' j, f (j + k))
      (fun k => Real.sin ((k : ℝ) * t)) (eq_tsum_tail_sub f hf)
      (by rw [Nat.cast_zero, zero_mul, Real.sin_zero]) N
    exact ((eq_sub_iff_add_eq).mp hN).symm
  simp_rw [heq]
  simpa only [add_zero, Function.comp_apply] using hF.add hB

end DirectedDistances.Tauberian
