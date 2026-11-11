/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Group.FunctionSeries








public section

namespace DirectedDistances.Tauberian

/-- The terms of a nonnegative weighted power series are bounded by their
coefficients throughout the closed unit disk. -/
theorem norm_weighted_pow_le {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k)
    {z : ℂ} (hz : ‖z‖ ≤ 1) (k : ℕ) :
    ‖(f k : ℂ) * z ^ k‖ ≤ f k := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf k), norm_pow]
  exact mul_le_of_le_one_right (hf k) (pow_le_one₀ (norm_nonneg z) hz)

/-- A summable nonnegative coefficient sequence defines a genuine convergent
power series at every point of the closed unit disk. -/
theorem hasSum_weighted_pow {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hs : Summable f) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun k => (f k : ℂ) * z ^ k) (∑' k, (f k : ℂ) * z ^ k) :=
  (hs.of_norm_bounded (norm_weighted_pow_le hf hz)).hasSum

/-- The power series with summable nonnegative coefficients converges uniformly
on the entire closed unit disk, including the boundary. -/
theorem tendstoUniformlyOn_sum_weighted_pow {f : ℕ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hs : Summable f) :
    TendstoUniformlyOn
      (fun (N : ℕ) (z : ℂ) => ∑ k ∈ Finset.range N, (f k : ℂ) * z ^ k)
      (fun z : ℂ => ∑' k, (f k : ℂ) * z ^ k)
      Filter.atTop (Metric.closedBall 0 1) := by
  apply tendstoUniformlyOn_tsum_nat hs
  intro k z hz
  exact norm_weighted_pow_le hf (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz) k

/-- Uniform convergence gives continuity of the series on the closed unit disk. -/
theorem continuousOn_tsum_weighted_pow {f : ℕ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hs : Summable f) :
    ContinuousOn (fun z : ℂ => ∑' k, (f k : ℂ) * z ^ k)
      (Metric.closedBall 0 1) := by
  apply continuousOn_tsum (f := fun (k : ℕ) (z : ℂ) => (f k : ℂ) * z ^ k)
    (fun k => (continuous_const.mul (continuous_id.pow k)).continuousOn) hs
  intro k z hz
  exact norm_weighted_pow_le hf (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz) k

/-- The same literal power series is holomorphic on the open unit disk. -/
theorem differentiableOn_tsum_weighted_pow {f : ℕ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hs : Summable f) :
    DifferentiableOn ℂ (fun z : ℂ => ∑' k, (f k : ℂ) * z ^ k)
      (Metric.ball 0 1) := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    (F := fun (k : ℕ) (z : ℂ) => (f k : ℂ) * z ^ k) hs
    (fun k => ((differentiable_const (f k : ℂ)).mul (differentiable_id.pow k)).differentiableOn)
    Metric.isOpen_ball
  intro k z hz
  exact norm_weighted_pow_le hf
    (le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hz)) k

/-- Summation of the coefficients at one agrees with their prescribed mass. -/
theorem tsum_weighted_pow_one {f : ℕ → ℝ} {m : ℝ} (hs : HasSum f m) :
    (∑' k, (f k : ℂ) * (1 : ℂ) ^ k) = (m : ℂ) := by
  simpa only [one_pow, mul_one] using (Complex.hasSum_ofReal.mpr hs).tsum_eq

/-- Revised Appendix A, the assertion following `eqn-gen-func-def`: for any
nonnegative integer probability law, its literal generating series converges
uniformly on the closed unit disk, is continuous there, is holomorphic on the
open unit disk, and has value one at one. The explicit `HasSum` clause certifies
that every use of `tsum` on the source domain is the convergent series. -/
theorem probability_generating_series_properties {f : ℕ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hs : HasSum f 1) :
    (∀ z : ℂ, ‖z‖ ≤ 1 →
      HasSum (fun k => (f k : ℂ) * z ^ k) (∑' k, (f k : ℂ) * z ^ k)) ∧
    TendstoUniformlyOn
      (fun (N : ℕ) (z : ℂ) => ∑ k ∈ Finset.range N, (f k : ℂ) * z ^ k)
      (fun z : ℂ => ∑' k, (f k : ℂ) * z ^ k)
      Filter.atTop (Metric.closedBall 0 1) ∧
    ContinuousOn (fun z : ℂ => ∑' k, (f k : ℂ) * z ^ k)
      (Metric.closedBall 0 1) ∧
    DifferentiableOn ℂ (fun z : ℂ => ∑' k, (f k : ℂ) * z ^ k)
      (Metric.ball 0 1) ∧
    (∑' k, (f k : ℂ) * (1 : ℂ) ^ k) = 1 := by
  exact ⟨fun _ hz => hasSum_weighted_pow hf hs.summable hz,
    tendstoUniformlyOn_sum_weighted_pow hf hs.summable,
    continuousOn_tsum_weighted_pow hf hs.summable,
    differentiableOn_tsum_weighted_pow hf hs.summable,
    by simpa only [Complex.ofReal_one] using tsum_weighted_pow_one hs⟩

end DirectedDistances.Tauberian
