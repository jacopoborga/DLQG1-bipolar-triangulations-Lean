/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.ProbabilityGeneratingFunction
public import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Algebra.Ring.GeomSum








public section
namespace DirectedDistances.Tauberian

open scoped Topology
open Filter

/-- The finite geometric polynomial obeys the first-moment bound throughout
the closed disk, including degree zero and the boundary point one. -/
theorem norm_weighted_geom_sum_le {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {z : ℂ} (hz : ‖z‖ ≤ 1) (n : ℕ) :
    ‖(f n : ℂ) * (∑ k ∈ Finset.range n, z ^ k)‖ ≤ (n : ℝ) * f n := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf n)]
  have hgeom : ‖∑ k ∈ Finset.range n, z ^ k‖ ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, ‖z ^ k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun k _ => by
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg z) hz
      _ = (n : ℝ) := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  exact (mul_le_mul_of_nonneg_left hgeom (hf n)).trans_eq (mul_comm _ _)

/-- The divided-difference generating series has its actual sum everywhere
on the closed unit disk under exactly a finite first-moment condition. -/
theorem hasSum_weighted_geom_sum {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hm : Summable (fun (n : ℕ) => (n : ℝ) * f n)) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun n => (f n : ℂ) * (∑ k ∈ Finset.range n, z ^ k))
      (∑' n, (f n : ℂ) * (∑ k ∈ Finset.range n, z ^ k)) :=
  (hm.of_norm_bounded (norm_weighted_geom_sum_le hf hz)).hasSum

/-- First-moment domination yields uniform convergence of the geometric
polynomial series on the closed disk. -/
theorem tendstoUniformlyOn_sum_weighted_geom_sum {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hm : Summable (fun (n : ℕ) => (n : ℝ) * f n)) :
    TendstoUniformlyOn
      (fun (N : ℕ) (z : ℂ) => ∑ n ∈ Finset.range N,
        (f n : ℂ) * (∑ k ∈ Finset.range n, z ^ k))
      (fun z : ℂ => ∑' n, (f n : ℂ) * (∑ k ∈ Finset.range n, z ^ k))
      atTop (Metric.closedBall 0 1) := by
  apply tendstoUniformlyOn_tsum_nat hm
  intro n z hz
  exact norm_weighted_geom_sum_le hf
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz) n

/-- The geometric polynomial series is continuous on the entire closed disk. -/
theorem continuousOn_tsum_weighted_geom_sum {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hm : Summable (fun (n : ℕ) => (n : ℝ) * f n)) :
    ContinuousOn
      (fun z : ℂ => ∑' n, (f n : ℂ) * (∑ k ∈ Finset.range n, z ^ k))
      (Metric.closedBall 0 1) := by
  apply continuousOn_tsum
    (f := fun (n : ℕ) (z : ℂ) => (f n : ℂ) * (∑ k ∈ Finset.range n, z ^ k))
    (fun n => (continuous_const.mul
      (continuous_finsetSum _ (fun k _ => continuous_id.pow k))).continuousOn) hm
  intro n z hz
  exact norm_weighted_geom_sum_le hf
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz) n

/-- The geometric polynomial series is holomorphic in the open disk. -/
theorem differentiableOn_tsum_weighted_geom_sum {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hm : Summable (fun (n : ℕ) => (n : ℝ) * f n)) :
    DifferentiableOn ℂ
      (fun z : ℂ => ∑' n, (f n : ℂ) * (∑ k ∈ Finset.range n, z ^ k))
      (Metric.ball 0 1) := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    (F := fun (n : ℕ) (z : ℂ) => (f n : ℂ) * (∑ k ∈ Finset.range n, z ^ k)) hm
    (fun n => ((differentiable_const (f n : ℂ)).mul
      (Differentiable.fun_sum (fun k _ => differentiable_id.pow k))).differentiableOn)
    Metric.isOpen_ball
  intro n z hz
  exact norm_weighted_geom_sum_le hf
    (le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hz)) n

/-- The geometric polynomial series at one equals the actual first moment. -/
theorem tsum_weighted_geom_sum_one {f : ℕ → ℝ}
    (hm : Summable (fun (n : ℕ) => (n : ℝ) * f n)) :
    (∑' n, (f n : ℂ) * (∑ k ∈ Finset.range n, (1 : ℂ) ^ k)) =
      ((∑' (n : ℕ), (n : ℝ) * f n : ℝ) : ℂ) := by
  have h := (Complex.hasSum_ofReal.mpr hm.hasSum).tsum_eq
  simpa only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    Complex.ofReal_mul, Complex.ofReal_natCast, mul_comm] using h

/-- The convergent geometric series is exactly the divided difference before
any division, including at the endpoint one. -/
theorem tsum_weighted_pow_sub_one_eq {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hs : HasSum f 1)
    (hm : Summable (fun (n : ℕ) => (n : ℝ) * f n)) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (∑' n, (f n : ℂ) * z ^ n) - 1 =
      (z - 1) * (∑' n, (f n : ℂ) * (∑ k ∈ Finset.range n, z ^ k)) := by
  have hleft := (hasSum_weighted_pow hf hs.summable hz).sub
    (Complex.hasSum_ofReal.mpr hs)
  have hright := (hasSum_weighted_geom_sum hf hm hz).mul_left (z - 1)
  apply hleft.unique
  apply hright.congr_fun
  intro n
  symm
  calc
    (z - 1) * ((f n : ℂ) * (∑ k ∈ Finset.range n, z ^ k)) =
        (f n : ℂ) * ((z - 1) * (∑ k ∈ Finset.range n, z ^ k)) := by ring
    _ = (f n : ℂ) * z ^ n - (f n : ℂ) := by rw [mul_geom_sum]; ring

/-- The boundary complex derivative is the actual first moment, with approach
restricted to the closed unit disk. -/
theorem hasDerivWithinAt_tsum_weighted_pow_one {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hs : HasSum f 1)
    (hm : Summable (fun (n : ℕ) => (n : ℝ) * f n)) :
    HasDerivWithinAt (fun z : ℂ => ∑' n, (f n : ℂ) * z ^ n)
      ((∑' (n : ℕ), (n : ℝ) * f n : ℝ) : ℂ) (Metric.closedBall 0 1) 1 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hcont := (continuousOn_tsum_weighted_geom_sum hf hm) 1
    (by simp only [Metric.mem_closedBall, dist_zero_right, norm_one, le_refl])
  have ht := hcont.tendsto.mono_left (nhdsWithin_mono 1 (Set.sdiff_subset (t := {1})))
  rw [tsum_weighted_geom_sum_one hm] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hnorm : ‖z‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1
  have hne : z - 1 ≠ 0 := sub_ne_zero.mpr (by simpa only [Set.mem_singleton_iff] using hz.2)
  rw [slope_def_field, tsum_weighted_pow_one hs, Complex.ofReal_one,
    tsum_weighted_pow_sub_one_eq hf hs hm hnorm, mul_div_cancel_left₀ _ hne]

/-- Dividing the geometric series by its nonzero actual first moment gives
the continuous holomorphic extension of the manuscript normalized quotient.
The quotient identity is asserted away from one; the extension has value one. -/
theorem normalized_geom_series_properties {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hs : HasSum f 1)
    (hm : Summable (fun (n : ℕ) => (n : ℝ) * f n))
    (hm0 : (∑' (n : ℕ), (n : ℝ) * f n) ≠ 0) :
    ContinuousOn
      (fun z : ℂ => (∑' n, (f n : ℂ) * (∑ k ∈ Finset.range n, z ^ k)) /
        ((∑' (n : ℕ), (n : ℝ) * f n : ℝ) : ℂ)) (Metric.closedBall 0 1) ∧
    DifferentiableOn ℂ
      (fun z : ℂ => (∑' n, (f n : ℂ) * (∑ k ∈ Finset.range n, z ^ k)) /
        ((∑' (n : ℕ), (n : ℝ) * f n : ℝ) : ℂ)) (Metric.ball 0 1) ∧
    (∑' n, (f n : ℂ) * (∑ k ∈ Finset.range n, (1 : ℂ) ^ k)) /
      ((∑' (n : ℕ), (n : ℝ) * f n : ℝ) : ℂ) = 1 ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 →
      (∑' n, (f n : ℂ) * (∑ k ∈ Finset.range n, z ^ k)) /
        ((∑' (n : ℕ), (n : ℝ) * f n : ℝ) : ℂ) =
      ((∑' n, (f n : ℂ) * z ^ n) - 1) /
        (((∑' (n : ℕ), (n : ℝ) * f n : ℝ) : ℂ) * (z - 1))) := by
  have hmC : ((∑' (n : ℕ), (n : ℝ) * f n : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hm0
  refine ⟨(continuousOn_tsum_weighted_geom_sum hf hm).div_const _,
    (differentiableOn_tsum_weighted_geom_sum hf hm).div_const _, ?_, ?_⟩
  · rw [tsum_weighted_geom_sum_one hm, div_self hmC]
  · intro z hz hne
    rw [tsum_weighted_pow_sub_one_eq hf hs hm hz]
    field_simp [hmC, sub_ne_zero.mpr hne]

end DirectedDistances.Tauberian
