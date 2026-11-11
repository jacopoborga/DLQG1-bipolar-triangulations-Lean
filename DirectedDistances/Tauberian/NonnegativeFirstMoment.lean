/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.RealDeriv

/-! Supporting lemmas for paper labels `lem-tauberian`, `lem-tauberian'` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.Tauberian

open Set MeasureTheory Filter
open scoped Topology Interval

/-- The sine primitive at frequency zero is handled separately; positive
integer frequencies have their actual cosine primitive. -/
theorem integral_sin_nat_mul (k : ℕ) (t : ℝ) :
    (∫ s : ℝ in (0 : ℝ)..t, Real.sin ((k : ℝ) * s)) =
      (1 - Real.cos ((k : ℝ) * t)) / (k : ℝ) := by
  by_cases hk : k = 0
  · simp only [hk, Nat.cast_zero, zero_mul, Real.sin_zero, intervalIntegral.integral_zero,
      Real.cos_zero, sub_self, div_zero]
  · have h := intervalIntegral.mul_integral_comp_mul_left (f := Real.sin)
      (a := (0 : ℝ)) (b := t) (c := (k : ℝ))
    rw [mul_zero, integral_sin, Real.cos_zero] at h
    apply (eq_div_iff (Nat.cast_ne_zero.2 hk)).2
    simpa only [mul_comm] using h

/-- The normalized primitive is a squared sinc expression. This gives its
nonnegativity and small-parameter limit without assuming a moment. -/
theorem integral_sin_nat_mul_div_sq (k : ℕ) {t : ℝ} (ht : t ≠ 0) :
    (∫ s : ℝ in (0 : ℝ)..t, Real.sin ((k : ℝ) * s)) / t ^ 2 =
      (k : ℝ) / 2 * (Real.sinc ((k : ℝ) * t / 2)) ^ 2 := by
  by_cases hk : k = 0
  · simp only [hk, Nat.cast_zero, zero_mul, Real.sin_zero, intervalIntegral.integral_zero,
      zero_div]
  · have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
    rw [integral_sin_nat_mul, Real.sinc_of_ne_zero
      (div_ne_zero (mul_ne_zero hk' ht) (by norm_num))]
    have hcos := Real.cos_two_mul ((k : ℝ) * t / 2)
    have htrig := Real.sin_sq_add_cos_sq ((k : ℝ) * t / 2)
    have he : 2 * ((k : ℝ) * t / 2) = (k : ℝ) * t := by ring
    rw [he] at hcos
    have hhalf : 1 - Real.cos ((k : ℝ) * t) =
        2 * Real.sin ((k : ℝ) * t / 2) ^ 2 := by nlinarith only [hcos, htrig]
    rw [hhalf]
    field_simp

/-- Each normalized integrated sine term has the expected half-frequency limit. -/
theorem tendsto_integral_sin_nat_mul_div_sq (k : ℕ) :
    Tendsto (fun t : ℝ =>
      (∫ s : ℝ in (0 : ℝ)..t, Real.sin ((k : ℝ) * s)) / t ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 ((k : ℝ) / 2)) := by
  have hc : Continuous (fun t : ℝ =>
      (k : ℝ) / 2 * (Real.sinc ((k : ℝ) * t / 2)) ^ 2) := by fun_prop
  have hh : Tendsto (fun t : ℝ =>
      (k : ℝ) / 2 * (Real.sinc ((k : ℝ) * t / 2)) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 ((k : ℝ) / 2)) := by
    simpa only [mul_zero, zero_div, Real.sinc_zero, one_pow, mul_one] using
      (hc.tendsto 0).mono_left (y := 𝓝[>] (0 : ℝ)) nhdsWithin_le_nhds
  apply hh.congr'
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  exact (integral_sin_nat_mul_div_sq k (show 0 < t from ht).ne').symm

/-- Uniformly summable nonnegative weights give a continuous sine transform. -/
theorem continuous_nonnegative_sine_transform (f : ℕ → ℝ) (hf : Summable f)
    (hn : ∀ k, 0 ≤ f k) :
    Continuous (fun t : ℝ => ∑' k, f k * Real.sin ((k : ℝ) * t)) := by
  apply continuous_tsum (fun k => by fun_prop) hf
  intro k t
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hn k), Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (hn k)).trans_eq (mul_one _)

/-- The integral norm bound needed for actual termwise integration depends
only on the total probability weights, not on their first moment. -/
theorem integral_norm_weight_sin_le {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (k : ℕ) :
    (∫ s : ℝ in Ioc 0 t, ‖a * Real.sin ((k : ℝ) * s)‖) ≤ t * a := by
  rw [← intervalIntegral.integral_of_le ht]
  calc
    (∫ s : ℝ in (0 : ℝ)..t, ‖a * Real.sin ((k : ℝ) * s)‖) ≤
        ∫ s : ℝ in (0 : ℝ)..t, a := by
      apply intervalIntegral.integral_mono_on ht
        ((continuous_const.mul (Real.continuous_sin.comp
          (continuous_const.mul continuous_id))).norm.intervalIntegrable _ _)
        intervalIntegrable_const
      intro s _
      change ‖a * Real.sin ((k : ℝ) * s)‖ ≤ a
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ha, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) ha).trans_eq (mul_one _)
    _ = t * a := by rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]

/-- The sine transform may be integrated term by term because its weights
are summable; no moment hypothesis is consumed. -/
theorem hasSum_integrated_nonnegative_sine_transform (f : ℕ → ℝ) (hf : Summable f)
    (hn : ∀ k, 0 ≤ f k) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun k : ℕ => f k * (∫ s : ℝ in (0 : ℝ)..t, Real.sin ((k : ℝ) * s)))
      (∫ s : ℝ in (0 : ℝ)..t, ∑' k, f k * Real.sin ((k : ℝ) * s)) := by
  have hi : ∀ k : ℕ, IntegrableOn (fun s : ℝ => f k * Real.sin ((k : ℝ) * s)) (Ioc 0 t) := by
    intro k
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1
    exact (continuous_const.mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hs : Summable (fun k : ℕ =>
      ∫ s : ℝ in Ioc 0 t, ‖f k * Real.sin ((k : ℝ) * s)‖) := by
    apply (hf.mul_left t).of_nonneg_of_le
      (fun k => integral_nonneg (fun _ => norm_nonneg _))
    exact fun k => integral_norm_weight_sin_le (hn k) ht k
  have hh := hasSum_integral_of_summable_integral_norm hi hs
  have hh' : HasSum
      (fun k : ℕ => ∫ s : ℝ in (0 : ℝ)..t, f k * Real.sin ((k : ℝ) * s))
      (∫ s : ℝ in (0 : ℝ)..t, ∑' k, f k * Real.sin ((k : ℝ) * s)) := by
    simpa only [intervalIntegral.integral_of_le ht] using hh
  simpa only [intervalIntegral.integral_const_mul] using hh'

/-- Every integrated sine term is nonnegative for a nonnegative frequency;
this is the positivity that makes the derivative converse possible. -/
theorem integral_sin_nat_mul_nonneg (k : ℕ) (t : ℝ) :
    0 ≤ ∫ s : ℝ in (0 : ℝ)..t, Real.sin ((k : ℝ) * s) := by
  rw [integral_sin_nat_mul]
  exact div_nonneg (sub_nonneg.2 (Real.cos_le_one _)) (Nat.cast_nonneg _)

/-- A local linear upper bound on the sine transform forces first-moment
summability, by nonnegative integrated terms and finite partial-sum limits. -/
theorem summable_first_moment_of_local_sine_bound (f : ℕ → ℝ) (hf : Summable f)
    (hn : ∀ k, 0 ≤ f k) {M δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ s ∈ Icc (0 : ℝ) δ,
      (∑' k, f k * Real.sin ((k : ℝ) * s)) ≤ M * s) :
    Summable (fun k : ℕ => (k : ℝ) * f k) := by
  apply summable_of_sum_range_le (fun k => mul_nonneg (Nat.cast_nonneg k) (hn k))
  intro N
  have hlim : Tendsto (fun t : ℝ => ∑ k ∈ Finset.range N,
      f k * ((∫ s : ℝ in (0 : ℝ)..t, Real.sin ((k : ℝ) * s)) / t ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (∑ k ∈ Finset.range N, f k * ((k : ℝ) / 2))) := by
    apply tendsto_finsetSum
    intro k _
    exact (tendsto_integral_sin_nat_mul_div_sq k).const_mul (f k)
  have hle : (∑ k ∈ Finset.range N, f k * ((k : ℝ) / 2)) ≤ M / 2 := by
    apply le_of_tendsto hlim
    filter_upwards [eventually_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htδ
    have ht0 : 0 < t := ht
    have hs := hasSum_integrated_nonnegative_sine_transform f hf hn ht0.le
    have hp : (∑ k ∈ Finset.range N,
        f k * (∫ s : ℝ in (0 : ℝ)..t, Real.sin ((k : ℝ) * s))) ≤
        ∫ s : ℝ in (0 : ℝ)..t, ∑' k, f k * Real.sin ((k : ℝ) * s) := by
      rw [← hs.tsum_eq]
      exact hs.summable.sum_le_tsum _
        (fun k _ => mul_nonneg (hn k) (integral_sin_nat_mul_nonneg k t))
    have hi : (∫ s : ℝ in (0 : ℝ)..t, ∑' k, f k * Real.sin ((k : ℝ) * s)) ≤
        M * t ^ 2 / 2 := by
      calc
        _ ≤ ∫ s : ℝ in (0 : ℝ)..t, M * s := by
          apply intervalIntegral.integral_mono_on ht0.le
            ((continuous_nonnegative_sine_transform f hf hn).intervalIntegrable _ _)
            ((continuous_const.mul continuous_id).intervalIntegrable _ _)
          intro s hs
          exact hbound s ⟨hs.1, hs.2.trans htδ.le⟩
        _ = M * t ^ 2 / 2 := by
          rw [intervalIntegral.integral_const_mul, integral_id]
          ring
    have he : (∑ k ∈ Finset.range N,
        f k * ((∫ s : ℝ in (0 : ℝ)..t, Real.sin ((k : ℝ) * s)) / t ^ 2)) =
        (∑ k ∈ Finset.range N,
          f k * (∫ s : ℝ in (0 : ℝ)..t, Real.sin ((k : ℝ) * s))) / t ^ 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [he]
    apply (div_le_iff₀ (sq_pos_of_pos ht0)).2
    linarith only [hp, hi]
  have he : (∑ k ∈ Finset.range N, f k * ((k : ℝ) / 2)) =
      (∑ k ∈ Finset.range N, (k : ℝ) * f k) / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he] at hle
  linarith only [hle]

/-- Once the moment is proved summable, dominated convergence identifies the
sine difference quotient with the genuine first-moment sum. -/
theorem tendsto_sine_transform_div_first_moment (f : ℕ → ℝ)
    (hn : ∀ k, 0 ≤ f k) (hm : Summable (fun k : ℕ => (k : ℝ) * f k)) :
    Tendsto (fun t : ℝ => (∑' k, f k * Real.sin ((k : ℝ) * t)) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (∑' k : ℕ, (k : ℝ) * f k)) := by
  have hterm (k : ℕ) : Tendsto (fun t : ℝ => f k * Real.sin ((k : ℝ) * t) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 ((k : ℝ) * f k)) := by
    have hd : HasDerivAt (fun t : ℝ => Real.sin ((k : ℝ) * t)) (k : ℝ) 0 := by
      simpa only [id_eq, mul_zero, Real.cos_zero, one_mul, mul_one] using
        (((hasDerivAt_id (0 : ℝ)).const_mul (k : ℝ)).sin)
    simpa only [zero_add, mul_zero, Real.sin_zero, sub_zero, smul_eq_mul,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hd.tendsto_slope_zero_right.const_mul (f k)
  have hdom : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      ∀ k : ℕ, ‖f k * Real.sin ((k : ℝ) * t) / t‖ ≤ (k : ℝ) * f k := by
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    intro k
    have ht0 : 0 < t := ht
    rw [norm_div, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hn k), Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos ht0]
    apply (div_le_iff₀ ht0).2
    have hs := Real.abs_sin_le_abs (x := (k : ℝ) * t)
    rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg k) ht0.le)] at hs
    exact (mul_le_mul_of_nonneg_left hs (hn k)).trans_eq (by ring)
  have hh := tendsto_tsum_of_dominated_convergence hm hterm hdom
  simpa only [tsum_div_const] using hh

/-- A derivative of the sine transform forces first-moment existence and
identifies its value; finiteness is a conclusion, not an assumption. -/
theorem first_moment_of_sine_transform_derivative (f : ℕ → ℝ) (hf : Summable f)
    (hn : ∀ k, 0 ≤ f k) {c₁ : ℝ}
    (hd : HasDerivAt (fun t : ℝ => ∑' k, f k * Real.sin ((k : ℝ) * t)) c₁ 0) :
    Summable (fun k : ℕ => (k : ℝ) * f k) ∧ (∑' k : ℕ, (k : ℝ) * f k) = c₁ := by
  have hzero : (∑' k, f k * Real.sin ((k : ℝ) * (0 : ℝ))) = 0 := by simp
  have hbig := hd.isBigO_sub
  simp only [hzero, sub_zero] at hbig
  obtain ⟨M, _hM, hMbound⟩ := Asymptotics.isBigO_iff'.1 hbig
  obtain ⟨δ, hδ, hsmall⟩ := Metric.mem_nhds_iff.1 hMbound
  have hm : Summable (fun k : ℕ => (k : ℝ) * f k) := by
    apply summable_first_moment_of_local_sine_bound f hf hn (half_pos hδ)
    intro s hs
    have hdist : dist s 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
      linarith only [hs.2, hδ]
    have hh := hsmall hdist
    change ‖∑' k, f k * Real.sin ((k : ℝ) * s)‖ ≤ M * ‖s‖ at hh
    calc
      (∑' k, f k * Real.sin ((k : ℝ) * s)) ≤
          |∑' k, f k * Real.sin ((k : ℝ) * s)| := le_abs_self _
      _ ≤ M * s := by simpa only [Real.norm_eq_abs, abs_of_nonneg hs.1] using hh
  refine ⟨hm, ?_⟩
  have hquot : Tendsto (fun t : ℝ => (∑' k, f k * Real.sin ((k : ℝ) * t)) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 c₁) := by
    simpa only [zero_add, hzero, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hd.tendsto_slope_zero_right
  exact tendsto_nhds_unique (tendsto_sine_transform_div_first_moment f hn hm) hquot

/-- For a nonnegative integer law, the characteristic-function derivative at
zero forces a genuine finite first moment with the indicated value. This is
the derivative-to-moment input required in revised A.3. -/
theorem first_moment_of_characteristic_derivative (f : ℕ → ℝ)
    (hn : ∀ k, 0 ≤ f k) (hsum : HasSum f 1) {c₁ : ℝ}
    (hd : HasDerivAt (fun t : ℝ => ∑' k,
      (f k : ℂ) * Complex.exp ((((t * (k : ℝ) : ℝ)) : ℂ) * Complex.I))
      ((c₁ : ℂ) * Complex.I) 0) :
    Summable (fun k : ℕ => (k : ℝ) * f k) ∧ (∑' k : ℕ, (k : ℝ) * f k) = c₁ := by
  have hf := hsum.summable
  have hs (t : ℝ) : Summable (fun k : ℕ =>
      (f k : ℂ) * Complex.exp ((((t * (k : ℝ) : ℝ)) : ℂ) * Complex.I)) := by
    apply hf.of_norm_bounded
    intro k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hn k),
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have him (t : ℝ) : (∑' k,
      (f k : ℂ) * Complex.exp ((((t * (k : ℝ) : ℝ)) : ℂ) * Complex.I)).im =
        ∑' k, f k * Real.sin ((k : ℝ) * t) := by
    rw [Complex.im_tsum (hs t)]
    apply tsum_congr
    intro k
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.exp_im]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_add, mul_one,
      Real.exp_zero, one_mul, mul_comm]
  have himfun : (fun t : ℝ => (∑' k,
      (f k : ℂ) * Complex.exp ((((t * (k : ℝ) : ℝ)) : ℂ) * Complex.I)).im) =
        (fun t : ℝ => ∑' k, f k * Real.sin ((k : ℝ) * t)) := funext him
  have hdIm : HasDerivAt (fun t : ℝ => (∑' k,
      (f k : ℂ) * Complex.exp ((((t * (k : ℝ) : ℝ)) : ℂ) * Complex.I)).im) c₁ 0 := by
    simpa only [Function.comp_def, Complex.imCLM_apply, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, add_zero] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hd
  rw [himfun] at hdIm
  exact first_moment_of_sine_transform_derivative f hf hn hdIm

end DirectedDistances.Tauberian
