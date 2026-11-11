/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Poisson
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import DirectedDistances.Tauberian.PoissonCircleBarrier
import DirectedDistances.Tauberian.PoissonNormBound
import DirectedDistances.Tauberian.ScaledPowerError

/-! Supporting lemmas for paper labels `lem-holo-asymp` (see CORRESPONDENCE.md). -/









public section
namespace DirectedDistances.Tauberian

open Complex Metric Set MeasureTheory Filter
open scoped Topology ComplexConjugate

/-- The fractional-power model meets the source's precise disk regularity,
including continuity at its boundary zero. -/
theorem diffContOnCl_one_sub_cpow {ν : ℝ} (hν : 0 < ν) :
    DiffContOnCl ℂ (fun z : ℂ => (1 - z) ^ (ν : ℂ)) (ball (0 : ℂ) 1) := by
  constructor
  · intro z hz
    have hz' : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
    have hr : 0 < (1 - z).re := by
      rw [sub_re, one_re]
      exact sub_pos.2 ((re_le_norm z).trans_lt hz')
    exact (((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).cpow_const
      (mem_slitPlane_iff.2 (Or.inl hr))).differentiableWithinAt
  · rw [closure_ball (0 : ℂ) zero_lt_one.ne']
    intro z hz
    have hz' : ‖z‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hz
    have hr : 0 ≤ (1 - z).re := by
      rw [sub_re, one_re]
      exact sub_nonneg.2 ((re_le_norm z).trans hz')
    exact ((continuousAt_cpow_const_of_re_pos (Or.inl hr)
      (by simpa only [ofReal_re] using hν)).comp
        (continuous_const.sub continuous_id).continuousAt).continuousWithinAt

/-- Positive real dilation commutes with a positive real complex power,
including a zero complex argument. -/
theorem cpow_mul_ofReal_pos {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (z : ℂ) :
    (z * (t : ℂ)) ^ (ν : ℂ) = z ^ (ν : ℂ) * ((t ^ ν : ℝ) : ℂ) := by
  have hνne : (ν : ℂ) ≠ 0 := ofReal_ne_zero.2 hν.ne'
  by_cases hz : z = 0
  · simp only [hz, zero_mul, zero_cpow hνne]
  rw [ofReal_cpow ht.le, cpow_def_of_ne_zero
    (mul_ne_zero hz (ofReal_ne_zero.2 ht.ne')), log_mul_ofReal t ht z hz,
    cpow_def_of_ne_zero hz, cpow_def_of_ne_zero (ofReal_ne_zero.2 ht.ne'),
    ← ofReal_log ht.le, add_mul, exp_add]
  ring

/-- The first-order boundary parametrization has the correct complex phase. -/
theorem tendsto_one_sub_exp_div_pos :
    Tendsto (fun t : ℝ => (1 - Complex.exp ((t : ℂ) * I)) / (t : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (-I)) := by
  have hdC : HasDerivAt (fun z : ℂ => 1 - Complex.exp (z * I)) (-I) 0 := by
    simpa only [id_eq, zero_mul, exp_zero, one_mul, mul_one] using
      ((((hasDerivAt_id (0 : ℂ)).mul_const I).cexp).const_sub 1)
  have hd := hdC.comp_ofReal
  have ht := hd.tendsto_slope_zero_right
  simpa only [zero_add, ofReal_zero, zero_mul, mul_zero, exp_zero, sub_self, sub_zero,
    Complex.real_smul, ofReal_inv, div_eq_mul_inv, mul_comm] using ht

/-- The boundary fractional-power model, normalized at positive angles. -/
theorem tendsto_one_sub_exp_cpow_div_pos {ν : ℝ} (hν : 0 < ν) :
    Tendsto (fun t : ℝ => (1 - Complex.exp ((t : ℂ) * I)) ^ (ν : ℂ) /
      ((t ^ ν : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 ((-I) ^ (ν : ℂ))) := by
  have hh := tendsto_one_sub_exp_div_pos.cpow (tendsto_const_nhds (x := (ν : ℂ)))
    (mem_slitPlane_iff.2 (Or.inr (by simp)))
  apply hh.congr'
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  have he := cpow_mul_ofReal_pos hν (inv_pos.2 ht)
    (1 - Complex.exp ((t : ℂ) * I))
  rw [div_eq_mul_inv, ← ofReal_inv, he, Real.inv_rpow ht.le,
    ofReal_inv, div_eq_mul_inv]

/-- The disk Poisson kernel is unchanged by conjugating the circle argument
when the pole lies on the real axis. -/
theorem poissonKernel_conj_real (w : ℝ) (z : ℂ) :
    poissonKernel 0 (w : ℂ) (conj z) = poissonKernel 0 (w : ℂ) z := by
  simp only [poissonKernel_def, sub_zero, norm_conj]
  have hh : conj z - (w : ℂ) = conj (z - (w : ℂ)) := by simp
  rw [hh, norm_conj]

/-- Symmetrizing boundary values about the real axis doubles the Poisson
integral at a real interior point. No representation hypothesis is assumed. -/
theorem circleAverage_poisson_even {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball (0 : ℂ) 1)) {w : ℝ} (hw : |w| < 1) :
    Real.circleAverage (fun z : ℂ =>
      poissonKernel 0 (w : ℂ) z • (f z + f (conj z))) 0 1 = 2 • f (w : ℂ) := by
  have hwball : (w : ℂ) ∈ ball (0 : ℂ) 1 := by
    simpa only [mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs] using hw
  have hwnot : (w : ℂ) ∉ sphere (0 : ℂ) |(1 : ℝ)| := by
    simpa only [abs_one, mem_sphere, dist_zero_right, norm_real, Real.norm_eq_abs] using
      ne_of_lt hw
  have hfc : ContinuousOn f (sphere (0 : ℂ) 1) := by
    apply hf.continuousOn.mono
    rw [closure_ball (0 : ℂ) zero_lt_one.ne']
    exact sphere_subset_closedBall
  have hfcc : ContinuousOn (fun z : ℂ => f (conj z)) (sphere (0 : ℂ) 1) := by
    apply hfc.comp continuous_conj.continuousOn
    intro z hz
    simpa only [mem_sphere, dist_zero_right, norm_conj] using hz
  have hkc : ContinuousOn (poissonKernel 0 (w : ℂ)) (sphere (0 : ℂ) 1) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    apply Complex.continuous_re.comp_continuousOn
    simpa only [abs_one] using continuousOn_herglotzRieszKernel_sphere hwnot
  have hi : CircleIntegrable (fun z => poissonKernel 0 (w : ℂ) z • f z) 0 1 :=
    (hkc.smul hfc).circleIntegrable (zero_le_one : (0 : ℝ) ≤ 1)
  have hic : CircleIntegrable (fun z => poissonKernel 0 (w : ℂ) z • f (conj z)) 0 1 :=
    (hkc.smul hfcc).circleIntegrable (zero_le_one : (0 : ℝ) ≤ 1)
  have hs : Real.circleAverage (fun z : ℂ => poissonKernel 0 (w : ℂ) z • f (conj z)) 0 1 =
      Real.circleAverage (fun z : ℂ => poissonKernel 0 (w : ℂ) z • f z) 0 1 := by
    calc
      _ = Real.circleAverage (fun z : ℂ =>
          poissonKernel 0 (w : ℂ) z⁻¹ • f z⁻¹) 0 1 := by
        apply Real.circleAverage_congr_sphere
        intro z hz
        dsimp only
        have hzn : ‖z‖ = 1 := by simpa only [abs_one, mem_sphere, dist_zero_right] using hz
        rw [inv_eq_conj hzn, poissonKernel_conj_real]
      _ = _ := Real.circleAverage_zero_one_congr_inv
        (f := fun z : ℂ => poissonKernel 0 (w : ℂ) z • f z)
  simp_rw [smul_add]
  have hp : Real.circleAverage (fun z => poissonKernel 0 (w : ℂ) z • f z) 0 1 = f (w : ℂ) :=
    hf.circleAverage_poissonKernel_smul hwball
  rw [Real.circleAverage_fun_add hi hic, hs, hp]
  exact (two_smul ℕ (f (w : ℂ))).symm

/-- The model phase has precisely the cosine factor occurring in A.1. -/
theorem re_neg_I_cpow_real (ν : ℝ) :
    ((-I) ^ (ν : ℂ)).re = Real.cos (Real.pi * ν / 2) := by
  rw [cpow_ofReal_re, norm_neg, norm_I, Real.one_rpow, one_mul, arg_neg_I]
  have he : -(Real.pi / 2) * ν = -(Real.pi * ν / 2) := by ring
  rw [he, Real.cos_neg]

/-- Normalized real boundary values of the exact analytic model tend to the
strictly positive cosine coefficient. -/
theorem tendsto_re_one_sub_exp_cpow_div_pos {ν : ℝ} (hν : 0 < ν) :
    Tendsto (fun t : ℝ => ((1 - Complex.exp ((t : ℂ) * I)) ^ (ν : ℂ)).re /
      t ^ ν) (𝓝[>] (0 : ℝ)) (𝓝 (Real.cos (Real.pi * ν / 2))) := by
  have hh := Complex.continuous_re.tendsto _ |>.comp (tendsto_one_sub_exp_cpow_div_pos hν)
  simpa only [Function.comp_def, div_ofReal_re, re_neg_I_cpow_real] using hh

/-- The real part of the fractional-power model is nonnegative on the full
closed unit disk, so it is a legitimate Poisson majorant. -/
theorem re_one_sub_cpow_nonneg {ν : ℝ} (hν₀ : 0 < ν) (hν₁ : ν < 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : 0 ≤ ((1 - z) ^ (ν : ℂ)).re := by
  have hr : 0 ≤ (1 - z).re := by
    rw [sub_re, one_re]
    exact sub_nonneg.2 ((re_le_norm z).trans hz)
  have ha := abs_arg_le_pi_div_two_iff.2 hr
  have hangle : |arg (1 - z) * ν| < Real.pi / 2 := by
    calc
      |arg (1 - z) * ν| = |arg (1 - z)| * ν := by rw [abs_mul, abs_of_pos hν₀]
      _ ≤ (Real.pi / 2) * ν := mul_le_mul_of_nonneg_right ha hν₀.le
      _ < Real.pi / 2 := by nlinarith only [hν₁, Real.pi_pos]
  rw [cpow_ofReal_re]
  exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
    (Real.cos_pos_of_mem_Ioo (abs_lt.1 hangle)).le

/-- Taking real parts commutes with the actual Poisson representation. -/
theorem circleAverage_poisson_re {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball (0 : ℂ) 1)) {w : ℝ} (hw : |w| < 1) :
    Real.circleAverage (fun z : ℂ => poissonKernel 0 (w : ℂ) z * (f z).re) 0 1 =
      (f (w : ℂ)).re := by
  have hwball : (w : ℂ) ∈ ball (0 : ℂ) 1 := by
    simpa only [mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs] using hw
  have hwnot : (w : ℂ) ∉ sphere (0 : ℂ) |(1 : ℝ)| := by
    simpa only [abs_one, mem_sphere, dist_zero_right, norm_real, Real.norm_eq_abs] using
      ne_of_lt hw
  have hfc : ContinuousOn f (sphere (0 : ℂ) 1) := by
    apply hf.continuousOn.mono
    rw [closure_ball (0 : ℂ) zero_lt_one.ne']
    exact sphere_subset_closedBall
  have hkc : ContinuousOn (poissonKernel 0 (w : ℂ)) (sphere (0 : ℂ) 1) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact Complex.continuous_re.comp_continuousOn
      (by simpa only [abs_one] using continuousOn_herglotzRieszKernel_sphere hwnot)
  have hi := (hkc.smul hfc).circleIntegrable (zero_le_one : (0 : ℝ) ≤ 1)
  have hh := Complex.reCLM.circleAverage_comp_comm hi
  rw [hf.circleAverage_poissonKernel_smul hwball] at hh
  simpa only [Function.comp_def, reCLM_apply, Pi.smul_apply', Complex.real_smul,
    re_ofReal_mul] using hh

/-- The source's two-sided little-o premise supplies both normalized boundary
limits with the same complex coefficient and its conjugate. -/
theorem boundary_quotients_of_isLittleO {ψ : ℂ → ℂ} {c : ℂ} {ν : ℝ}
    (hb : (fun t : ℝ => ψ (Complex.exp ((t : ℂ) * I)) - 1 -
      (if 0 < t then c else conj c) * (((|t| : ℝ) ^ ν : ℝ) : ℂ))
        =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν)) :
    Tendsto (fun t : ℝ => (ψ (Complex.exp ((t : ℂ) * I)) - 1) /
      ((t ^ ν : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 c) ∧
    Tendsto (fun t : ℝ => (ψ (Complex.exp (((-t : ℝ) : ℂ) * I)) - 1) /
      ((t ^ ν : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (conj c)) := by
  have he := hb.tendsto_inv_smul_nhds_zero
  constructor
  · have hh := (he.mono_left (nhdsGT_le_nhdsNE (0 : ℝ))).add_const c
    simp only [zero_add] at hh
    apply hh.congr'
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    rw [abs_of_pos ht, ite_eq_left (show 0 < t from ht), Complex.real_smul, ofReal_inv]
    have hd : (((t ^ ν : ℝ)) : ℂ) ≠ 0 :=
      ofReal_ne_zero.2 (Real.rpow_pos_of_pos ht ν).ne'
    field_simp
    ring
  · have hn : Tendsto (fun t : ℝ => -t) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_iff.2
      constructor
      · simpa only [neg_zero] using
          ((continuous_neg.tendsto (0 : ℝ)).mono_left (y := 𝓝[>] (0 : ℝ)) nhdsWithin_le_nhds)
      · filter_upwards [eventually_mem_nhdsWithin] with t ht
        simpa only [mem_compl_iff, mem_singleton_iff, neg_eq_zero] using ht.ne'
    have hh := (he.comp hn).add_const (conj c)
    simp only [zero_add] at hh
    apply hh.congr'
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    dsimp only [Function.comp_def]
    rw [abs_neg, abs_of_pos ht, ite_eq_right (not_lt_of_ge (neg_nonpos.2 ht.le)),
      Complex.real_smul, ofReal_inv]
    have hd : (((t ^ ν : ℝ)) : ℂ) ≠ 0 :=
      ofReal_ne_zero.2 (Real.rpow_pos_of_pos ht ν).ne'
    field_simp
    ring

/-- The opposite boundary angle has the conjugate model phase. -/
theorem tendsto_one_sub_exp_neg_cpow_div_pos {ν : ℝ} (hν : 0 < ν) :
    Tendsto (fun t : ℝ => (1 - Complex.exp (((-t : ℝ) : ℂ) * I)) ^ (ν : ℂ) /
      ((t ^ ν : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (I ^ (ν : ℂ))) := by
  have hdC : HasDerivAt (fun z : ℂ => 1 - Complex.exp (-z * I)) I 0 := by
    simpa only [Pi.neg_apply, id_eq, neg_zero, zero_mul, exp_zero, one_mul, mul_one,
      neg_one_mul, neg_neg] using
      (((((hasDerivAt_id (0 : ℂ)).neg).mul_const I).cexp).const_sub 1)
  have hs : Tendsto (fun t : ℝ => (1 - Complex.exp (((-t : ℝ) : ℂ) * I)) / (t : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 I) := by
    simpa only [zero_add, ofReal_zero, neg_zero, zero_mul, mul_zero, exp_zero,
      sub_self, sub_zero, Complex.real_smul, ofReal_inv, div_eq_mul_inv, mul_comm,
      ofReal_neg] using hdC.comp_ofReal.tendsto_slope_zero_right
  have hh := hs.cpow (tendsto_const_nhds (x := (ν : ℂ)))
    (mem_slitPlane_iff.2 (Or.inr (by simp)))
  apply hh.congr'
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  have he := cpow_mul_ofReal_pos hν (inv_pos.2 ht)
    (1 - Complex.exp (((-t : ℝ) : ℂ) * I))
  rw [div_eq_mul_inv, ← ofReal_inv, he, Real.inv_rpow ht.le,
    ofReal_inv, div_eq_mul_inv]

/-- The phases of the symmetrized analytic model sum to the real cosine
coefficient, with no improper moment integral assumed. -/
theorem neg_I_cpow_add_I_cpow (ν : ℝ) :
    (-I) ^ (ν : ℂ) + I ^ (ν : ℂ) =
      2 * ((Real.cos (Real.pi * ν / 2) : ℝ) : ℂ) := by
  have hc : I ^ (ν : ℂ) = conj ((-I) ^ (ν : ℂ)) := by
    simpa only [map_neg, conj_I, neg_neg, conj_ofReal] using
      conj_cpow (-I) (ν : ℂ) (by rw [arg_neg_I]; linarith only [Real.pi_pos])
  rw [hc, add_conj, re_neg_I_cpow_real]
  push_cast
  rfl

/-- The source boundary expansion and closed-disk continuity determine the
boundary value at the distinguished point, rather than assuming it. -/
theorem boundary_value_one_of_isLittleO {ψ : ℂ → ℂ} {c : ℂ} {ν : ℝ}
    (hν : 0 < ν) (hcont : ContinuousOn ψ (closedBall (0 : ℂ) 1))
    (hb : (fun t : ℝ => ψ (Complex.exp ((t : ℂ) * I)) - 1 -
      (if 0 < t then c else conj c) * (((|t| : ℝ) ^ ν : ℝ) : ℂ))
        =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν)) : ψ 1 = 1 := by
  have hp := (boundary_quotients_of_isLittleO hb).1
  have hpow : Tendsto (fun t : ℝ => t ^ ν) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.zero_rpow hν.ne'] using
      (Real.continuousAt_rpow_const 0 ν (Or.inr hν.le)).tendsto.mono_left
        (y := 𝓝[>] (0 : ℝ)) nhdsWithin_le_nhds
  have hpowC : Tendsto (fun t : ℝ => ((t ^ ν : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, ofReal_zero] using
      (Complex.continuous_ofReal.tendsto 0).comp hpow
  have hval : Tendsto (fun t : ℝ => ψ (Complex.exp ((t : ℂ) * I)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hh := (hp.mul hpowC).add_const 1
    simp only [mul_zero, zero_add] at hh
    apply hh.congr'
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    rw [div_mul_cancel₀ _ (ofReal_ne_zero.2 (Real.rpow_pos_of_pos ht ν).ne')]
    ring
  have hpath : Tendsto (fun t : ℝ => Complex.exp ((t : ℂ) * I))
      (𝓝[>] (0 : ℝ)) (𝓝[closedBall (0 : ℂ) 1] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have hc : Continuous (fun t : ℝ => Complex.exp ((t : ℂ) * I)) :=
        (Complex.continuous_ofReal.mul continuous_const).cexp
      simpa only [ofReal_zero, zero_mul, exp_zero] using
        (hc.tendsto 0).mono_left (y := 𝓝[>] (0 : ℝ)) nhdsWithin_le_nhds
    · exact Eventually.of_forall (fun t => by
        simp only [mem_closedBall, dist_zero_right, norm_exp_ofReal_mul_I, le_refl])
  exact tendsto_nhds_unique ((hcont 1 (by simp)).tendsto.comp hpath) hval

/-- The cosine normalization is strictly positive on the manuscript's exponent
range. -/
theorem cos_pi_mul_half_pos {ν : ℝ} (hν₀ : 0 < ν) (hν₁ : ν < 1) :
    0 < Real.cos (Real.pi * ν / 2) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have hh := mul_pos Real.pi_pos hν₀
    linarith only [hh, Real.pi_pos]
  · have hh := mul_lt_mul_of_pos_left hν₁ Real.pi_pos
    linarith only [hh]

/-- The paired boundary residual, after subtracting the normalized exact
analytic model, vanishes at the source power scale. -/
theorem tendsto_even_model_residual_div_pos {ψ : ℂ → ℂ} {c : ℂ} {ν : ℝ}
    (hν₀ : 0 < ν) (hν₁ : ν < 1)
    (hb : (fun t : ℝ => ψ (Complex.exp ((t : ℂ) * I)) - 1 -
      (if 0 < t then c else conj c) * (((|t| : ℝ) ^ ν : ℝ) : ℂ))
        =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν)) :
    let b : ℝ := c.re / Real.cos (Real.pi * ν / 2)
    Tendsto (fun t : ℝ =>
      ((ψ (Complex.exp ((t : ℂ) * I)) - 1 -
          (b : ℂ) * (1 - Complex.exp ((t : ℂ) * I)) ^ (ν : ℂ)) +
        (ψ (Complex.exp (((-t : ℝ) : ℂ) * I)) - 1 -
          (b : ℂ) * (1 - Complex.exp (((-t : ℝ) : ℂ) * I)) ^ (ν : ℂ))) /
          ((t ^ ν : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  dsimp only
  obtain ⟨hp, hn⟩ := boundary_quotients_of_isLittleO hb
  have hmodel := (tendsto_one_sub_exp_cpow_div_pos hν₀).add
    (tendsto_one_sub_exp_neg_cpow_div_pos hν₀)
  have hh := (hp.add hn).sub
    (hmodel.const_mul ((c.re / Real.cos (Real.pi * ν / 2) : ℝ) : ℂ))
  have hval : c + conj c - ((c.re / Real.cos (Real.pi * ν / 2) : ℝ) : ℂ) *
      ((-I) ^ (ν : ℂ) + I ^ (ν : ℂ)) = 0 := by
    rw [neg_I_cpow_add_I_cpow, add_conj]
    have hr : 2 * c.re - (c.re / Real.cos (Real.pi * ν / 2)) *
        (2 * Real.cos (Real.pi * ν / 2)) = 0 := by
      field_simp [(cos_pi_mul_half_pos hν₀ hν₁).ne']
      ring
    simpa only [ofReal_sub, ofReal_mul, ofReal_ofNat, ofReal_zero] using
      congrArg (fun x : ℝ => (x : ℂ)) hr
  rw [hval] at hh
  apply hh.congr'
  exact Eventually.of_forall (fun t => by ring)

/-- Conjugating the circle angle reverses its sign. -/
theorem conj_exp_angle (t : ℝ) :
    conj (Complex.exp ((t : ℂ) * I)) = Complex.exp (((-t : ℝ) : ℂ) * I) := by
  rw [← exp_conj]
  congr 1
  simp only [map_mul, conj_ofReal, conj_I, ofReal_neg, mul_neg, neg_mul]

/-- The analytic model respects conjugation on the closed disk. -/
theorem one_sub_conj_cpow {ν : ℝ} {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (1 - conj z) ^ (ν : ℂ) = conj ((1 - z) ^ (ν : ℂ)) := by
  have hr : 0 ≤ (1 - z).re := by
    rw [sub_re, one_re]
    exact sub_nonneg.2 ((re_le_norm z).trans hz)
  have ha := abs_arg_le_pi_div_two_iff.2 hr
  have hne : arg (1 - z) ≠ Real.pi := by
    intro heq
    rw [heq, abs_of_pos Real.pi_pos] at ha
    linarith only [ha, Real.pi_pos]
  simpa only [map_sub, map_one, conj_ofReal] using conj_cpow (1 - z) (ν : ℂ) hne

/-- The source expansion yields the local model comparison needed by the
compact Poisson barrier, including the value at angle zero and both signs. -/
theorem eventually_even_model_residual_le {ψ : ℂ → ℂ} {c : ℂ} {ν : ℝ}
    (hν₀ : 0 < ν) (hν₁ : ν < 1)
    (hcont : ContinuousOn ψ (closedBall (0 : ℂ) 1))
    (hb : (fun t : ℝ => ψ (Complex.exp ((t : ℂ) * I)) - 1 -
      (if 0 < t then c else conj c) * (((|t| : ℝ) ^ ν : ℝ) : ℂ))
        =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν)) :
    let b : ℝ := c.re / Real.cos (Real.pi * ν / 2)
    let f := fun z : ℂ => ψ z - 1 - (b : ℂ) * (1 - z) ^ (ν : ℂ)
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in 𝓝 0,
      ‖f (Complex.exp ((t : ℂ) * I)) + f (Complex.exp (((-t : ℝ) : ℂ) * I))‖ ≤
        ε * ((1 - Complex.exp ((t : ℂ) * I)) ^ (ν : ℂ)).re := by
  dsimp only
  let f := fun z : ℂ => ψ z - 1 -
    ((c.re / Real.cos (Real.pi * ν / 2) : ℝ) : ℂ) * (1 - z) ^ (ν : ℂ)
  let E := fun t : ℝ => f (Complex.exp ((t : ℂ) * I)) +
    f (Complex.exp (((-t : ℝ) : ℂ) * I))
  let Q := fun t : ℝ => ((1 - Complex.exp ((t : ℂ) * I)) ^ (ν : ℂ)).re
  have he : Tendsto (fun t : ℝ => E t / ((t ^ ν : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_even_model_residual_div_pos hν₀ hν₁ hb
  have hq : Tendsto (fun t : ℝ => Q t / t ^ ν) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.cos (Real.pi * ν / 2))) := tendsto_re_one_sub_exp_cpow_div_pos hν₀
  have hcos := cos_pi_mul_half_pos hν₀ hν₁
  have hEeven (t : ℝ) : E (-t) = E t := by
    dsimp only [E]
    rw [neg_neg, add_comm]
  have hQeven (t : ℝ) : Q (-t) = Q t := by
    have hz : ‖Complex.exp ((t : ℂ) * I)‖ ≤ 1 := by simp
    have hh := congrArg Complex.re (one_sub_conj_cpow (ν := ν) hz)
    simpa only [conj_exp_angle, conj_re] using hh
  have hf1 : f 1 = 0 := by
    dsimp only [f]
    simp only [boundary_value_one_of_isLittleO hν₀ hcont hb, sub_self,
      zero_cpow (ofReal_ne_zero.2 hν₀.ne'), mul_zero]
  intro ε hε
  have hη : 0 < ε * (Real.cos (Real.pi * ν / 2) / 2) :=
    mul_pos hε (half_pos hcos)
  have hen := he.norm
  simp only [norm_zero] at hen
  have hevent := hen.eventually (gt_mem_nhds hη)
  have hqevent := hq.eventually (lt_mem_nhds (half_lt_self hcos))
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ‖E t‖ ≤ ε * Q t := by
    filter_upwards [eventually_mem_nhdsWithin, hevent, hqevent] with t ht het hqt
    have htp : 0 < t ^ ν := Real.rpow_pos_of_pos ht ν
    have het' : ‖E t‖ / t ^ ν < ε * (Real.cos (Real.pi * ν / 2) / 2) := by
      simpa only [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos htp] using het
    have heprod := (div_lt_iff₀ htp).1 het'
    have hqprod := (lt_div_iff₀ htp).1 hqt
    calc
      ‖E t‖ ≤ ε * ((Real.cos (Real.pi * ν / 2) / 2) * t ^ ν) := by
        simpa only [mul_assoc] using heprod.le
      _ ≤ ε * Q t := mul_le_mul_of_nonneg_left hqprod.le hε.le
  obtain ⟨δ, hδ, hsmall⟩ := Metric.mem_nhdsWithin_iff.1 hpos
  apply Metric.eventually_nhds_iff.2
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  change ‖E t‖ ≤ ε * Q t
  rcases lt_trichotomy t 0 with hneg | rfl | hgt
  · have hh := hsmall (show -t ∈ ball (0 : ℝ) δ ∩ Ioi 0 from
        ⟨by simpa only [mem_ball, Real.dist_eq, sub_zero, abs_neg] using ht,
          neg_pos.2 hneg⟩)
    change ‖E (-t)‖ ≤ ε * Q (-t) at hh
    simpa only [hEeven, hQeven] using hh
  · simp only [E, Q, ofReal_zero, neg_zero, zero_mul, exp_zero,
      hf1, zero_add, norm_zero, sub_self, zero_cpow (ofReal_ne_zero.2 hν₀.ne'),
      zero_re, mul_zero, le_refl]
  · exact hsmall ⟨ht, hgt⟩

/-- Actual Poisson reproduction of the analytic fractional-power majorant. -/
theorem circleAverage_poisson_one_sub_cpow_re {ν w : ℝ} (hν : 0 < ν) (hw : |w| < 1) :
    Real.circleAverage (fun z : ℂ => poissonKernel 0 (w : ℂ) z *
      ((1 - z) ^ (ν : ℂ)).re) 0 1 = (1 - w) ^ ν := by
  rw [circleAverage_poisson_re (diffContOnCl_one_sub_cpow hν) hw]
  have hw' : 0 ≤ 1 - w := sub_nonneg.2 ((le_abs_self w).trans hw.le)
  rw [← ofReal_one, ← ofReal_sub, ← ofReal_cpow hw', ofReal_re]

/-- Actual Poisson reproduction of the linear boundary correction. -/
theorem circleAverage_poisson_one_sub_re {w : ℝ} (hw : |w| < 1) :
    Real.circleAverage (fun z : ℂ => poissonKernel 0 (w : ℂ) z * (1 - z).re) 0 1 =
      1 - w := by
  have hf : DiffContOnCl ℂ (fun z : ℂ => 1 - z) (ball (0 : ℂ) 1) :=
    ((differentiable_const (1 : ℂ)).sub differentiable_id).diffContOnCl
  rw [circleAverage_poisson_re hf hw, sub_re, one_re, ofReal_re]

/-- Positivity of the actual disk kernel on its integration circle. -/
theorem poissonKernel_real_nonneg {w : ℝ} (hw : |w| < 1) {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) 1) : 0 ≤ poissonKernel 0 (w : ℂ) z := by
  have hz' : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hz
  rw [poissonKernel_def, sub_zero, sub_zero, hz', norm_real, Real.norm_eq_abs]
  apply div_nonneg _ (sq_nonneg _)
  nlinarith only [hw, abs_nonneg w]

/-- Continuity of the actual disk kernel on its integration circle. -/
theorem continuousOn_poissonKernel_real {w : ℝ} (hw : |w| < 1) :
    ContinuousOn (poissonKernel 0 (w : ℂ)) (sphere (0 : ℂ) 1) := by
  have hwnot : (w : ℂ) ∉ sphere (0 : ℂ) |(1 : ℝ)| := by
    simpa only [abs_one, mem_sphere, dist_zero_right, norm_real, Real.norm_eq_abs] using
      ne_of_lt hw
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  exact Complex.continuous_re.comp_continuousOn
    (by simpa only [abs_one] using continuousOn_herglotzRieszKernel_sphere hwnot)

/-- The exact radial model value is the positive real power used in the source
conclusion. -/
theorem one_sub_radial_cpow {ν r : ℝ} (hr : 0 ≤ r) :
    (1 - ((1 - r : ℝ) : ℂ)) ^ (ν : ℂ) = ((r ^ ν : ℝ) : ℂ) := by
  have he : (1 : ℂ) - ((1 - r : ℝ) : ℂ) = (r : ℂ) := by push_cast; ring
  rw [he, ← ofReal_cpow hr]

/-- Complete analytic provider for revised A.1 (`lem-holo-asymp`). The
two-sided boundary expansion, disk regularity and nonzero real coefficient
are the source premises; all Poisson, model and barrier steps are proved. -/
theorem radial_asymptotic_of_boundary {ψ : ℂ → ℂ}
    (hcont : ContinuousOn ψ (closedBall (0 : ℂ) 1))
    (hholo : DifferentiableOn ℂ ψ (ball (0 : ℂ) 1))
    {ν : ℝ} (hν₀ : 0 < ν) (hν₁ : ν < 1) {c : ℂ} (hc : c.re ≠ 0)
    (hb : (fun t : ℝ => ψ (Complex.exp ((t : ℂ) * I)) - 1 -
      (if 0 < t then c else conj c) * (((|t| : ℝ) ^ ν : ℝ) : ℂ))
        =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν)) :
    let b : ℝ := c.re / Real.cos (Real.pi * ν / 2)
    b ≠ 0 ∧ (fun r : ℝ => ψ (((1 - r : ℝ) : ℂ)) - 1 -
      (b : ℂ) * (((r ^ ν : ℝ)) : ℂ))
        =o[𝓝[>] (0 : ℝ)] (fun r : ℝ => r ^ ν) := by
  let b : ℝ := c.re / Real.cos (Real.pi * ν / 2)
  let f := fun z : ℂ => ψ z - 1 - (b : ℂ) * (1 - z) ^ (ν : ℂ)
  let e := fun z : ℂ => f z + f (conj z)
  let q := fun z : ℂ => ((1 - z) ^ (ν : ℂ)).re
  have hψ : DiffContOnCl ℂ ψ (ball (0 : ℂ) 1) :=
    ⟨hholo, by simpa only [closure_ball (0 : ℂ) zero_lt_one.ne'] using hcont⟩
  have hm := diffContOnCl_one_sub_cpow hν₀
  have hf : DiffContOnCl ℂ f (ball (0 : ℂ) 1) := by
    convert (hψ.sub_const 1).sub (hm.const_smul (b : ℂ)) using 1
  have hfc : ContinuousOn f (sphere (0 : ℂ) 1) := by
    apply hf.continuousOn.mono
    rw [closure_ball (0 : ℂ) zero_lt_one.ne']
    exact sphere_subset_closedBall
  have hec : ContinuousOn e (sphere (0 : ℂ) 1) := by
    apply hfc.add (hfc.comp continuous_conj.continuousOn _)
    intro z hz
    simpa only [mem_sphere, dist_zero_right, norm_conj] using hz
  have hmc : ContinuousOn (fun z : ℂ => (1 - z) ^ (ν : ℂ)) (sphere (0 : ℂ) 1) := by
    apply hm.continuousOn.mono
    rw [closure_ball (0 : ℂ) zero_lt_one.ne']
    exact sphere_subset_closedBall
  have hqc : ContinuousOn q (sphere (0 : ℂ) 1) :=
    Complex.continuous_re.comp_continuousOn hmc
  have hpc : ContinuousOn (fun z : ℂ => 1 - z.re) (sphere (0 : ℂ) 1) :=
    (continuous_const.sub Complex.continuous_re).continuousOn
  have hqn : ∀ z ∈ sphere (0 : ℂ) 1, 0 ≤ q z := by
    intro z hz
    have hzn : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hz
    exact re_one_sub_cpow_nonneg hν₀ hν₁ hzn.le
  refine ⟨div_ne_zero hc (cos_pi_mul_half_pos hν₀ hν₁).ne', ?_⟩
  apply Asymptotics.IsLittleO.of_bound
  intro δ hδ
  have hl : ∀ᶠ t : ℝ in 𝓝 0, ‖e (Complex.exp ((t : ℂ) * I))‖ ≤
      δ * q (Complex.exp ((t : ℂ) * I)) := by
    simpa only [e, f, b, q, conj_exp_angle] using
      eventually_even_model_residual_le hν₀ hν₁ hcont hb δ hδ
  obtain ⟨C, hC, hbar⟩ := exists_global_circle_barrier_from_angle e q hec hqn hδ.le hl
  have hlinear := ((id_isLittleO_rpow_nhdsGT_zero hν₁).const_mul_left C).bound hδ
  filter_upwards [eventually_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds,
    hlinear] with r hr hr1 hlin
  have hr0 : 0 < r := hr
  have hw : |1 - r| < 1 := by rw [abs_lt]; constructor <;> linarith only [hr0, hr1]
  have hn := norm_circleAverage_kernel_smul_le (poissonKernel 0 ((1 - r : ℝ) : ℂ))
    e (fun z : ℂ => 1 - z.re) q (continuousOn_poissonKernel_real hw) hec hpc hqc
    (fun z hz => poissonKernel_real_nonneg hw hz) δ C hbar
  have hqavg := circleAverage_poisson_one_sub_cpow_re hν₀ hw
  have hpavg := circleAverage_poisson_one_sub_re hw
  simp only [sub_re, one_re] at hpavg
  change ‖Real.circleAverage (fun z : ℂ => poissonKernel 0 ((1 - r : ℝ) : ℂ) z •
      (f z + f (conj z))) 0 1‖ ≤ _ at hn
  rw [circleAverage_poisson_even hf hw, hqavg, hpavg, sub_sub_cancel] at hn
  have htwo : ‖(2 : ℕ) • f ((1 - r : ℝ) : ℂ)‖ = 2 * ‖f ((1 - r : ℝ) : ℂ)‖ := by
    rw [nsmul_eq_mul, norm_mul]
    norm_num
  rw [htwo] at hn
  have hpow : 0 < r ^ ν := Real.rpow_pos_of_pos hr ν
  have hlin' : C * r ≤ δ * r ^ ν := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC hr.le), abs_of_pos hpow] using hlin
  have hres : ‖f ((1 - r : ℝ) : ℂ)‖ ≤ δ * r ^ ν := by linarith only [hn, hlin']
  simpa only [f, one_sub_radial_cpow hr.le, Real.norm_eq_abs, abs_of_pos hpow] using hres

end DirectedDistances.Tauberian
