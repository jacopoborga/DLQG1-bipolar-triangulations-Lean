/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Supporting lemmas for paper labels `lem:riemann` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.Tauberian

open Set MeasureTheory Filter
open scoped Topology

/-- Positive real damping integrates every power whose singularity is locally
integrable at zero. This supplies all parameter-derivative majorants below. -/
theorem integrableOn_rpow_mul_exp_neg {a r : ℝ} (ha : -1 < a) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => x ^ a * Real.exp (-(r * x))) (Ioi 0) := by
  have hg : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ a) (Ioi 0) := by
    convert Real.GammaIntegral_convergent (s := a + 1) (by linarith only [ha]) using 1
    simp only [add_sub_cancel_right]
  have hh : IntegrableOn (fun x : ℝ => Real.exp (-(r * x)) * (r * x) ^ a) (Ioi 0) := by
    simpa only [mul_zero] using
      (integrableOn_Ioi_comp_mul_left_iff
        (fun x : ℝ => Real.exp (-x) * x ^ a) 0 hr).2 (by simpa only [mul_zero] using hg)
  apply (hh.const_mul ((r ^ a)⁻¹)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change (r ^ a)⁻¹ * (Real.exp (-(r * x)) * (r * x) ^ a) =
    x ^ a * Real.exp (-(r * x))
  rw [Real.mul_rpow hr.le hx.le]
  field_simp [(Real.rpow_pos_of_pos hr a).ne']

/-- Absolute integrability holds throughout the open right half-plane. -/
theorem integrableOn_complex_laplace_rpow {a : ℝ} {z : ℂ} (ha : -1 < a)
    (hz : 0 < z.re) :
    IntegrableOn (fun x : ℝ => ((x ^ a : ℝ) : ℂ) * Complex.exp (-z * x)) (Ioi 0) := by
  have hm : AEStronglyMeasurable
      (fun x : ℝ => ((x ^ a : ℝ) : ℂ) * Complex.exp (-z * x)) (volume.restrict (Ioi 0)) := by
    exact ((Complex.continuous_ofReal.measurable.comp (measurable_id.pow_const a)).mul
      ((continuous_const.mul Complex.continuous_ofReal).cexp.measurable)).aestronglyMeasurable
  apply (integrable_norm_iff hm).1
  apply (integrableOn_rpow_mul_exp_neg ha hz).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change x ^ a * Real.exp (-(z.re * x)) = ‖((x ^ a : ℝ) : ℂ) * Complex.exp (-z * x)‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hx.le _), Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, neg_mul]

/-- The absolute value of the complex Laplace integrand is its real damping
majorant. -/
theorem norm_complex_laplace_rpow (a : ℝ) (z : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    ‖((x ^ a : ℝ) : ℂ) * Complex.exp (-z * x)‖ =
      x ^ a * Real.exp (-(z.re * x)) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hx _), Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, neg_mul]

/-- The parameter derivative has one additional power of `x`. -/
theorem norm_complex_laplace_rpow_deriv (a : ℝ) (z : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖(-(x : ℂ)) * (((x ^ a : ℝ) : ℂ) * Complex.exp (-z * x))‖ =
      x ^ (a + 1) * Real.exp (-(z.re * x)) := by
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx,
    norm_complex_laplace_rpow a z hx.le, Real.rpow_add_one hx.ne']
  ring

/-- The Laplace integral is holomorphic throughout the open right half-plane,
by an explicitly integrable local derivative majorant. -/
theorem differentiableAt_complex_laplace_rpow {a : ℝ} {z : ℂ} (ha : -1 < a)
    (hz : 0 < z.re) :
    DifferentiableAt ℂ
      (fun z : ℂ => ∫ x : ℝ in Ioi 0, ((x ^ a : ℝ) : ℂ) * Complex.exp (-z * x)) z := by
  let F := fun (z : ℂ) (x : ℝ) => ((x ^ a : ℝ) : ℂ) * Complex.exp (-z * x)
  let F' := fun (z : ℂ) (x : ℝ) => (-(x : ℂ)) * F z x
  have hmeas : ∀ z : ℂ, Measurable (F z) := by
    intro z
    exact (Complex.continuous_ofReal.measurable.comp (measurable_id.pow_const a)).mul
      ((continuous_const.mul Complex.continuous_ofReal).cexp.measurable)
  have hmeas' : AEStronglyMeasurable (F' z) (volume.restrict (Ioi 0)) :=
    (Complex.continuous_ofReal.measurable.neg.mul (hmeas z)).aestronglyMeasurable
  have hs : {w : ℂ | z.re / 2 < w.re} ∈ 𝓝 z := by
    apply (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    change z.re / 2 < z.re
    linarith only [hz]
  have hbound : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0),
      ∀ w ∈ {w : ℂ | z.re / 2 < w.re},
        ‖F' w x‖ ≤ x ^ (a + 1) * Real.exp (-(z.re / 2 * x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro w hw
    change ‖(-(x : ℂ)) * (((x ^ a : ℝ) : ℂ) * Complex.exp (-w * x))‖ ≤ _
    rw [norm_complex_laplace_rpow_deriv a w hx]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx.le _)
    apply Real.exp_le_exp.2
    exact neg_le_neg (mul_le_mul_of_nonneg_right hw.le hx.le)
  have hd : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0),
      ∀ w ∈ {w : ℂ | z.re / 2 < w.re}, HasDerivAt (F · x) (F' w x) w := by
    exact ae_of_all _ (fun x w _ => by
      have hh := ((((hasDerivAt_id w).neg).mul_const (x : ℂ)).cexp).const_mul
        (((x ^ a : ℝ) : ℂ))
      simpa only [F, F', Pi.neg_apply, id_eq, neg_one_mul, mul_neg_one, mul_one, neg_mul, mul_neg,
        mul_assoc, mul_comm, mul_left_comm] using hh)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall (fun w => (hmeas w).aestronglyMeasurable))
    (integrableOn_complex_laplace_rpow ha hz) hmeas' hbound
    (integrableOn_rpow_mul_exp_neg (a := a + 1) (by linarith only [ha])
      (half_pos hz)) hd).2.differentiableAt

/-- Positive-real damping agrees with the complex power expression. -/
theorem integral_complex_laplace_rpow_real {a r : ℝ} (ha : -1 < a) (hr : 0 < r) :
    (∫ x : ℝ in Ioi 0, ((x ^ a : ℝ) : ℂ) * Complex.exp (-(r : ℂ) * x)) =
      (r : ℂ) ^ (-((a + 1 : ℝ) : ℂ)) * Complex.Gamma (a + 1) := by
  have hs : 0 < (((a + 1 : ℝ) : ℂ)).re := by
    simp only [Complex.ofReal_re]
    linarith only [ha]
  calc
    _ = ∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ ((((a + 1 : ℝ) : ℂ)) - 1) * Complex.exp (-(r * x)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      have he : (((a + 1 : ℝ) : ℂ)) - 1 = (a : ℂ) := by push_cast; ring
      rw [he, ← Complex.ofReal_cpow hx.le]
      congr 2
      ring
    _ = (1 / (r : ℂ)) ^ (((a + 1 : ℝ) : ℂ)) * Complex.Gamma (a + 1) :=
      by simpa only [Complex.ofReal_add, Complex.ofReal_one] using
        Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr
    _ = _ := by
      rw [one_div, Complex.inv_cpow_ofReal_nonneg hr.le, ← Complex.cpow_neg]

/-- The complex Laplace formula on the full right half-plane follows by the
identity theorem, after holomorphy and absolute integrability were proved. -/
theorem integral_complex_laplace_rpow {a : ℝ} {z : ℂ} (ha : -1 < a) (hz : 0 < z.re) :
    (∫ x : ℝ in Ioi 0, ((x ^ a : ℝ) : ℂ) * Complex.exp (-z * x)) =
      z ^ (-((a + 1 : ℝ) : ℂ)) * Complex.Gamma (a + 1) := by
  let U := {z : ℂ | 0 < z.re}
  let f := fun z : ℂ => ∫ x : ℝ in Ioi 0,
    ((x ^ a : ℝ) : ℂ) * Complex.exp (-z * x)
  let g := fun z : ℂ => z ^ (-((a + 1 : ℝ) : ℂ)) * Complex.Gamma (a + 1)
  have ho : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ f U := by
    apply DifferentiableOn.analyticOnNhd _ ho
    intro w hw
    exact (differentiableAt_complex_laplace_rpow ha hw).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ g U := by
    apply DifferentiableOn.analyticOnNhd _ ho
    intro w hw
    exact ((differentiableAt_id.cpow_const
      (Complex.mem_slitPlane_iff.2 (Or.inl hw))).mul_const
        (Complex.Gamma (a + 1))).differentiableWithinAt
  have hU : IsPreconnected U :=
    ((convex_Ioi (0 : ℝ)).linear_preimage Complex.reLm).isPreconnected
  have h1 : (1 : ℂ) ∈ U := by change 0 < (1 : ℂ).re; norm_num
  have hacc : (1 : ℂ) ∈ closure ({w : ℂ | f w = g w} \ {(1 : ℂ)}) := by
    have ht : Tendsto (fun n : ℕ => (1 : ℂ) +
        ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 (1 : ℂ)) := by
      simpa only [Function.comp_def, Complex.ofReal_zero, add_zero] using
        (Complex.continuous_ofReal.tendsto 0 |>.comp
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).const_add (1 : ℂ)
    apply mem_closure_of_tendsto ht
    exact Eventually.of_forall (fun n => by
      have hp : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.2 (by positivity)
      constructor
      · change f ((1 : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) = _
        have hh := integral_complex_laplace_rpow_real ha
          (show 0 < 1 + 1 / ((n : ℝ) + 1) by linarith only [hp])
        dsimp only [f, g]
        simpa only [Complex.ofReal_add, Complex.ofReal_one] using hh
      · intro heq
        have heq' : (1 : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) = 1 := heq
        have hh := congrArg Complex.re heq'
        simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re] at hh
        linarith only [hp, hh])
  exact hf.eqOn_of_preconnected_of_mem_closure hg hU h1 hacc hz

end DirectedDistances.Tauberian
