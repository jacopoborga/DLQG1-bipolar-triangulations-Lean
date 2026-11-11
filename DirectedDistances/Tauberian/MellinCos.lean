/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.PowerCos
public import DirectedDistances.Tauberian.ComplexLaplace
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Supporting lemmas for paper labels `lem:riemann` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.Tauberian

open Set MeasureTheory Filter
open scoped Topology Interval

/-- Dirichlet's finite-interval estimate, with the total variation of a
nonnegative decreasing differentiable weight evaluated by the FTC. -/
theorem norm_integral_mul_cos_le_of_deriv_nonpos {w w' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hd : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x)
    (hi : IntervalIntegrable w' volume a b)
    (hw : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hn : ∀ x ∈ Icc a b, w' x ≤ 0) :
    ‖∫ x : ℝ in a..b, w x * Real.cos x‖ ≤ 2 * w a := by
  have hd' : ∀ x ∈ uIcc a b, HasDerivAt w (w' x) x := by
    simpa only [uIcc_of_le hab] using hd
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt hd' hi
  have hm : ‖∫ x : ℝ in a..b, w' x * Real.sin x‖ ≤ w a - w b := by
    calc
      ‖∫ x : ℝ in a..b, w' x * Real.sin x‖ ≤ ∫ x : ℝ in a..b, -w' x := by
        apply intervalIntegral.norm_integral_le_of_norm_le hab _ hi.neg
        exact ae_of_all _ (fun x hx => by
          have hx' : x ∈ Icc a b := ⟨hx.1.le, hx.2⟩
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonpos (hn x hx')]
          exact (mul_le_mul_of_nonneg_left
            (show ‖Real.sin x‖ ≤ 1 by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one x)
            (neg_nonneg.2 (hn x hx'))).trans_eq (mul_one _))
      _ = w a - w b := by rw [intervalIntegral.integral_neg, hft, neg_sub]
  have hs : ∀ x ∈ Icc a b, ‖w x * Real.sin x‖ ≤ w x := by
    intro x hx
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hw x hx)]
    exact (mul_le_mul_of_nonneg_left
      (show ‖Real.sin x‖ ≤ 1 by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one x)
      (hw x hx)).trans_eq (mul_one _)
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hd'
    (fun x _ => Real.hasDerivAt_sin x) hi (Real.continuous_cos.intervalIntegrable _ _)]
  calc
    ‖w b * Real.sin b - w a * Real.sin a - ∫ x in a..b, w' x * Real.sin x‖ ≤
        (‖w b * Real.sin b‖ + ‖w a * Real.sin a‖) +
          ‖∫ x in a..b, w' x * Real.sin x‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (w b + w a) + (w a - w b) :=
      add_le_add (add_le_add (hs b ⟨hab, le_rfl⟩) (hs a ⟨le_rfl, hab⟩)) hm
    _ = 2 * w a := by ring

/-- Exponential damping leaves the power-cosine tail estimate uniform,
including damping parameter zero. -/
theorem norm_integral_damped_power_cos_tail_le {ν ε a b : ℝ}
    (hν : 0 ≤ ν) (hε : 0 ≤ ε) (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ x : ℝ in a..b, (x ^ (-ν) * Real.exp (-ε * x)) * Real.cos x‖ ≤
      2 * a ^ (-ν) := by
  let w' := fun x : ℝ =>
    (-ν * x ^ (-ν - 1)) * Real.exp (-ε * x) +
      x ^ (-ν) * (-ε * Real.exp (-ε * x))
  have hx : ∀ x ∈ Icc a b, 0 < x := fun x hx => ha.trans_le hx.1
  have hd : ∀ x ∈ Icc a b,
      HasDerivAt (fun x : ℝ => x ^ (-ν) * Real.exp (-ε * x)) (w' x) x := by
    intro x hxx
    have he : HasDerivAt (fun x : ℝ => Real.exp (-ε * x))
        (-ε * Real.exp (-ε * x)) x := by
      simpa only [id_eq, mul_one, mul_comm] using
        (((hasDerivAt_id x).const_mul (-ε)).exp)
    exact (Real.hasDerivAt_rpow_const (Or.inl (hx x hxx).ne')).mul he
  have hp : ∀ r : ℝ, ContinuousOn (fun x : ℝ => x ^ r) (uIcc a b) := by
    intro r
    apply continuousOn_id.rpow_const
    intro x hxx
    rw [uIcc_of_le hab] at hxx
    exact Or.inl (hx x hxx).ne'
  have he : ContinuousOn (fun x : ℝ => Real.exp (-ε * x)) (uIcc a b) :=
    (continuous_const.mul continuous_id).rexp.continuousOn
  have hi : IntervalIntegrable w' volume a b :=
    (((hp (-ν - 1)).const_mul (-ν)).mul he |>.add
      ((hp (-ν)).mul (he.const_mul (-ε)))).intervalIntegrable
  have hw : ∀ x ∈ Icc a b, 0 ≤ x ^ (-ν) * Real.exp (-ε * x) :=
    fun x hxx => mul_nonneg (Real.rpow_nonneg (hx x hxx).le _) (Real.exp_pos _).le
  have hn : ∀ x ∈ Icc a b, w' x ≤ 0 := by
    intro x hxx
    exact add_nonpos
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hν)
          (Real.rpow_nonneg (hx x hxx).le _)) (Real.exp_pos _).le)
      (mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (hx x hxx).le _)
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hε) (Real.exp_pos _).le))
  apply (norm_integral_mul_cos_le_of_deriv_nonpos hab hd hi hw hn).trans
  have hexp : Real.exp (-ε * a) ≤ 1 := Real.exp_le_one_iff.2
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hε) ha.le)
  exact mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg ha.le _)).trans_eq (mul_one _))
    (by norm_num)

/-- A positive exponential damping makes the power weight absolutely integrable. -/
theorem integrableOn_damped_power {ν ε : ℝ} (hν₀ : 0 ≤ ν) (hν₁ : ν < 1)
    (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ => x ^ (-ν) * Real.exp (-ε * x)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  apply IntegrableOn.union
  · apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
    exact (intervalIntegrable_rpow_neg hν₁).mul_continuousOn
      (continuous_const.mul continuous_id).rexp.continuousOn
  · apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos hε) 1).mono'
      ((measurable_id.pow_const (-ν)).mul
        (measurable_const.mul measurable_id).exp).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change ‖x ^ (-ν) * Real.exp (-ε * x)‖ ≤ Real.exp (-ε * x)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans hx).le _) (Real.exp_pos _).le)]
    exact (mul_le_mul_of_nonneg_right
      (Real.rpow_le_one_of_one_le_of_nonpos hx.le (neg_nonpos.2 hν₀))
      (Real.exp_pos _).le).trans_eq (one_mul _)

/-- The damped oscillatory integral is a genuine absolutely integrable integral. -/
theorem integrableOn_damped_power_cos {ν ε : ℝ} (hν₀ : 0 ≤ ν) (hν₁ : ν < 1)
    (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ =>
      (x ^ (-ν) * Real.exp (-ε * x)) * Real.cos x) (Ioi 0) := by
  apply (integrableOn_damped_power hν₀ hν₁ hε).mul_bdd
    Real.continuous_cos.aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one x)

/-- The uniform finite-tail bound passes to the absolutely convergent damped tail. -/
theorem norm_integral_Ioi_damped_power_cos_le {ν ε a : ℝ}
    (hν₀ : 0 ≤ ν) (hν₁ : ν < 1) (hε : 0 < ε) (ha : 0 < a) :
    ‖∫ x : ℝ in Ioi a, (x ^ (-ν) * Real.exp (-ε * x)) * Real.cos x‖ ≤
      2 * a ^ (-ν) := by
  have hi := (integrableOn_damped_power_cos hν₀ hν₁ hε).mono_set
    (Ioi_subset_Ioi ha.le)
  apply le_of_tendsto (intervalIntegral_tendsto_integral_Ioi a hi tendsto_id).norm
  filter_upwards [eventually_ge_atTop a] with b hab
  exact norm_integral_damped_power_cos_tail_le hν₀ hε.le ha hab

/-- On each bounded positive interval, damping tends to one under the integral. -/
theorem tendsto_integral_damped_power_cos_cutoff {ν A : ℝ}
    (hν : ν < 1) (hA : 0 ≤ A) :
    Tendsto (fun ε : ℝ => ∫ x : ℝ in (0 : ℝ)..A,
      (x ^ (-ν) * Real.exp (-ε * x)) * Real.cos x)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x : ℝ in (0 : ℝ)..A, x ^ (-ν) * Real.cos x)) := by
  simp only [intervalIntegral.integral_of_le hA]
  apply tendsto_integral_filter_of_dominated_convergence (fun x : ℝ => x ^ (-ν))
  · exact Eventually.of_forall (fun ε =>
      (((measurable_id.pow_const (-ν)).mul
        (measurable_const.mul measurable_id).exp).mul
          Real.continuous_cos.measurable).aestronglyMeasurable)
  · filter_upwards [eventually_mem_nhdsWithin] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    change ‖(x ^ (-ν) * Real.exp (-ε * x)) * Real.cos x‖ ≤ x ^ (-ν)
    rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx.1.le _),
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-ε * x) ≤ 1 := Real.exp_le_one_iff.2
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hε.le) hx.1.le)
    calc
      (x ^ (-ν) * Real.exp (-ε * x)) * ‖Real.cos x‖ ≤
          (x ^ (-ν) * 1) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hx.1.le _))
          (by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one x)
          (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hx.1.le _) zero_le_one)
      _ = x ^ (-ν) := by rw [mul_one, mul_one]
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hA).1
      (intervalIntegrable_rpow_neg hν)
  · exact ae_of_all _ (fun x => by
      have hh : Tendsto (fun ε : ℝ => Real.exp (-ε * x)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
        have hc : Continuous (fun ε : ℝ => Real.exp (-ε * x)) :=
          (continuous_id.neg.mul continuous_const).rexp
        simpa only [neg_zero, zero_mul, Real.exp_zero] using
          (hc.tendsto (0 : ℝ)).mono_left (y := 𝓝[>] (0 : ℝ)) nhdsWithin_le_nhds
      simpa only [mul_one] using (hh.const_mul (x ^ (-ν))).mul_const (Real.cos x))

/-- The actual improper power-cosine integral is the limit of its exponentially
damped integrals. The limit witness is supplied by the proved existence theorem. -/
theorem exists_improper_power_cos_damping_limit {ν : ℝ}
    (hν₀ : 0 < ν) (hν₁ : ν < 1) :
    ∃ J : ℝ,
      Tendsto (fun R : ℝ => ∫ x : ℝ in (0 : ℝ)..R, x ^ (-ν) * Real.cos x)
        atTop (𝓝 J) ∧
      Tendsto (fun ε : ℝ => ∫ x : ℝ in Ioi 0,
        (x ^ (-ν) * Real.exp (-ε * x)) * Real.cos x) (𝓝[>] (0 : ℝ)) (𝓝 J) := by
  obtain ⟨J, hJ⟩ := exists_improper_power_cos hν₀ hν₁
  refine ⟨J, hJ, Metric.tendsto_nhds.2 ?_⟩
  intro δ hδ
  have hδ3 : 0 < δ / 3 := div_pos hδ (by norm_num)
  have hb : ∀ᶠ A : ℝ in atTop, 2 * A ^ (-ν) < δ / 3 := by
    have hh := (tendsto_rpow_neg_atTop hν₀).const_mul 2
    have hh' : Tendsto (fun A : ℝ => 2 * A ^ (-ν)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hh
    exact hh'.eventually (gt_mem_nhds hδ3)
  have hc := (Metric.tendsto_nhds.1 hJ) (δ / 3) hδ3
  obtain ⟨A, hA, htail, hclose⟩ :=
    ((eventually_ge_atTop (1 : ℝ)).and (hb.and hc)).exists
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hfinite := Metric.tendsto_nhds.1
    (tendsto_integral_damped_power_cos_cutoff hν₁ hApos.le) (δ / 3) hδ3
  filter_upwards [eventually_mem_nhdsWithin, hfinite] with ε hε hεclose
  have hi := integrableOn_damped_power_cos hν₀.le hν₁ hε
  have hs := intervalIntegral.integral_interval_add_Ioi hi
    (hi.mono_set (Ioi_subset_Ioi hApos.le))
  have hbound := norm_integral_Ioi_damped_power_cos_le hν₀.le hν₁ hε hApos
  rw [← hs]
  rw [dist_eq_norm]
  calc
    ‖((∫ x : ℝ in (0 : ℝ)..A, (x ^ (-ν) * Real.exp (-ε * x)) * Real.cos x) +
        ∫ x : ℝ in Ioi A, (x ^ (-ν) * Real.exp (-ε * x)) * Real.cos x) - J‖ ≤
      ‖∫ x : ℝ in Ioi A, (x ^ (-ν) * Real.exp (-ε * x)) * Real.cos x‖ +
        dist (∫ x : ℝ in (0 : ℝ)..A,
          (x ^ (-ν) * Real.exp (-ε * x)) * Real.cos x)
          (∫ x : ℝ in (0 : ℝ)..A, x ^ (-ν) * Real.cos x) +
        dist (∫ x : ℝ in (0 : ℝ)..A, x ^ (-ν) * Real.cos x) J := by
      simpa only [dist_eq_norm, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        (norm_add_le
          (∫ x : ℝ in Ioi A, (x ^ (-ν) * Real.exp (-ε * x)) * Real.cos x)
          ((∫ x : ℝ in (0 : ℝ)..A, (x ^ (-ν) * Real.exp (-ε * x)) * Real.cos x) - J)).trans
          (add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub _
            (∫ x : ℝ in (0 : ℝ)..A, x ^ (-ν) * Real.cos x) _))
    _ < δ := by linarith only [hbound, htail, hεclose, hclose]

/-- The damped cosine transform is the real part of the proved complex Laplace
formula. Absolute integrability is supplied explicitly before taking real parts. -/
theorem integral_damped_power_cos_eq_gamma {ν ε : ℝ}
    (hν : ν < 1) (hε : 0 < ε) :
    (∫ x : ℝ in Ioi 0, (x ^ (-ν) * Real.exp (-ε * x)) * Real.cos x) =
      (((ε : ℂ) - Complex.I) ^ (-((1 - ν : ℝ) : ℂ)) *
        Complex.Gamma ((1 - ν : ℝ) : ℂ)).re := by
  have hz : 0 < ((ε : ℂ) - Complex.I).re := by simpa only [Complex.sub_re,
    Complex.ofReal_re, Complex.I_re, sub_zero] using hε
  have ha : -1 < -ν := by linarith only [hν]
  calc
    _ = ∫ x : ℝ in Ioi 0,
        (((x ^ (-ν) : ℝ) : ℂ) * Complex.exp (-((ε : ℂ) - Complex.I) * x)).re := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        dsimp only
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.exp_re]
        simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
          Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, sub_zero, zero_sub, mul_zero,
          one_mul, neg_neg, zero_add, sub_zero]
        ring)
    _ = (∫ x : ℝ in Ioi 0,
        ((x ^ (-ν) : ℝ) : ℂ) * Complex.exp (-((ε : ℂ) - Complex.I) * x)).re :=
      integral_re (integrableOn_complex_laplace_rpow ha hz)
    _ = _ := by
      have hh := integral_complex_laplace_rpow ha hz
      have he : -ν + 1 = 1 - ν := by ring
      rw [he] at hh
      have hc : -(ν : ℂ) + 1 = 1 - (ν : ℂ) := by ring
      simpa only [Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_one, hc] using
        congrArg Complex.re hh

/-- The boundary value of the complex Gamma expression is the sine coefficient
in revised A.6; the approach remains inside the proven Laplace half-plane. -/
theorem tendsto_damped_power_cos_gamma {ν : ℝ} (hν : ν < 1) :
    Tendsto (fun ε : ℝ => ∫ x : ℝ in Ioi 0,
      (x ^ (-ν) * Real.exp (-ε * x)) * Real.cos x) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.Gamma (1 - ν) * Real.sin (Real.pi * ν / 2))) := by
  have hs : -Complex.I ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.2 (Or.inr (by simp))
  have hz : Tendsto (fun ε : ℝ => (ε : ℂ) - Complex.I) (𝓝[>] (0 : ℝ))
      (𝓝 (-Complex.I)) := by
    simpa only [Complex.ofReal_zero, zero_sub] using
      ((Complex.continuous_ofReal.tendsto 0).sub_const Complex.I).mono_left
        (y := 𝓝[>] (0 : ℝ)) nhdsWithin_le_nhds
  have htC := (hz.cpow (tendsto_const_nhds (x := -((1 - ν : ℝ) : ℂ))) hs).mul_const
    (Complex.Gamma ((1 - ν : ℝ) : ℂ))
  have ht := (Complex.continuous_re.tendsto _).comp htC
  have hv : ((-Complex.I) ^ (-((1 - ν : ℝ) : ℂ)) *
      Complex.Gamma ((1 - ν : ℝ) : ℂ)).re =
        Real.Gamma (1 - ν) * Real.sin (Real.pi * ν / 2) := by
    rw [Complex.Gamma_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.cpow_def_of_ne_zero (neg_ne_zero.2 Complex.I_ne_zero),
      Complex.log_neg_I, Complex.exp_re]
    rw [show (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) by norm_cast]
    have hr : ((-((Real.pi / 2 : ℝ) : ℂ) * Complex.I) *
        (-((1 - ν : ℝ) : ℂ))).re = 0 := by simp
    have hi : ((-((Real.pi / 2 : ℝ) : ℂ) * Complex.I) *
        (-((1 - ν : ℝ) : ℂ))).im = Real.pi / 2 - Real.pi * ν / 2 := by
      simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [hr, hi, Real.exp_zero, one_mul, Real.cos_pi_div_two_sub, mul_comm]
  rw [hv] at ht
  apply ht.congr'
  filter_upwards [eventually_mem_nhdsWithin] with ε hε
  exact (integral_damped_power_cos_eq_gamma hν hε).symm

/-- The actual arbitrary-cutoff cosine Mellin integral has the Gamma value
claimed in revised A.6. -/
theorem tendsto_integral_power_cos_gamma {ν : ℝ} (hν₀ : 0 < ν) (hν₁ : ν < 1) :
    Tendsto (fun R : ℝ => ∫ x : ℝ in (0 : ℝ)..R, x ^ (-ν) * Real.cos x) atTop
      (𝓝 (Real.Gamma (1 - ν) * Real.sin (Real.pi * ν / 2))) := by
  obtain ⟨J, hJ, hd⟩ := exists_improper_power_cos_damping_limit hν₀ hν₁
  have hval : J = Real.Gamma (1 - ν) * Real.sin (Real.pi * ν / 2) :=
    tendsto_nhds_unique hd (tendsto_damped_power_cos_gamma hν₁)
  exact hval ▸ hJ

/-- Complete analytic provider for revised `lem:riemann` (A.6), retaining the
actual improper integrals, their Gamma value, a single uniform coefficient,
and both source remainder scales in one declaration. -/
theorem exists_staircase_power_cos_gamma_asymptotics {ν : ℝ}
    (hν₀ : 0 < ν) (hν₁ : ν < 1) :
    ∃ (J : ℝ) (I : ℝ → ℝ),
      Tendsto (fun R : ℝ => ∫ u : ℝ in (0 : ℝ)..R, u ^ (-ν) * Real.cos u)
        atTop (𝓝 J) ∧
      J = Real.Gamma (1 - ν) * Real.sin (Real.pi * ν / 2) ∧
      (∀ t : ℝ, 0 < t → Tendsto (fun R : ℝ => ∫ u : ℝ in (0 : ℝ)..R,
        (((⌊u / t⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) * Real.cos u) atTop (𝓝 (I t))) ∧
      (∀ t : ℝ, 0 < t → ‖I t - t ^ ν * J‖ ≤ t * (1 / (1 - ν) + 1)) ∧
      (fun t : ℝ => I t - t ^ ν * J) =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t) ∧
      (fun t : ℝ => I t -
        (Real.Gamma (1 - ν) * Real.sin (Real.pi * ν / 2)) * t ^ ν)
          =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ ν) := by
  obtain ⟨J, I, hJ, hI, hb, hbig, hlittle⟩ :=
    exists_improper_staircase_power_cos_asymptotics hν₀ hν₁
  have hval : J = Real.Gamma (1 - ν) * Real.sin (Real.pi * ν / 2) :=
    tendsto_nhds_unique hJ (tendsto_integral_power_cos_gamma hν₀ hν₁)
  refine ⟨J, I, hJ, hval, hI, hb, hbig, ?_⟩
  simpa only [hval, mul_comm] using hlittle

end DirectedDistances.Tauberian
