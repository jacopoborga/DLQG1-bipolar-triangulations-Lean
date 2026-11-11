module

public import DirectedDistances.Probability.StrictStableLaws

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Normed.Group.Continuity

public section

namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory
open Filter
open scoped Interval Topology Filter

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
The characteristic function gives a polynomial bound on the two-sided tail. -/
theorem spectrallyPositive_stable_tail_bound
    {α c : ℝ} {μ : ProbabilityMeasure ℝ}
    (hμ : SpectrallyPositiveStableLaw α c μ) :
    ∃ C > 0, ∀ r : ℝ, 1 ≤ r →
      (μ : Measure ℝ).real {x | r < |x|} ≤ C * Real.rpow r (-α) := by
  rcases hμ with ⟨hα₁, hα₂, hc, hchar⟩
  let b : ℝ := c * (1 + |Real.tan (Real.pi * α / 2)|)
  let C : ℝ := 2 * b * Real.exp (b * 2 ^ α) * 2 ^ α
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro r hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hrInv : 0 < r⁻¹ := inv_pos.mpr hrpos
  have hbound : ∀ x ∈ Set.uIcc (-2 * r⁻¹) (2 * r⁻¹),
      ‖1 - charFun (μ : Measure ℝ) x‖ ≤
        b * (2 * r⁻¹) ^ α * Real.exp (b * 2 ^ α) := by
    intro x hx
    have hIcc : x ∈ Set.Icc (-2 * r⁻¹) (2 * r⁻¹) := by
      have hle : (-2 : ℝ) * r⁻¹ ≤ 2 * r⁻¹ := by nlinarith [hrInv]
      simpa only [Set.uIcc_of_le (α := ℝ) hle] using hx
    have hxabs : |x| ≤ 2 * r⁻¹ := abs_le.mpr ⟨by nlinarith [hIcc.1], hIcc.2⟩
    have hxsmall : |x| ≤ 2 := by
      calc
        |x| ≤ 2 * r⁻¹ := hxabs
        _ ≤ 2 := by
          have : r⁻¹ ≤ 1 := (inv_le_one₀ hrpos).2 hr
          nlinarith
    let s : ℝ := if 0 < x then 1 else if x < 0 then -1 else 0
    let z : ℂ := -((c * |x| ^ α : ℝ) : ℂ) *
      (1 - Complex.I * ((s * Real.tan (Real.pi * α / 2) : ℝ) : ℂ))
    have hs : |s| ≤ 1 := by
      dsimp [s]
      split_ifs <;> norm_num
    have htan : |s * Real.tan (Real.pi * α / 2)| ≤
        |Real.tan (Real.pi * α / 2)| := by
      rw [abs_mul]
      calc
        |s| * |Real.tan (Real.pi * α / 2)| ≤
            1 * |Real.tan (Real.pi * α / 2)| :=
          mul_le_mul_of_nonneg_right hs (abs_nonneg _)
        _ = |Real.tan (Real.pi * α / 2)| := one_mul _
    have hfactor : ‖(1 : ℂ) - Complex.I *
        ((s * Real.tan (Real.pi * α / 2) : ℝ) : ℂ)‖ ≤
        1 + |Real.tan (Real.pi * α / 2)| := by
      calc
        _ ≤ ‖(1 : ℂ)‖ + ‖Complex.I *
            ((s * Real.tan (Real.pi * α / 2) : ℝ) : ℂ)‖ := norm_sub_le _ _
        _ = 1 + |s * Real.tan (Real.pi * α / 2)| := by
          simp only [norm_one, Complex.norm_mul, Complex.norm_I, one_mul,
            Complex.norm_real, Real.norm_eq_abs]
        _ ≤ 1 + |Real.tan (Real.pi * α / 2)| := add_le_add_right htan _
    have hz : ‖z‖ ≤ b * |x| ^ α := by
      dsimp [z, b]
      simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hc]
      calc
        c * |(|x| ^ α)| *
            ‖1 - Complex.I * ↑(s * Real.tan (Real.pi * α / 2))‖
          ≤ c * |x| ^ α * (1 + |Real.tan (Real.pi * α / 2)|) := by
            rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) α)]
            exact mul_le_mul_of_nonneg_left hfactor (by positivity)
        _ = b * |x| ^ α := by dsimp [b]; ring
    have hxpow : |x| ^ α ≤ 2 ^ α :=
      Real.rpow_le_rpow (abs_nonneg x) hxsmall (by linarith)
    have hz' : ‖z‖ ≤ b * 2 ^ α := by
      exact hz.trans (mul_le_mul_of_nonneg_left hxpow hb.le)
    have hφ : charFun (μ : Measure ℝ) x = Complex.exp z := by
      simpa [z, s] using hchar x
    rw [hφ]
    calc
      ‖1 - Complex.exp z‖ = ‖Complex.exp z - 1‖ := by rw [norm_sub_rev]
      _ ≤ ‖z‖ * Real.exp ‖z‖ := by
        simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp z 1
      _ ≤ (b * |x| ^ α) * Real.exp (b * 2 ^ α) := by
        exact mul_le_mul hz (Real.exp_le_exp.mpr hz') (by positivity) (by positivity)
      _ ≤ b * (2 * r⁻¹) ^ α * Real.exp (b * 2 ^ α) := by
        gcongr
  have hboundI : ∀ x ∈ Ι (-2 * r⁻¹) (2 * r⁻¹),
      ‖1 - charFun (μ : Measure ℝ) x‖ ≤
        b * (2 * r⁻¹) ^ α * Real.exp (b * 2 ^ α) := by
    intro x hx
    exact hbound x (Set.uIoc_subset_uIcc hx)
  have hinterval : ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
      1 - charFun (μ : Measure ℝ) t‖ ≤
        (b * (2 * r⁻¹) ^ α * Real.exp (b * 2 ^ α)) * |(2 * r⁻¹) - (-2 * r⁻¹)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hboundI
  have htail := measureReal_abs_gt_le_integral_charFun (μ := (μ : Measure ℝ)) hrpos
  calc
    (μ : Measure ℝ).real {x | r < |x|} ≤
        2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
          1 - charFun (μ : Measure ℝ) t‖ := htail
    _ ≤ C * Real.rpow r (-α) := by
      rw [show |(2 * r⁻¹) - (-2 * r⁻¹)| = 4 * r⁻¹ by
        rw [show (2 * r⁻¹) - (-2 * r⁻¹) = 4 * r⁻¹ by ring]
        exact abs_of_nonneg (by positivity)] at hinterval
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num] at *
      have hrpow : Real.rpow r (-α) = (Real.rpow r α)⁻¹ :=
        Real.rpow_neg hrpos.le α
      have hrpowpos : 0 < Real.rpow r α := Real.rpow_pos_of_pos hrpos α
      rw [hrpow]
      dsimp [C, b]
      have hpow : (2 * r⁻¹) ^ α = 2 ^ α * (r ^ α)⁻¹ := by
        rw [Real.mul_rpow (by norm_num) hrInv.le, Real.inv_rpow hrpos.le]
      calc
        1 / 2 * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
            1 - charFun (μ : Measure ℝ) t‖ ≤
            1 / 2 * r *
              (b * (2 * r⁻¹) ^ α * Real.exp (b * 2 ^ α) * (4 * r⁻¹)) := by
          gcongr
        _ = C * (Real.rpow r α)⁻¹ := by
          rw [hpow]
          dsimp [C, b]
          field_simp [ne_of_gt hrpos, ne_of_gt hrpowpos]
          ring

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
The polynomial tail bound and layer-cake formula give a finite first absolute moment. -/
theorem spectrally_positive_stable_integrable_abs
    {α c : ℝ} {μ : ProbabilityMeasure ℝ}
    (hμ : SpectrallyPositiveStableLaw α c μ) :
    Integrable (fun x : ℝ => |x|) (μ : Measure ℝ) := by
  rcases hμ with ⟨hα₁, hα₂, hc, hchar⟩
  obtain ⟨C, hC, htail⟩ := spectrallyPositive_stable_tail_bound
    (hμ := ⟨hα₁, hα₂, hc, hchar⟩)
  let M : Measure ℝ := μ
  let A : Set ℝ := Set.Ioc 0 1
  let B : Set ℝ := Set.Ioi 1
  let p : ℝ → ENNReal := fun t => ENNReal.ofReal (Real.rpow t (-α))
  let g₁ : ℝ → ENNReal := A.indicator fun _ => 1
  let g₂ : ℝ → ENNReal := fun t => ENNReal.ofReal C * B.indicator p t
  let g : ℝ → ENNReal := g₁ + g₂
  have hpos : ∀ t ∈ Set.Ioi (0 : ℝ), M {x : ℝ | t < |x|} ≤ g t := by
    intro t ht
    by_cases hle : t ≤ 1
    · have hm : M {x : ℝ | t < |x|} ≤ 1 := by
        simpa [M] using (prob_le_one (μ := (μ : Measure ℝ))
          (s := {x : ℝ | t < |x|}))
      have htA : t ∈ A := ⟨ht, hle⟩
      have htB : t ∉ B := not_lt.mpr hle
      simpa [g, g₁, g₂, A, B, htA, htB] using hm
    · have ht1 : 1 < t := lt_of_not_ge hle
      have hmfin : M {x : ℝ | t < |x|} ≠ ⊤ := by finiteness
      have hreal : M {x : ℝ | t < |x|} =
          ENNReal.ofReal (M.real {x : ℝ | t < |x|}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal hmfin]
      have htA : t ∉ A := by
        intro h
        exact (not_le_of_gt ht1) h.2
      have htB : t ∈ B := ht1
      have hgval : g t = ENNReal.ofReal (C * Real.rpow t (-α)) := by
        calc
          g t = ENNReal.ofReal C * ENNReal.ofReal (Real.rpow t (-α)) := by
            simp [g, g₁, g₂, A, B, htA, htB, p]
          _ = ENNReal.ofReal (C * Real.rpow t (-α)) := by
            rw [ENNReal.ofReal_mul hC.le]
      rw [hgval, hreal]
      exact ENNReal.ofReal_le_ofReal (htail t (le_of_lt ht1))
  have hpint : IntegrableOn (fun t : ℝ => Real.rpow t (-α)) B := by
    simpa [B] using
      (integrableOn_Ioi_rpow_of_lt (a := -α) (c := 1) (by linarith) (by norm_num))
  have hpfin : (∫⁻ t in B, p t ∂(volume : Measure ℝ)) < ⊤ := by
    simpa [p, B] using hpint.setLIntegral_lt_top
  have h1fin : (∫⁻ t in Set.Ioi (0 : ℝ), g₁ t ∂(volume : Measure ℝ)) < ⊤ := by
    have hA : (volume : Measure ℝ) A < ⊤ := by simp [A]
    calc
      _ ≤ (volume : Measure ℝ) A := by
        exact (lintegral_mono' (μ := volume.restrict (Set.Ioi (0 : ℝ)))
          (ν := volume) Measure.restrict_le_self le_rfl).trans_eq
          (by simp [g₁, A])
      _ < ⊤ := hA
  have hrest :
      (∫⁻ t, B.indicator p t ∂(volume.restrict (Set.Ioi (0 : ℝ)))) ≤
        ∫⁻ t in B, p t ∂(volume : Measure ℝ) := by
    calc
      _ ≤ ∫⁻ t, B.indicator p t ∂(volume : Measure ℝ) :=
        lintegral_mono' Measure.restrict_le_self le_rfl
      _ = ∫⁻ t in B, p t ∂(volume : Measure ℝ) :=
        lintegral_indicator measurableSet_Ioi p
  have h2fin : (∫⁻ t in Set.Ioi (0 : ℝ), g₂ t ∂(volume : Measure ℝ)) < ⊤ := by
    have hscaled : (∫⁻ t in Set.Ioi (0 : ℝ), g₂ t ∂(volume : Measure ℝ)) ≤
        ENNReal.ofReal C * (∫⁻ t in B, p t ∂(volume : Measure ℝ)) := by
      calc
        _ = ENNReal.ofReal C *
            (∫⁻ t in Set.Ioi (0 : ℝ), B.indicator p t ∂(volume : Measure ℝ)) := by
          change (∫⁻ t, ENNReal.ofReal C * B.indicator p t ∂
            (volume.restrict (Set.Ioi (0 : ℝ)))) = _
          exact lintegral_const_mul' _ _ (by simp)
        _ ≤ ENNReal.ofReal C * (∫⁻ t in B, p t ∂(volume : Measure ℝ)) :=
          mul_le_mul_of_nonneg_left hrest (by positivity)
    exact lt_of_le_of_lt hscaled (ENNReal.mul_lt_top (by simp) hpfin)
  have hGmeas : Measurable g₁ := by
    exact measurable_const.indicator measurableSet_Ioc
  have hGfin : (∫⁻ t in Set.Ioi (0 : ℝ), g t ∂(volume : Measure ℝ)) < ⊤ := by
    change (∫⁻ t, g₁ t + g₂ t ∂(volume.restrict (Set.Ioi (0 : ℝ)))) < ⊤
    rw [lintegral_add_left' (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      hGmeas.aemeasurable]
    exact ENNReal.add_lt_top.mpr ⟨h1fin, h2fin⟩
  have hcake := lintegral_eq_lintegral_meas_lt (μ := M)
    (f := fun x : ℝ => |x|) (ae_of_all _ fun x => abs_nonneg x)
    continuous_abs.measurable.aemeasurable
  have hbound :
      (∫⁻ t in Set.Ioi (0 : ℝ), M {x : ℝ | t < |x|} ∂(volume : Measure ℝ)) ≤
        ∫⁻ t in Set.Ioi (0 : ℝ), g t ∂(volume : Measure ℝ) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hpos t ht
  have hlin : (∫⁻ x, ENNReal.ofReal (|x|) ∂M) < ⊤ := by
    calc
      _ = ∫⁻ t in Set.Ioi (0 : ℝ), M {x : ℝ | t < |x|} ∂(volume : Measure ℝ) := hcake
      _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), g t ∂(volume : Measure ℝ) := hbound
      _ < ⊤ := hGfin
  refine ⟨continuous_abs.measurable.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simpa [Real.norm_eq_abs, abs_abs] using hlin

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
The first moment is the derivative of the characteristic function at zero. -/
theorem spectrally_positive_stable_charFun_hasDerivAt_zero
    {α c : ℝ} {μ : ProbabilityMeasure ℝ}
    (hμ : SpectrallyPositiveStableLaw α c μ) :
    HasDerivAt (fun u : ℝ => charFun (μ : Measure ℝ) u)
      (Complex.I * (((∫ x : ℝ, x ∂(μ : Measure ℝ)) : ℝ) : ℂ)) 0 := by
  let M : Measure ℝ := μ
  let F : ℝ → ℝ → ℂ := fun u x => Complex.exp (u • ((x : ℂ) * Complex.I))
  let F' : ℝ → ℝ → ℂ := fun u x =>
    Complex.exp (u • ((x : ℂ) * Complex.I)) * ((x : ℂ) * Complex.I)
  have hMabs : Integrable (fun x : ℝ => |x|) M := by
    simpa [M] using spectrally_positive_stable_integrable_abs hμ
  have hs : Metric.ball (0 : ℝ) 1 ∈ 𝓝 0 := Metric.ball_mem_nhds _ zero_lt_one
  have hFmeas : ∀ᶠ u in 𝓝 (0 : ℝ), AEStronglyMeasurable (F u) M := by
    filter_upwards [] with u
    dsimp [F]
    fun_prop
  have hFint : Integrable (F 0) M := by
    simp [F]
  have hF'meas : AEStronglyMeasurable (F' 0) M := by
    dsimp [F']
    fun_prop
  have hbound : ∀ᵐ x ∂M, ∀ u ∈ Metric.ball (0 : ℝ) 1, ‖F' u x‖ ≤ |x| := by
    filter_upwards [] with x
    intro u hu
    dsimp [F']
    have harg : (u : ℂ) * ((x : ℂ) * Complex.I) =
        ((u * x : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [Complex.norm_mul, harg, Complex.norm_exp_ofReal_mul_I]
    simp [Complex.norm_I, Real.norm_eq_abs]
  have hdiff : ∀ᵐ x ∂M, ∀ u ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt (F · x) (F' u x) u := by
    filter_upwards [] with x
    intro u hu
    simpa only [F, F', Complex.exp_eq_exp_ℂ, smul_eq_mul, mul_assoc] using
      (hasDerivAt_exp_smul_const ((x : ℂ) * Complex.I) u)
  have hderiv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := M) (s := Metric.ball (0 : ℝ) 1) (x₀ := 0) hs hFmeas hFint hF'meas
    hbound hMabs hdiff).2
  have hFchar : (fun u : ℝ => charFun M u) = fun u => ∫ x, F u x ∂M := by
    funext u
    rw [charFun_apply_real]
    congr 1
    funext x
    simp [F, mul_assoc]
  have hint : (∫ x : ℝ, (x : ℂ) * Complex.I ∂M) =
      Complex.I * (((∫ x : ℝ, x ∂M : ℝ) : ℂ)) := by
    have hreal : (∫ x : ℝ, (x : ℂ) ∂M) =
        (((∫ x : ℝ, x ∂M : ℝ) : ℂ)) := integral_ofReal
    rw [integral_mul_const, hreal]
    ring
  rw [hFchar]
  simpa [F', hint, smul_eq_mul] using hderiv

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
The strictly stable characteristic function forces a zero mean when `α > 1`. -/
theorem spectrally_positive_stable_mean_eq_zero
    {α c : ℝ} {μ : ProbabilityMeasure ℝ}
    (hμ : SpectrallyPositiveStableLaw α c μ) :
    ∫ x : ℝ, x ∂(μ : Measure ℝ) = 0 := by
  rcases hμ with ⟨hα₁, hα₂, hc, hchar⟩
  let M : Measure ℝ := μ
  let t : ℝ := Real.tan (Real.pi * α / 2)
  let b : ℝ := c * (1 + |t|)
  let C : ℝ := b * Real.exp b
  have hb : 0 < b := by positivity
  have hderiv := spectrally_positive_stable_charFun_hasDerivAt_zero
    (hμ := ⟨hα₁, hα₂, hc, hchar⟩)
  have hzero : charFun M 0 = 1 := by simp [M]
  have hformulaBound : ∀ u : ℝ, |u| ≤ 1 →
      ‖charFun M u - 1‖ ≤ C * |u| ^ α := by
    intro u hu
    let s : ℝ := if 0 < u then 1 else if u < 0 then -1 else 0
    let z : ℂ := -((c * |u| ^ α : ℝ) : ℂ) *
      (1 - Complex.I * ((s * t : ℝ) : ℂ))
    have hs : |s| ≤ 1 := by
      dsimp [s]
      split_ifs <;> norm_num
    have hst : |s * t| ≤ |t| := by
      rw [abs_mul]
      calc
        |s| * |t| ≤ 1 * |t| := mul_le_mul_of_nonneg_right hs (abs_nonneg t)
        _ = |t| := one_mul _
    have hfactor : ‖(1 : ℂ) - Complex.I * ((s * t : ℝ) : ℂ)‖ ≤ 1 + |t| := by
      calc
        _ ≤ ‖(1 : ℂ)‖ + ‖Complex.I * ((s * t : ℝ) : ℂ)‖ := norm_sub_le _ _
        _ = 1 + |s * t| := by
          simp only [norm_one, Complex.norm_mul, Complex.norm_I, one_mul,
            Complex.norm_real, Real.norm_eq_abs]
        _ ≤ 1 + |t| := add_le_add_right hst 1
    have hz : ‖z‖ ≤ b * |u| ^ α := by
      dsimp [z, b]
      simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hc]
      calc
        c * |(|u| ^ α)| * ‖1 - Complex.I * ↑(s * t)‖ ≤
            c * |u| ^ α * (1 + |t|) := by
          rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg u) α)]
          exact mul_le_mul_of_nonneg_left hfactor (by positivity)
        _ = c * (1 + |t|) * |u| ^ α := by ring
    have hpow : |u| ^ α ≤ 1 := by
      calc
        |u| ^ α ≤ (1 : ℝ) ^ α :=
          Real.rpow_le_rpow (abs_nonneg u) hu (by linarith)
        _ = 1 := by simp
    have hz' : ‖z‖ ≤ b := by
      calc
        ‖z‖ ≤ b * |u| ^ α := hz
        _ ≤ b * 1 := mul_le_mul_of_nonneg_left hpow hb.le
        _ = b := mul_one _
    have hφ : charFun M u = Complex.exp z := by
      simpa [M, z, s, t] using hchar u
    rw [hφ]
    calc
      ‖Complex.exp z - 1‖ = ‖Complex.exp z - 1‖ := rfl
      _ ≤ ‖z‖ * Real.exp ‖z‖ := by
        simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp z 1
      _ ≤ (b * |u| ^ α) * Real.exp b :=
        mul_le_mul hz (Real.exp_le_exp.mpr hz') (by positivity) (by positivity)
      _ = C * |u| ^ α := by dsimp [C]; ring
  have hsmall : ∀ᶠ u in 𝓝[≠] (0 : ℝ), |u| ≤ 1 := by
    have hball : ∀ᶠ u in 𝓝 (0 : ℝ), u ∈ Metric.ball 0 1 :=
      Metric.ball_mem_nhds _ zero_lt_one
    filter_upwards [hball.filter_mono nhdsWithin_le_nhds] with u hu
    have hu' : dist u (0 : ℝ) < 1 := Metric.mem_ball.mp hu
    have hu'' : |u| < 1 := by simpa [Real.dist_eq] using hu'
    exact le_of_lt hu''
  have hne : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ≠ 0 :=
    by
      filter_upwards [eventually_mem_nhdsWithin] with u hu
      exact hu
  have hslopeBound : ∀ᶠ u in 𝓝[≠] (0 : ℝ),
      ‖u⁻¹ • (charFun M u - charFun M 0)‖ ≤ C * |u| ^ (α - 1) := by
    filter_upwards [hsmall, hne] with u hu hu0
    have hcu := hformulaBound u hu
    calc
      ‖u⁻¹ • (charFun M u - charFun M 0)‖ = |u|⁻¹ *
          ‖charFun M u - 1‖ := by simp [hzero, Real.norm_eq_abs]
      _ ≤ |u|⁻¹ * (C * |u| ^ α) :=
        mul_le_mul_of_nonneg_left hcu (by positivity)
      _ = C * |u| ^ (α - 1) := by
        rw [Real.rpow_sub (abs_pos.mpr hu0) α 1]
        field_simp
        rw [Real.rpow_one]
        ring
  have hpow : Tendsto (fun u : ℝ => |u| ^ (α - 1))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have hbase : Continuous (fun x : ℝ => x ^ (α - 1)) :=
      Real.continuous_rpow_const (by linarith)
    have hcont : Continuous (fun u : ℝ => |u| ^ (α - 1)) :=
      hbase.comp continuous_abs
    have hcont0 : Tendsto (fun u : ℝ => |u| ^ (α - 1))
        (𝓝 (0 : ℝ)) (𝓝 0) := by
      have habs : Tendsto (fun u : ℝ => |u|) (𝓝 0) (𝓝 0) := by
        simpa using continuous_abs.tendsto (0 : ℝ)
      have hp : Tendsto (fun x : ℝ => x ^ (α - 1)) (𝓝 0)
          (𝓝 ((0 : ℝ) ^ (α - 1))) :=
        (Real.continuousAt_rpow_const 0 (α - 1)
          (Or.inr (by linarith : 0 ≤ α - 1))).tendsto
      have hcomp : Tendsto (fun u : ℝ => (fun x : ℝ => x ^ (α - 1)) |u|)
          (𝓝 0) (𝓝 ((0 : ℝ) ^ (α - 1))) := hp.comp habs
      simpa only [Real.zero_rpow (by linarith : α - 1 ≠ 0)] using hcomp
    exact hcont0.mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := ({0}ᶜ : Set ℝ)))
  have hboundTendsto : Tendsto (fun u : ℝ => C * |u| ^ (α - 1))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa using hpow.const_mul C
  have hslopeNorm : Tendsto
      (fun u : ℝ => ‖u⁻¹ • (charFun M u - charFun M 0)‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      hslopeBound hboundTendsto
  have hslope : Tendsto (fun u : ℝ => u⁻¹ •
      (charFun M u - charFun M 0)) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hslopeNorm
  have hderivZero : HasDerivAt (fun u : ℝ => charFun M u) 0 0 :=
    hasDerivAt_iff_tendsto_slope_zero.mpr (by simpa only [zero_add] using hslope)
  have heq := hderiv.unique hderivZero
  have hmeanComplex : (((∫ x : ℝ, x ∂M) : ℝ) : ℂ) = 0 := by
    rcases mul_eq_zero.mp heq with hI | hmean
    · exact (Complex.I_ne_zero hI).elim
    · exact hmean
  have hmean : ∫ x : ℝ, x ∂M = 0 := by exact_mod_cast hmeanComplex
  simpa [M] using hmean

/-- Helper toward Lemma 7.12 (lem-boltzmann-sdp-lower); not a paper result.
The law has positive mass on the negative half-line. -/
theorem spectrally_positive_stable_negative_mass
    {α c : ℝ} {μ : ProbabilityMeasure ℝ}
    (hμ : SpectrallyPositiveStableLaw α c μ) :
    0 < (μ : Measure ℝ) (Set.Iio 0) := by
  have hmean := spectrally_positive_stable_mean_eq_zero hμ
  have habs := spectrally_positive_stable_integrable_abs hμ
  by_contra hneg
  have hμzero : (μ : Measure ℝ) (Set.Iio 0) = 0 :=
    le_antisymm (le_of_not_gt hneg) zero_le
  have hnonneg : ∀ᵐ x ∂(μ : Measure ℝ), 0 ≤ x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμzero] with x hx
    simpa only [Set.mem_Iio, not_lt] using hx
  have habsEq : (fun x : ℝ => |x|) =ᵐ[(μ : Measure ℝ)] fun x => x := by
    filter_upwards [hnonneg] with x hx
    exact abs_of_nonneg hx
  have hInt : Integrable (fun x : ℝ => x) (μ : Measure ℝ) :=
    (integrable_congr habsEq).mp habs
  have hzero : (fun x : ℝ => x) =ᵐ[(μ : Measure ℝ)] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hInt).mp hmean
  have hcharone : charFun (μ : Measure ℝ) 1 = 1 := by
    rw [charFun_apply_real]
    have hfun : (fun x : ℝ =>
        Complex.exp (((1 : ℝ) : ℂ) * (x : ℂ) * Complex.I)) =ᵐ[(μ : Measure ℝ)]
        fun _ => (1 : ℂ) := by
      filter_upwards [hzero] with x hx
      simp [hx]
    rw [integral_congr_ae hfun]
    simp
  rcases hμ with ⟨_, _, hc, hφ⟩
  let t : ℝ := Real.tan (Real.pi * α / 2)
  let z : ℂ := -(c : ℂ) * (1 - Complex.I * (t : ℂ))
  have hφone : charFun (μ : Measure ℝ) 1 = Complex.exp z := by
    simpa [z, t] using hφ 1
  have hzre : z.re = -c := by
    simp [z, Complex.mul_re, Complex.I_re, Complex.I_im]
  have hnorm : ‖charFun (μ : Measure ℝ) 1‖ = Real.exp (-c) := by
    rw [hφone, Complex.norm_exp, hzre]
  have heq : Real.exp (-c) = 1 := by
    simpa [hcharone] using hnorm.symm
  have hexp : Real.exp (-c) < 1 := by
    simpa using Real.exp_lt_exp.mpr (show -c < 0 by linarith)
  linarith

end DirectedDistances.Probability
