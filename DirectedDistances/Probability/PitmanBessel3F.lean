/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.PitmanBessel3E
public import Mathlib.Analysis.Calculus.ParametricIntegral





public section
namespace DirectedDistances.Probability
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- Helper toward Lemma 4.11: multiplying the sinc kernel by its frequency
has a bounded cosine derivative, including radius zero and frequency zero. -/
theorem hasDerivAt_mul_sinc (r a : ℝ) :
    HasDerivAt (fun b => b * Real.sinc (b * r)) (Real.cos (a * r)) a := by
  by_cases hr : r = 0
  · subst r
    simpa only [mul_zero, Real.sinc_zero, mul_one, Real.cos_zero, id_eq] using (hasDerivAt_id' (𝕜 := ℝ) a)
  have he (b : ℝ) : b * Real.sinc (b * r) = Real.sin (b * r) / r := by
    by_cases hb : b = 0
    · simp only [hb, zero_mul, Real.sin_zero, zero_div]
    · rw [Real.sinc_of_ne_zero (mul_ne_zero hb hr)]
      field_simp
  simp_rw [he]
  simpa only [id_eq, one_mul, mul_div_cancel_right₀ _ hr] using
    (((hasDerivAt_id a).mul_const r).sin.div_const r)

/-- Helper toward Lemma 4.11: differentiating the frequency times a sinc
transform recovers the cosine transform for every finite measure. -/
theorem hasDerivAt_integral_mul_sinc
    (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) :
    HasDerivAt (fun b => b * ∫ r, Real.sinc (b * r) ∂μ)
      (∫ r, Real.cos (a * r) ∂μ) a := by
  have hi : Integrable (fun r => a * Real.sinc (a * r)) μ := by
    apply Integrable.mono' (integrable_const |a|) (by fun_prop)
    filter_upwards [] with r
    simpa only [Real.norm_eq_abs, abs_mul, mul_one] using
      mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one (a * r)) (abs_nonneg a)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun b r : ℝ => b * Real.sinc (b * r))
    (F' := fun b r : ℝ => Real.cos (b * r)) (bound := fun _ => (1 : ℝ))
    (s := Set.univ) (x₀ := a) (Filter.univ_mem)
    (Filter.Eventually.of_forall (fun _ => by fun_prop)) hi (by fun_prop)
    (Filter.Eventually.of_forall (fun r b _ => Real.abs_cos_le_one (b * r)))
    (integrable_const 1)
    (Filter.Eventually.of_forall (fun r b _ => hasDerivAt_mul_sinc r b))
  simpa only [integral_const_mul] using hd.2

/-- Helper toward Lemma 4.11: equal sinc transforms imply equal cosine
transforms, without integrability or support assumptions beyond finite mass. -/
theorem integral_cos_eq_of_integral_sinc_eq
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ a : ℝ, (∫ r, Real.sinc (a * r) ∂μ) = ∫ r, Real.sinc (a * r) ∂ν)
    (a : ℝ) :
    (∫ r, Real.cos (a * r) ∂μ) = ∫ r, Real.cos (a * r) ∂ν := by
  have hμ := hasDerivAt_integral_mul_sinc μ a
  have hν := hasDerivAt_integral_mul_sinc ν a
  simp_rw [h] at hμ
  exact hμ.unique hν

private theorem integrable_cexp (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) :
    Integrable (fun r : ℝ => Complex.exp ((a : ℂ) * r * Complex.I)) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
  exact Filter.Eventually.of_forall (fun r => by simp [Complex.norm_exp])

/-- Helper toward Lemma 4.11: symmetrizing a finite real measure replaces
its characteristic function by twice its real cosine transform. -/
theorem charFun_add_map_neg (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) :
    charFun (μ + μ.map (fun r => -r)) a =
      2 * ((∫ r, Real.cos (a * r) ∂μ : ℝ) : ℂ) := by
  rw [charFun_apply_real, integral_add_measure (integrable_cexp μ a)
    (integrable_cexp (μ.map (fun r => -r)) a),
    integral_map (measurable_neg.aemeasurable) (by fun_prop)]
  have hn : Integrable (fun r : ℝ => Complex.exp ((a : ℂ) * (-r) * Complex.I)) μ := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
    exact Filter.Eventually.of_forall (fun r => by simp [Complex.norm_exp])
  simp only [Complex.ofReal_neg]
  rw [← integral_add (integrable_cexp μ a) hn]
  have he (r : ℝ) : Complex.exp ((a : ℂ) * r * Complex.I) +
      Complex.exp ((a : ℂ) * (-r) * Complex.I) = 2 * (Real.cos (a * r) : ℂ) := by
    apply Complex.ext <;> simp [Complex.exp_re, Complex.exp_im, mul_neg,
      ← Complex.ofReal_mul, -Complex.ofReal_cos]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_complex_ofReal]

/-- Helper toward Lemma 4.11: the cosine transform determines a finite
measure supported on the nonnegative half-line. -/
theorem measure_eq_of_integral_cos_eq_of_nonneg
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ r ∂μ, 0 ≤ r) (hν : ∀ᵐ r ∂ν, 0 ≤ r)
    (h : ∀ a : ℝ, (∫ r, Real.cos (a * r) ∂μ) = ∫ r, Real.cos (a * r) ∂ν) :
    μ = ν := by
  have hs : μ + μ.map (fun r => -r) = ν + ν.map (fun r => -r) := by
    apply Measure.ext_of_charFun
    funext a
    rw [charFun_add_map_neg, charFun_add_map_neg, h a]
  have hm (ρ : Measure ℝ) (hρ : ∀ᵐ r ∂ρ, 0 ≤ r) : ρ.map abs = ρ := by
    calc
      ρ.map abs = ρ.map id := Measure.map_congr (hρ.mono (fun r hr => abs_of_nonneg hr))
      _ = ρ := Measure.map_id
  have hn (ρ : Measure ℝ) : (ρ.map (fun r => -r)).map abs = ρ.map abs := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    simp only [Function.comp_def, abs_neg]
  have ha := congrArg (Measure.map (abs : ℝ → ℝ)) hs
  rw [Measure.map_add _ _ (by fun_prop), Measure.map_add _ _ (by fun_prop),
    hn, hn, hm μ hμ, hm ν hν] at ha
  ext s hs
  have he := congrArg (fun ρ : Measure ℝ => (ρ s).toReal) ha
  simp only [Measure.add_apply, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at he
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp (by linarith)

/-- Helper toward Lemma 4.11: sinc transforms uniquely determine finite
nonnegative laws. This is a transform-uniqueness theorem, not an assumption
of the missing Pitman or radial transition law. -/
theorem measure_eq_of_integral_sinc_eq_of_nonneg
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ r ∂μ, 0 ≤ r) (hν : ∀ᵐ r ∂ν, 0 ≤ r)
    (h : ∀ a : ℝ, (∫ r, Real.sinc (a * r) ∂μ) = ∫ r, Real.sinc (a * r) ∂ν) :
    μ = ν :=
  measure_eq_of_integral_cos_eq_of_nonneg μ ν hμ hν
    (integral_cos_eq_of_integral_sinc_eq μ ν h)

end DirectedDistances.Probability
