/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.PitmanBessel3E
public import DirectedDistances.Probability.PitmanBessel3C
public import Mathlib.Analysis.Calculus.ParametricIntegral
import DirectedDistances.Probability.PitmanBessel3G

/-! Helper toward Lemma 4.11: uniqueness tools for the one-time sinc transform. -/

public section

namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory Filter Set
open DirectedDistances.RandomWalk
open scoped Topology NNReal ENNReal

local instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    MeasurableSpace C(X, Y) := borel _
local instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    BorelSpace C(X, Y) := ⟨rfl⟩
local instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [LocallyCompactSpace X] [SecondCountableTopology Y] :
    SecondCountableTopology C(X, Y) := continuousPath_secondCountable

namespace OneTimeSinc

/-- Helper toward Lemma 4.11: multiplication by the frequency removes the
singularity of the sinc transform, including a zero spatial argument. -/
theorem hasDerivAt_mul_sinc (x a : ℝ) :
    HasDerivAt (fun b : ℝ => b * Real.sinc (b * x)) (Real.cos (a * x)) a := by
  by_cases hx : x = 0
  · simpa only [hx, mul_zero, Real.sinc_zero, mul_one, Real.cos_zero, id_eq]
      using (hasDerivAt_id' a)
  have he (b : ℝ) : b * Real.sinc (b * x) = Real.sin (b * x) / x := by
    by_cases hb : b = 0
    · simp [hb]
    · rw [Real.sinc_of_ne_zero (mul_ne_zero hb hx)]
      field_simp
  simp_rw [he]
  simpa only [mul_div_cancel_right₀ _ hx] using
    (hasDerivAt_mul_const (x := a) x).sin.div_const x

/-- Helper toward Lemma 4.11: the derivative of frequency times the sinc
transform of any finite real measure is its cosine transform. No moment
assumption is needed. -/
theorem hasDerivAt_integral_mul_sinc (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) :
    HasDerivAt (fun b : ℝ => b * ∫ x, Real.sinc (b * x) ∂μ)
      (∫ x, Real.cos (a * x) ∂μ) a := by
  have hi (b : ℝ) : Integrable (fun x : ℝ => b * Real.sinc (b * x)) μ := by
    apply Integrable.mono' (integrable_const |b|) (by fun_prop)
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_mul, mul_one] using
      mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one (b * x)) (abs_nonneg b)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun b x : ℝ => b * Real.sinc (b * x))
    (F' := fun b x : ℝ => Real.cos (b * x)) (bound := fun _ => (1 : ℝ))
    (s := Set.univ) (by simp)
    (Filter.Eventually.of_forall (fun _ => by fun_prop)) (hi a) (by fun_prop)
    (Filter.Eventually.of_forall (fun x b _ => by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (b * x)))
    (integrable_const 1)
    (Filter.Eventually.of_forall (fun x b _ => hasDerivAt_mul_sinc x b))
  simpa only [integral_const_mul] using hd.2

/-- Helper toward Lemma 4.11: equal sinc transforms imply equal cosine
transforms for finite real measures, without integrability of the identity. -/
theorem integral_cos_eq_of_integral_sinc_eq
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ a : ℝ, (∫ x, Real.sinc (a * x) ∂μ) =
      ∫ x, Real.sinc (a * x) ∂ν) (a : ℝ) :
    (∫ x, Real.cos (a * x) ∂μ) = ∫ x, Real.cos (a * x) ∂ν := by
  have he : (fun b : ℝ => b * ∫ x, Real.sinc (b * x) ∂μ) =
      (fun b : ℝ => b * ∫ x, Real.sinc (b * x) ∂ν) := by
    funext b
    rw [h b]
  have hd := hasDerivAt_integral_mul_sinc μ a
  rw [he] at hd
  exact hd.unique (hasDerivAt_integral_mul_sinc ν a)

private theorem integrable_cexp_mul (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) :
    Integrable (fun x : ℝ => Complex.exp ((a : ℂ) * x * Complex.I)) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
  filter_upwards [] with x
  simp [Complex.norm_exp]

private theorem charFun_add_map_neg (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) :
    charFun (μ + μ.map (fun x : ℝ => -x)) a =
      Complex.ofReal (∫ x, Real.cos (a * x) ∂μ) +
        Complex.ofReal (∫ x, Real.cos (a * x) ∂μ) := by
  rw [charFun_apply_real, integral_add_measure (integrable_cexp_mul μ a)
    (integrable_cexp_mul _ a), integral_map (by fun_prop :
      AEMeasurable (fun x : ℝ => -x) μ) (by fun_prop)]
  rw [← integral_add (integrable_cexp_mul μ a)
    (by simpa only [Complex.ofReal_neg, mul_neg, neg_mul] using integrable_cexp_mul μ (-a))]
  have he (x : ℝ) :
      Complex.exp ((a : ℂ) * x * Complex.I) +
        Complex.exp ((a : ℂ) * Complex.ofReal (-x) * Complex.I) =
      ((Real.cos (a * x) + Real.cos (a * x) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
    simp only [mul_neg, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, Complex.ofReal_add]
    ring
  calc
    _ = ∫ x, ((Real.cos (a * x) + Real.cos (a * x) : ℝ) : ℂ) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall he)
    _ = _ := ?_
  rw [integral_complex_ofReal, integral_add]
  · exact Complex.ofReal_add _ _
  all_goals
    apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (a * x)

/-- Helper toward Lemma 4.11: a finite measure supported on the nonnegative
half-line is uniquely determined by its cosine transform. -/
theorem measure_eq_of_integral_cos_eq_of_nonneg
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hν : ∀ᵐ x ∂ν, 0 ≤ x)
    (h : ∀ a : ℝ, (∫ x, Real.cos (a * x) ∂μ) =
      ∫ x, Real.cos (a * x) ∂ν) : μ = ν := by
  have hs : μ + μ.map (fun x : ℝ => -x) =
      ν + ν.map (fun x : ℝ => -x) := by
    apply Measure.ext_of_charFun
    funext a
    rw [charFun_add_map_neg, charFun_add_map_neg, h a]
  have habs (ρ : Measure ℝ) (hρ : ∀ᵐ x ∂ρ, 0 ≤ x) : ρ.map abs = ρ := by
    calc
      ρ.map abs = ρ.map id := Measure.map_congr (hρ.mono (fun x hx => abs_of_nonneg hx))
      _ = ρ := Measure.map_id
  have hneg (ρ : Measure ℝ) :
      (ρ.map (fun x : ℝ => -x)).map abs = ρ.map abs := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    exact abs_neg x
  have he := congrArg (Measure.map (abs : ℝ → ℝ)) hs
  rw [Measure.map_add _ _ (by fun_prop), Measure.map_add _ _ (by fun_prop),
    hneg, hneg, habs μ hμ, habs ν hν] at he
  apply Measure.ext
  intro s hs
  have hv := congrArg (fun ρ : Measure ℝ => ρ s) he
  simp only [Measure.add_apply, ← two_mul] at hv
  exact (ENNReal.mul_right_inj (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).mp hv

/-- Helper toward Lemma 4.11: finite nonnegative real laws are uniquely
determined by their sinc transforms, with no moment or density assumptions. -/
theorem measure_eq_of_integral_sinc_eq_of_nonneg
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hν : ∀ᵐ x ∂ν, 0 ≤ x)
    (h : ∀ a : ℝ, (∫ x, Real.sinc (a * x) ∂μ) =
      ∫ x, Real.sinc (a * x) ∂ν) : μ = ν := by
  exact measure_eq_of_integral_cos_eq_of_nonneg μ ν hμ hν
    (integral_cos_eq_of_integral_sinc_eq μ ν h)

end OneTimeSinc

/-- Helper toward Lemma 4.11: equality of all sinc expectations identifies
nonnegative random variables on possibly different finite measure spaces. -/
theorem identDistrib_of_integral_sinc_eq_of_nonneg
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {X : Ω → ℝ} {Y : Ω' → ℝ} (hX : AEMeasurable X P) (hY : AEMeasurable Y Q)
    (hX₀ : ∀ᵐ ω ∂P, 0 ≤ X ω) (hY₀ : ∀ᵐ ω ∂Q, 0 ≤ Y ω)
    (h : ∀ a : ℝ, (∫ ω, Real.sinc (a * X ω) ∂P) =
      ∫ ω, Real.sinc (a * Y ω) ∂Q) : IdentDistrib X Y P Q := by
  refine ⟨hX, hY, OneTimeSinc.measure_eq_of_integral_sinc_eq_of_nonneg _ _
    ((ae_map_iff hX measurableSet_Ici).mpr hX₀)
    ((ae_map_iff hY measurableSet_Ici).mpr hY₀) ?_⟩
  intro a
  rw [integral_map hX (by fun_prop), integral_map hY (by fun_prop)]
  exact h a

/-- Helper toward Lemma 4.11: the Gaussian vector underlying the radial
process at one arbitrary time has the product of three exact marginal laws. -/
theorem firstThree_hasLaw_eval
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (t : ℝ≥0) :
    HasLaw (fun p (i : Fin 3) => p t i.castSucc)
      (Measure.pi (fun _ : Fin 3 => gaussianReal 0 t)) W₄ := by
  have hm (i : Fin 3) : Measurable
      (fun p : C(ℝ≥0, Fin 4 → ℝ) => p t i.castSucc) :=
    (measurable_pi_apply i.castSucc).comp (continuous_eval_const t).measurable
  have hi := (hI.precomp (Fin.castSucc_injective 3)).comp
    (fun _ : Fin 3 => fun f : C(ℝ≥0, ℝ) => f t)
    (fun _ => (continuous_eval_const t).measurable)
  refine ⟨(measurable_pi_iff.mpr hm).aemeasurable, ?_⟩
  rw [hi.map_fun_eq_pi_map (fun i => (hm i).aemeasurable)]
  congr 1
  funext i
  exact (hB i.castSucc).hasLaw_eval t |>.map_eq

/-- Helper toward Lemma 4.11: the radial one-time law is the explicit norm
pushforward of three independent centered Gaussians of variance `t`. -/
theorem radial3_hasLaw_eval
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (t : ℝ≥0) :
    HasLaw (fun p => radial3Path (firstThreePath p) t)
      ((Measure.pi (fun _ : Fin 3 => gaussianReal 0 t)).map
        (fun x => Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2))) W₄ := by
  exact (hasLaw_map (by fun_prop : AEMeasurable
    (fun x : Fin 3 → ℝ => Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2))
      (Measure.pi (fun _ : Fin 3 => gaussianReal 0 t)))).comp
    (firstThree_hasLaw_eval W₄ hB hI t)

/-- Helper toward Lemma 4.11: Brownian scaling as a continuous scalar path. -/
@[expose] noncomputable def brownianScalePath (c : ℝ≥0) (f : C(ℝ≥0, ℝ)) :
    C(ℝ≥0, ℝ) :=
  ⟨fun s => (Real.sqrt c)⁻¹ * f (c * s), by fun_prop⟩

/-- Helper toward Lemma 4.11: Brownian scaling is continuous in the input path. -/
theorem continuous_brownianScalePath (c : ℝ≥0) : Continuous (brownianScalePath c) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_const.mul (continuous_eval.comp
    (continuous_fst.prodMk (continuous_const.mul continuous_snd)))

/-- Helper toward Lemma 4.11: positive time scaling preserves precisely the
closed interval used by the running minimum. -/
theorem runningMinimum_time_mul (f : C(ℝ≥0, ℝ)) (c t : ℝ≥0) (hc : c ≠ 0) :
    sInf ((fun s => f (c * s)) '' Set.Icc 0 t) =
      continuousRunningMinimum f (c * t) := by
  change sInf _ = sInf _
  congr 1
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨c * s, ⟨zero_le, mul_le_mul_of_nonneg_left hs.2 zero_le⟩, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s / c, ⟨zero_le, (div_le_iff₀ (pos_iff_ne_zero.mpr hc)).mpr ?_⟩, ?_⟩
    · simpa only [mul_comm] using hs.2
    · change f (c * (s / c)) = f s
      rw [mul_div_cancel₀ _ hc]

/-- Helper toward Lemma 4.11: the scalar Pitman transform commutes with
positive Brownian scaling at every time. -/
theorem scalarPitman_brownianScalePath (f : C(ℝ≥0, ℝ)) (c : ℝ≥0) (hc : c ≠ 0)
    (t : ℝ≥0) :
    scalarPitman (brownianScalePath c f) t =
      (Real.sqrt c)⁻¹ * scalarPitman f (c * t) := by
  let g : C(ℝ≥0, ℝ) := ⟨fun s => f (c * s), by fun_prop⟩
  have hm := runningMinimum_const_mul g (Real.sqrt c)⁻¹ (by positivity) t
  change (Real.sqrt c)⁻¹ * f (c * t) -
    2 * sInf ((fun s => (Real.sqrt c)⁻¹ * f (c * s)) '' Set.Icc 0 t) = _
  change sInf ((fun s => (Real.sqrt c)⁻¹ * f (c * s)) '' Set.Icc 0 t) =
    (Real.sqrt c)⁻¹ * sInf ((fun s => f (c * s)) '' Set.Icc 0 t) at hm
  rw [hm, runningMinimum_time_mul f c t hc]
  change _ = (Real.sqrt c)⁻¹ * (f (c * t) - 2 * continuousRunningMinimum f (c * t))
  ring

/-- Helper toward Lemma 4.11: every positive-time scalar Pitman marginal
is the square-root time dilation of its time-one marginal. -/
theorem scalarPitman_eval_identDistrib_scale
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t 0) W₄)
    (t : ℝ≥0) (ht : t ≠ 0) :
    IdentDistrib (fun p => scalarPitman (pathCoordinate p 0) t)
      (fun p => Real.sqrt t * scalarPitman (pathCoordinate p 0) 1) W₄ W₄ := by
  have hp := brownianScalarPath_identDistrib
    ((continuous_brownianScalePath t).comp (continuous_pathCoordinate 0)).measurable
    (continuous_pathCoordinate 0).measurable (hB.smul ht) hB
  have he := hp.comp ((continuous_eval_const 1).comp continuous_scalarPitman).measurable
  have hh := he.comp (by fun_prop : Measurable (fun x : ℝ => Real.sqrt t * x))
  have hs : Real.sqrt (t : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (NNReal.coe_pos.mpr
    (pos_iff_ne_zero.mpr ht))
  convert hh using 1
  · funext p
    simp only [Function.comp_apply, scalarPitman_brownianScalePath _ _ ht, mul_one]
    exact (mul_inv_cancel_left₀ hs _).symm
  · rfl

/-- Helper toward Lemma 4.11: the scalar Pitman sinc transform at every
positive time, with the exact Brownian variance factor `t`. -/
theorem scalarPitman_eval_sinc_of_pos
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (t : ℝ≥0) (ht : t ≠ 0) (a : ℝ) :
    (∫ p, Real.sinc (a * scalarPitman (pathCoordinate p 0) t) ∂W₄) =
      Real.exp (-(a ^ 2 * t) / 2) := by
  have h := (scalarPitman_eval_identDistrib_scale W₄ (hB 0) t ht).comp
    (by fun_prop : Measurable (fun x : ℝ => Real.sinc (a * x)))
  have he := h.integral_eq
  simp only [Function.comp_apply, ← mul_assoc] at he
  rw [he, scalarPitman_endpoint_sinc W₄ hB hI (a * Real.sqrt t)]
  congr 1
  rw [mul_pow, Real.sq_sqrt (NNReal.coe_nonneg t)]

/-- Helper toward Lemma 4.11: the Euclidean radius commutes with every
nonnegative scalar dilation, including dilation by zero. -/
theorem sqrt_sum_three_sq_const_mul (c : ℝ) (hc : 0 ≤ c) (x : Fin 3 → ℝ) :
    Real.sqrt ((c * x 0)^2 + (c * x 1)^2 + (c * x 2)^2) =
      c * Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2) := by
  calc
    _ = Real.sqrt (c ^ 2 * ((x 0)^2 + (x 1)^2 + (x 2)^2)) := by
      congr 1
      ring
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- Helper toward Lemma 4.11: the radial Gaussian marginal at each time
is the square-root time dilation of its time-one marginal, including time zero. -/
theorem radial3_eval_identDistrib_scale
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (t : ℝ≥0) :
    IdentDistrib (fun p => radial3Path (firstThreePath p) t)
      (fun p => Real.sqrt t * radial3Path (firstThreePath p) 1) W₄ W₄ := by
  have hm (i : Fin 3) : Measurable
      (fun p : C(ℝ≥0, Fin 4 → ℝ) => Real.sqrt t * p 1 i.castSucc) :=
    measurable_const.mul ((measurable_pi_apply i.castSucc).comp
      (continuous_eval_const (1 : ℝ≥0)).measurable)
  have hi := (hI.precomp (Fin.castSucc_injective 3)).comp
    (fun _ : Fin 3 => fun f : C(ℝ≥0, ℝ) => Real.sqrt t * f 1)
    (fun _ => measurable_const.mul (continuous_eval_const (1 : ℝ≥0)).measurable)
  have hl : HasLaw (fun p (i : Fin 3) => Real.sqrt t * p 1 i.castSucc)
      (Measure.pi (fun _ : Fin 3 => gaussianReal 0 t)) W₄ := by
    refine ⟨(measurable_pi_iff.mpr hm).aemeasurable, ?_⟩
    rw [hi.map_fun_eq_pi_map (fun i => (hm i).aemeasurable)]
    congr 1
    funext i
    have he := (gaussianReal_const_mul ((hB i.castSucc).hasLaw_eval 1) (Real.sqrt t)).map_eq
    have hv : NNReal.mk ((Real.sqrt t) ^ 2) (sq_nonneg _) = t := by
      apply NNReal.coe_injective
      exact Real.sq_sqrt (NNReal.coe_nonneg t)
    simpa only [mul_zero, mul_one, hv] using he
  have hr := (hasLaw_map (by fun_prop : AEMeasurable
    (fun x : Fin 3 → ℝ => Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2))
      (Measure.pi (fun _ : Fin 3 => gaussianReal 0 t)))).comp hl
  have he : (fun p : C(ℝ≥0, Fin 4 → ℝ) =>
      Real.sqrt ((Real.sqrt t * p 1 0)^2 + (Real.sqrt t * p 1 1)^2 +
        (Real.sqrt t * p 1 2)^2)) =
      (fun p => Real.sqrt t * radial3Path (firstThreePath p) 1) := by
    funext p
    exact sqrt_sum_three_sq_const_mul _ (Real.sqrt_nonneg _) (fun i => p 1 i.castSucc)
  change HasLaw (fun p => Real.sqrt ((Real.sqrt t * p 1 0)^2 +
    (Real.sqrt t * p 1 1)^2 + (Real.sqrt t * p 1 2)^2)) _ W₄ at hr
  rw [he] at hr
  exact ⟨(radial3_hasLaw_eval W₄ hB hI t).aemeasurable, hr.aemeasurable,
    (radial3_hasLaw_eval W₄ hB hI t).map_eq.trans hr.map_eq.symm⟩

/-- Helper toward Lemma 4.11: at every nonnegative time, the scalar Pitman
transform of Brownian coordinate zero has the three-dimensional radial
Gaussian marginal. This asserts equality of one-time laws only. -/
theorem scalarPitman_radial3_identDistrib_eval
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (t : ℝ≥0) :
    IdentDistrib (fun p => scalarPitman (pathCoordinate p 0) t)
      (fun p => radial3Path (firstThreePath p) t) W₄ W₄ := by
  by_cases ht : t = 0
  · subst t
    refine ⟨((continuous_eval_const 0).comp
      (continuous_scalarPitman.comp (continuous_pathCoordinate 0))).measurable.aemeasurable,
      (radial3_hasLaw_eval W₄ hB hI 0).aemeasurable, Measure.map_congr ?_⟩
    filter_upwards [(hB 0).eval_zero_ae_eq_zero,
      (hB 1).eval_zero_ae_eq_zero, (hB 2).eval_zero_ae_eq_zero] with p hp₀ hp₁ hp₂
    change p 0 0 - 2 * sInf ((pathCoordinate p 0) '' Set.Icc 0 0) =
      Real.sqrt ((p 0 0)^2 + (p 0 1)^2 + (p 0 2)^2)
    simp [Set.Icc_self, hp₀, hp₁, hp₂, pathCoordinate]
  · exact (scalarPitman_eval_identDistrib_scale W₄ (hB 0) t ht).trans
      (((scalarPitman_endpoint_identDistrib_radial3 W₄ hB hI).comp
        (by fun_prop : Measurable (fun x : ℝ => Real.sqrt t * x))).trans
          (radial3_eval_identDistrib_scale W₄ hB hI t).symm)

/-- Helper toward Lemma 4.11: the cosine transform of the radius of three
independent standard Gaussian coordinates. -/
theorem integral_cos_gaussian_radial3 (a : ℝ) :
    (∫ x : Fin 3 → ℝ,
      Real.cos (a * Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2))
        ∂Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)) =
      (1 - a ^ 2) * Real.exp (-(a ^ 2) / 2) := by
  let ν := (gaussianReal 0 1).withDensity (fun x : ℝ => ENNReal.ofReal (x ^ 2))
  have hν : IsProbabilityMeasure ν := isProbabilityMeasure_gaussian_sq_weighted
  have he := congrArg (fun ρ : Measure ℝ => ∫ r, Real.cos (a * r) ∂ρ)
    gaussian_sq_weighted_abs_eq_radial3
  rw [integral_map (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) (by fun_prop)] at he
  rw [← he]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun x : ℝ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
  have hc (x : ℝ) : Real.cos (a * |x|) = Real.cos (a * x) := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg (lt_of_not_ge hx), mul_neg, Real.cos_neg]
  simp_rw [hc]
  exact gaussian_sq_cos a

/-- Helper toward Lemma 4.11: the sinc transform of the radius of three
independent standard Gaussians is exactly `exp (-a²/2)` at every real frequency. -/
theorem integral_sinc_gaussian_radial3 (a : ℝ) :
    (∫ x : Fin 3 → ℝ,
      Real.sinc (a * Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2))
        ∂Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)) =
      Real.exp (-(a ^ 2) / 2) := by
  let μ := (Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)).map
    (fun x => Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2))
  have hμ : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  have hc (b : ℝ) : (∫ r, Real.cos (b * r) ∂μ) =
      (1 - b ^ 2) * Real.exp (-(b ^ 2) / 2) := by
    rw [show μ = _ from rfl, integral_map (by fun_prop) (by fun_prop)]
    exact integral_cos_gaussian_radial3 b
  let F (b : ℝ) := b * (∫ r, Real.sinc (b * r) ∂μ) - b * Real.exp (-(b ^ 2) / 2)
  have hd (b : ℝ) : HasDerivAt F 0 b := by
    have hs := OneTimeSinc.hasDerivAt_integral_mul_sinc μ b
    rw [hc b] at hs
    have he : HasDerivAt (fun c : ℝ => c * Real.exp (-(c ^ 2) / 2))
        ((1 - b ^ 2) * Real.exp (-(b ^ 2) / 2)) b := by
      convert (hasDerivAt_id' b).mul ((((hasDerivAt_id' b).pow 2).neg.div_const 2).exp)
        using 1
      dsimp only [Pi.pow_apply, Pi.neg_apply]
      ring
    simpa only [F, sub_self] using hs.fun_sub he
  have hF : F a = F 0 := is_const_of_deriv_eq_zero
    (fun b => (hd b).differentiableAt) (fun b => (hd b).deriv) a 0
  have hz : F 0 = 0 := by simp only [F, zero_mul, sub_self]
  rw [hz] at hF
  have hs : (∫ r, Real.sinc (a * r) ∂μ) = Real.exp (-(a ^ 2) / 2) := by
    by_cases ha : a = 0
    · subst a
      simp
    · apply (mul_left_cancel₀ ha)
      exact sub_eq_zero.mp hF
  rw [show μ = _ from rfl, integral_map (by fun_prop) (by fun_prop)] at hs
  exact hs

end DirectedDistances.Probability
