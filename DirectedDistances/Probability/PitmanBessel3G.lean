/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.PitmanBessel3F

/-! Supporting lemmas for paper labels `lem-cond-walk-bm` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.Probability
open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.RandomWalk
open scoped NNReal Topology

local instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    MeasurableSpace C(X, Y) := borel _
local instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    BorelSpace C(X, Y) := ⟨rfl⟩

/-- Helper toward Lemma 4.11: the explicit cosine transform of the scalar
Pitman endpoint at time one. The proof requires no moment bound on that endpoint. -/
theorem scalarPitman_endpoint_cos
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄) (a : ℝ) :
    (∫ p, Real.cos (a * scalarPitman (pathCoordinate p 0) 1) ∂W₄) =
      (1 - a ^ 2) * Real.exp (-(a ^ 2) / 2) := by
  let R (p : C(ℝ≥0, Fin 4 → ℝ)) := scalarPitman (pathCoordinate p 0) 1
  have hR : Measurable R := ((continuous_eval_const (1 : ℝ≥0)).comp
    (continuous_scalarPitman.comp (continuous_pathCoordinate 0))).measurable
  have hs (b : ℝ) : (∫ r, Real.sinc (b * r) ∂W₄.map R) = Real.exp (-(b ^ 2) / 2) := by
    rw [integral_map hR.aemeasurable (by fun_prop)]
    exact scalarPitman_endpoint_sinc W₄ hB hI b
  have hd := hasDerivAt_integral_mul_sinc (W₄.map R) a
  simp_rw [hs] at hd
  have he : HasDerivAt (fun b : ℝ => b * Real.exp (-(b ^ 2) / 2))
      ((1 - a ^ 2) * Real.exp (-(a ^ 2) / 2)) a := by
    convert (hasDerivAt_id' a).mul ((((hasDerivAt_id' a).pow 2).neg.div_const 2).exp) using 1
    dsimp only [Pi.pow_apply, Pi.neg_apply]
    ring
  have hh := hd.unique he
  rw [integral_map hR.aemeasurable (by fun_prop)] at hh
  exact hh

private theorem gaussian_cos (a : ℝ) :
    (∫ x : ℝ, Real.cos (a * x) ∂gaussianReal 0 1) = Real.exp (-(a ^ 2) / 2) := by
  have hi : Integrable (fun x : ℝ => Complex.exp ((a : ℂ) * x * Complex.I))
      (gaussianReal 0 1) := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
    exact Filter.Eventually.of_forall (fun x => by simp [Complex.norm_exp])
  have hc := congrArg Complex.re (charFun_gaussianReal (μ := 0) (v := 1) a)
  rw [charFun_apply_real] at hc
  have hire := integral_re hi
  change (∫ x : ℝ, (Complex.exp ((a : ℂ) * x * Complex.I)).re ∂gaussianReal 0 1) =
    (∫ x : ℝ, Complex.exp ((a : ℂ) * x * Complex.I) ∂gaussianReal 0 1).re at hire
  rw [← hire] at hc
  simpa [← Complex.ofReal_pow, Complex.exp_re, neg_div] using hc

private theorem gaussian_id_integrable :
    Integrable (fun x : ℝ => x) (gaussianReal 0 1) := by
  exact (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)

private theorem gaussian_sq_integrable :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := by
  exact (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq

private theorem gaussian_sin_first_moment (a : ℝ) :
    (∫ x : ℝ, -(x * Real.sin (a * x)) ∂gaussianReal 0 1) =
      -a * Real.exp (-(a ^ 2) / 2) := by
  have hi : Integrable (fun x : ℝ => Real.cos (a * x)) (gaussianReal 0 1) := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
    exact Filter.Eventually.of_forall (fun x => Real.abs_cos_le_one (a * x))
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := fun b x : ℝ => Real.cos (b * x))
    (F' := fun b x : ℝ => -(x * Real.sin (b * x))) (bound := fun x : ℝ => |x|)
    (s := Set.univ) (x₀ := a) Filter.univ_mem
    (Filter.Eventually.of_forall (fun _ => by fun_prop)) hi (by fun_prop)
    (Filter.Eventually.of_forall (fun x b _ => by
      simpa only [Real.norm_eq_abs, abs_neg, abs_mul, mul_one] using
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (b * x)) (abs_nonneg x)))
    gaussian_id_integrable.abs
    (Filter.Eventually.of_forall (fun x b _ => by
      convert ((hasDerivAt_id' b).mul_const x).cos using 1; ring))
  have he : HasDerivAt (fun b : ℝ => Real.exp (-(b ^ 2) / 2))
      (-a * Real.exp (-(a ^ 2) / 2)) a := by
    convert (((hasDerivAt_id' a).pow 2).neg.div_const 2).exp using 1
    dsimp only [Pi.pow_apply, Pi.neg_apply]
    ring
  have hh := hd.2
  simp_rw [gaussian_cos] at hh
  exact hh.unique he

/-- Helper toward Lemma 4.11: weighting a standard Gaussian by its squared
coordinate gives the same cosine transform as the scalar Pitman endpoint. -/
theorem gaussian_sq_cos (a : ℝ) :
    (∫ x : ℝ, x ^ 2 * Real.cos (a * x) ∂gaussianReal 0 1) =
      (1 - a ^ 2) * Real.exp (-(a ^ 2) / 2) := by
  have hi : Integrable (fun x : ℝ => -(x * Real.sin (a * x))) (gaussianReal 0 1) := by
    apply Integrable.mono' gaussian_id_integrable.abs (by fun_prop)
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_neg, abs_mul, mul_one] using
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (a * x)) (abs_nonneg x)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := fun b x : ℝ => -(x * Real.sin (b * x)))
    (F' := fun b x : ℝ => -(x ^ 2 * Real.cos (b * x))) (bound := fun x : ℝ => x ^ 2)
    (s := Set.univ) (x₀ := a) Filter.univ_mem
    (Filter.Eventually.of_forall (fun _ => by fun_prop)) hi (by fun_prop)
    (Filter.Eventually.of_forall (fun x b _ => by
      simpa only [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg x), mul_one] using
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (b * x)) (sq_nonneg x)))
    gaussian_sq_integrable
    (Filter.Eventually.of_forall (fun x b _ => by
      convert ((((hasDerivAt_id' b).mul_const x).sin).const_mul x).neg using 1; ring))
  have he : HasDerivAt (fun b : ℝ => -b * Real.exp (-(b ^ 2) / 2))
      (-(1 - a ^ 2) * Real.exp (-(a ^ 2) / 2)) a := by
    convert (hasDerivAt_id' a).neg.mul ((((hasDerivAt_id' a).pow 2).neg.div_const 2).exp) using 1
    dsimp only [Pi.pow_apply, Pi.neg_apply]
    ring
  have hh := hd.2
  simp_rw [gaussian_sin_first_moment] at hh
  have hh' := hh.unique he
  rw [integral_neg] at hh'
  linarith only [hh']

/-- Helper toward Lemma 4.11: the squared-coordinate weighting of the
standard Gaussian is a probability measure, with its exact normalization. -/
theorem isProbabilityMeasure_gaussian_sq_weighted :
    IsProbabilityMeasure ((gaussianReal 0 1).withDensity (fun x : ℝ => ENNReal.ofReal (x ^ 2))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal gaussian_sq_integrable
      (Filter.Eventually.of_forall (fun x : ℝ => sq_nonneg x))]
  have h := gaussian_sq_cos 0
  simp only [zero_mul, Real.cos_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, sub_zero, neg_zero, zero_div, Real.exp_zero] at h
  rw [h, ENNReal.ofReal_one]

/-- Helper toward Lemma 4.11: the exact time-one Pitman law is the absolute
value pushforward of the squared-coordinate-weighted standard Gaussian.
This gives an explicit one-time law without assuming a radial identification. -/
theorem scalarPitman_endpoint_hasLaw_weightedGaussian
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄) :
    HasLaw (fun p => scalarPitman (pathCoordinate p 0) 1)
      (((gaussianReal 0 1).withDensity (fun x : ℝ => ENNReal.ofReal (x ^ 2))).map abs) W₄ := by
  let R (p : C(ℝ≥0, Fin 4 → ℝ)) := scalarPitman (pathCoordinate p 0) 1
  have hR : Measurable R := ((continuous_eval_const (1 : ℝ≥0)).comp
    (continuous_scalarPitman.comp (continuous_pathCoordinate 0))).measurable
  let ν := (gaussianReal 0 1).withDensity (fun x : ℝ => ENNReal.ofReal (x ^ 2))
  have : IsProbabilityMeasure ν := isProbabilityMeasure_gaussian_sq_weighted
  refine ⟨hR.aemeasurable, ?_⟩
  apply measure_eq_of_integral_cos_eq_of_nonneg (W₄.map R) (ν.map abs)
  · apply (ae_map_iff hR.aemeasurable measurableSet_Ici).mpr
    exact (scalarPitman_nonneg_ae W₄ (hB 0)).mono (fun p hp => hp 1)
  · apply (ae_map_iff (by fun_prop) measurableSet_Ici).mpr
    exact Filter.Eventually.of_forall abs_nonneg
  · intro a
    rw [integral_map hR.aemeasurable (by fun_prop),
      scalarPitman_endpoint_cos W₄ hB hI a,
      integral_map (by fun_prop : AEMeasurable (abs : ℝ → ℝ) ν) (by fun_prop)]
    change _ = ∫ x, Real.cos (a * |x|) ∂(gaussianReal 0 1).withDensity _
    rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall (fun x : ℝ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
    have hc (x : ℝ) : Real.cos (a * |x|) = Real.cos (a * x) := by
      by_cases hx : 0 ≤ x
      · rw [abs_of_nonneg hx]
      · rw [abs_of_neg (lt_of_not_ge hx), mul_neg, Real.cos_neg]
    simp_rw [hc]
    exact (gaussian_sq_cos a).symm

private theorem gaussian_square_charFun_quadratic (a : ℝ) :
    (1 - 2 * (a : ℂ) * Complex.I) *
      (∫ x : ℝ, Complex.exp ((a : ℂ) * x ^ 2 * Complex.I) ∂gaussianReal 0 1) ^ 2 = 1 := by
  let b : ℂ := 1 / 2 - (a : ℂ) * Complex.I
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  have hb : 0 < b.re := by simp [b]
  have hi : (∫ x : ℝ, Complex.exp ((a : ℂ) * x ^ 2 * Complex.I) ∂gaussianReal 0 1) =
      (c : ℂ) * ∫ x : ℝ, Complex.exp (-b * (x : ℂ) ^ 2) := by
    rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero,
      Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_exp,
      Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_ofNat]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    · simp only [c, Complex.ofReal_inv]
    · dsimp [b]
      ring
  rw [hi, mul_pow, integral_gaussian_sq_complex hb]
  have hc : (c : ℂ) ^ 2 * (2 * Real.pi) = 1 := by
    have hr : c ^ 2 * (2 * Real.pi) = 1 := by
      dsimp [c]
      rw [inv_pow, Real.sq_sqrt (by positivity)]
      exact inv_mul_cancel₀ (by positivity)
    exact_mod_cast hr
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  have he : (1 - 2 * (a : ℂ) * Complex.I) = 2 * b := by dsimp [b]; ring
  rw [he]
  calc
    (2 * b) * ((c : ℂ) ^ 2 * (Real.pi / b)) = (c : ℂ) ^ 2 * (2 * Real.pi) := by
      field_simp [hb0]
    _ = 1 := hc

/-- Helper toward Lemma 4.11: the square under the squared-coordinate-weighted
Gaussian law has the characteristic function of the sum of three independent
standard Gaussian squares. -/
theorem gaussian_sq_weighted_square_charFun (a : ℝ) :
    (∫ x : ℝ, (x : ℂ) ^ 2 * Complex.exp ((a : ℂ) * x ^ 2 * Complex.I) ∂gaussianReal 0 1) =
      (∫ x : ℝ, Complex.exp ((a : ℂ) * x ^ 2 * Complex.I) ∂gaussianReal 0 1) ^ 3 := by
  let H (b : ℝ) := ∫ x : ℝ, Complex.exp ((b : ℂ) * x ^ 2 * Complex.I) ∂gaussianReal 0 1
  let J := ∫ x : ℝ, (x : ℂ) ^ 2 * Complex.exp ((a : ℂ) * x ^ 2 * Complex.I) ∂gaussianReal 0 1
  have hi : Integrable (fun x : ℝ => Complex.exp ((a : ℂ) * x ^ 2 * Complex.I))
      (gaussianReal 0 1) := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
    exact Filter.Eventually.of_forall (fun x => by simp [Complex.norm_exp, ← Complex.ofReal_pow])
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1)
    (F := fun b x : ℝ => Complex.exp ((b : ℂ) * x ^ 2 * Complex.I))
    (F' := fun b x : ℝ => Complex.I * (x : ℂ) ^ 2 * Complex.exp ((b : ℂ) * x ^ 2 * Complex.I))
    (bound := fun x : ℝ => x ^ 2) (s := Set.univ) (x₀ := a) Filter.univ_mem
    (Filter.Eventually.of_forall (fun _ => by fun_prop)) hi (by fun_prop)
    (Filter.Eventually.of_forall (fun x b _ => by
      simp [Complex.norm_exp, Complex.norm_real, norm_pow, sq_abs, ← Complex.ofReal_pow]))
    gaussian_sq_integrable
    (Filter.Eventually.of_forall (fun x b _ => by
      convert ((((hasDerivAt_id' (b : ℂ)).mul_const ((x : ℂ) ^ 2)).mul_const Complex.I).cexp).comp_ofReal using 1; ring))
  have hH : HasDerivAt H (Complex.I * J) a := by
    simpa only [H, J, mul_assoc, integral_const_mul] using hd.2
  have hQ : HasDerivAt (fun b : ℝ => 1 - 2 * (b : ℂ) * Complex.I) (-2 * Complex.I) a := by
    convert ((((hasDerivAt_id' (a : ℂ)).const_mul 2).mul_const Complex.I).const_sub 1).comp_ofReal using 1; ring
  have hp := hQ.mul (hH.pow 2)
  have hpoly (b : ℝ) : (1 - 2 * (b : ℂ) * Complex.I) * H b ^ 2 = 1 :=
    gaussian_square_charFun_quadratic b
  change HasDerivAt (fun b : ℝ => (1 - 2 * (b : ℂ) * Complex.I) * H b ^ 2) _ a at hp
  simp_rw [hpoly] at hp
  have hz := hp.unique (hasDerivAt_const a (1 : ℂ))
  simp only [Pi.pow_apply] at hz
  have hza : (2 * Complex.I) * (J - H a ^ 3) = 0 := by
    linear_combination H a * hz - (2 * Complex.I * J) * hpoly a
  have he := (mul_eq_zero.mp hza).resolve_left (by norm_num)
  exact sub_eq_zero.mp he

/-- Helper toward Lemma 4.11: the absolute value of a standard Gaussian
weighted by its squared coordinate has exactly the three-dimensional
standard Gaussian radial law. -/
theorem gaussian_sq_weighted_abs_eq_radial3 :
    (((gaussianReal 0 1).withDensity (fun x : ℝ => ENNReal.ofReal (x ^ 2))).map abs) =
      (Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)).map
        (fun x => Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2)) := by
  let ν := (gaussianReal 0 1).withDensity (fun x : ℝ => ENNReal.ofReal (x ^ 2))
  have : IsProbabilityMeasure ν := isProbabilityMeasure_gaussian_sq_weighted
  have hsq : Measurable (fun x : Fin 3 → ℝ => ∑ i, (x i) ^ 2) :=
    Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).pow_const 2)
  have hs : ν.map (fun x => x ^ 2) =
      (Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)).map (fun x => ∑ i, (x i) ^ 2) := by
    apply Measure.ext_of_charFun
    funext a
    rw [charFun_apply_real, charFun_apply_real,
      integral_map (by fun_prop) (by fun_prop), integral_map hsq.aemeasurable (by fun_prop)]
    change (∫ x, Complex.exp ((a : ℂ) * (x ^ 2 : ℝ) * Complex.I)
      ∂(gaussianReal 0 1).withDensity _) = _
    rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall (fun x : ℝ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (sq_nonneg _), Complex.real_smul, Complex.ofReal_pow]
    rw [gaussian_sq_weighted_square_charFun]
    have he (x : Fin 3 → ℝ) :
        Complex.exp ((a : ℂ) * (∑ i, x i ^ 2 : ℝ) * Complex.I) =
          ∏ i, Complex.exp ((a : ℂ) * (x i : ℂ) ^ 2 * Complex.I) := by
      rw [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul, Complex.exp_sum]
      simp only [Complex.ofReal_pow]
    simp_rw [he]
    rw [integral_fintype_prod_eq_prod (fun (_ : Fin 3) (x : ℝ) =>
      Complex.exp ((a : ℂ) * x ^ 2 * Complex.I))]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h := congrArg (Measure.map Real.sqrt) hs
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) hsq] at h
  simpa [ν, Function.comp_def, Real.sqrt_sq_eq_abs, Fin.sum_univ_succ, add_assoc] using h

/-- Helper toward Lemma 4.11: Pitman's transform of Brownian coordinate zero
at time one has the same law as the radius of the first three independent
Brownian coordinates. This is a one-time statement, not the full path theorem. -/
theorem scalarPitman_endpoint_identDistrib_radial3
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄) :
    IdentDistrib (fun p => scalarPitman (pathCoordinate p 0) 1)
      (fun p => radial3Path (firstThreePath p) 1) W₄ W₄ := by
  have hm (i : Fin 3) : Measurable (fun p : C(ℝ≥0, Fin 4 → ℝ) => p 1 i.castSucc) :=
    (measurable_pi_apply i.castSucc).comp (continuous_eval_const (1 : ℝ≥0)).measurable
  have hi := (hI.precomp (Fin.castSucc_injective 3)).comp
    (fun _ : Fin 3 => fun f : C(ℝ≥0, ℝ) => f 1)
    (fun _ => (continuous_eval_const (1 : ℝ≥0)).measurable)
  have hl : HasLaw (fun p (i : Fin 3) => p 1 i.castSucc)
      (Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)) W₄ := by
    refine ⟨(measurable_pi_iff.mpr hm).aemeasurable, ?_⟩
    rw [hi.map_fun_eq_pi_map (fun i => (hm i).aemeasurable)]
    congr 1
    funext i
    exact (hB i.castSucc).hasLaw_eval 1 |>.map_eq
  have hr := (hasLaw_map (by fun_prop : AEMeasurable
    (fun x : Fin 3 → ℝ => Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2))
    (Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)))).comp hl
  have hp := scalarPitman_endpoint_hasLaw_weightedGaussian W₄ hB hI
  refine ⟨hp.aemeasurable, hr.aemeasurable, ?_⟩
  exact hp.map_eq.trans (gaussian_sq_weighted_abs_eq_radial3.trans hr.map_eq.symm)

/-- Helper toward Lemma 4.11: the standard Brownian space-time rescaling
of a scalar continuous path, defined at every nonnegative scale. -/
@[expose] noncomputable def pitmanRescaledPath (τ : ℝ≥0) (f : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) :=
  ⟨fun s => (Real.sqrt τ)⁻¹ * f (τ * s),
    continuous_const.mul (f.continuous.comp (continuous_const.mul continuous_id))⟩

/-- Helper toward Lemma 4.11: rescaling is continuous as a map on paths. -/
theorem continuous_pitmanRescaledPath (τ : ℝ≥0) : Continuous (pitmanRescaledPath τ) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_const.mul (continuous_eval.comp
    (continuous_fst.prodMk (continuous_const.mul continuous_snd)))

/-- Helper toward Lemma 4.11: the scalar Pitman transform commutes with
Brownian rescaling at positive scales, including its running minimum. -/
theorem scalarPitman_rescaled_one (τ : ℝ≥0) (hτ : τ ≠ 0) (f : C(ℝ≥0, ℝ)) :
    scalarPitman (pitmanRescaledPath τ f) 1 =
      (Real.sqrt τ)⁻¹ * scalarPitman f τ := by
  let g : C(ℝ≥0, ℝ) := ⟨fun s => f (τ * s), f.continuous.comp (continuous_const.mul continuous_id)⟩
  have himage : (fun s : ℝ≥0 => f (τ * s)) '' Set.Icc 0 1 = f '' Set.Icc 0 τ := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨τ * s, ⟨zero_le, by simpa only [mul_one] using mul_le_mul_of_nonneg_left hs.2 (show (0 : ℝ≥0) ≤ τ from zero_le)⟩, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u / τ, ⟨zero_le, (div_le_one (pos_of_ne_zero hτ)).mpr hu.2⟩, ?_⟩
      change f (τ * (u / τ)) = f u
      rw [mul_div_cancel₀ _ hτ]
  have hm := runningMinimum_const_mul g (Real.sqrt τ)⁻¹ (by positivity) 1
  change continuousRunningMinimum (pitmanRescaledPath τ f) 1 = _ at hm
  have hg : continuousRunningMinimum g 1 = continuousRunningMinimum f τ := by
    change sInf ((fun s : ℝ≥0 => f (τ * s)) '' Set.Icc 0 1) = sInf (f '' Set.Icc 0 τ)
    rw [himage]
  rw [hg] at hm
  change (Real.sqrt τ)⁻¹ * f (τ * 1) - 2 * continuousRunningMinimum (pitmanRescaledPath τ f) 1 =
    (Real.sqrt τ)⁻¹ * (f τ - 2 * continuousRunningMinimum f τ)
  rw [hm, mul_one]
  ring

/-- Helper toward Lemma 4.11: Brownian self-similarity transfers the scalar
Pitman marginal at every positive time to its time-one marginal. -/
theorem scalarPitman_rescaled_identDistrib
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t 0) W₄)
    (τ : ℝ≥0) (hτ : τ ≠ 0) :
    IdentDistrib (fun p => (Real.sqrt τ)⁻¹ * scalarPitman (pathCoordinate p 0) τ)
      (fun p => scalarPitman (pathCoordinate p 0) 1) W₄ W₄ := by
  have h := brownianScalarPath_identDistrib
    ((continuous_pitmanRescaledPath τ).comp (continuous_pathCoordinate 0)).measurable
    (continuous_pathCoordinate 0).measurable (hB.smul hτ) hB
  have he := (h.comp continuous_scalarPitman.measurable).comp
    (continuous_eval_const (1 : ℝ≥0)).measurable
  simpa only [Function.comp_def, scalarPitman_rescaled_one τ hτ] using he

private theorem sqrt_three_smul (c x y z : ℝ) (hc : 0 ≤ c) :
    Real.sqrt ((c * x) ^ 2 + (c * y) ^ 2 + (c * z) ^ 2) =
      c * Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) := by
  have he : (c * x) ^ 2 + (c * y) ^ 2 + (c * z) ^ 2 =
      c ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2) := by ring
  rw [he, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- Helper toward Lemma 4.11: every one-time scalar Pitman marginal is the
three-dimensional Brownian radial marginal, including the degenerate time zero.
This does not assert equality of multi-time or entire-path laws. -/
theorem scalarPitman_eval_identDistrib_radial3
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄) (τ : ℝ≥0) :
    IdentDistrib (fun p => scalarPitman (pathCoordinate p 0) τ)
      (fun p => radial3Path (firstThreePath p) τ) W₄ W₄ := by
  by_cases hτ : τ = 0
  · subst τ
    apply IdentDistrib.of_ae_eq (((continuous_eval_const (0 : ℝ≥0)).comp
      (continuous_scalarPitman.comp (continuous_pathCoordinate 0))).measurable.aemeasurable)
    filter_upwards [(hB 0).eval_zero_ae_eq_zero, (hB 1).eval_zero_ae_eq_zero,
      (hB 2).eval_zero_ae_eq_zero] with p h0 h1 h2
    change p 0 0 - 2 * sInf ((fun t : ℝ≥0 => p t 0) '' Set.Icc 0 0) =
      Real.sqrt ((p 0 0)^2 + (p 0 1)^2 + (p 0 2)^2)
    simp only [Set.Icc_self, Set.image_singleton, csInf_singleton, h0, h1, h2]
    norm_num
  let c : ℝ := (Real.sqrt τ)⁻¹
  have hm (i : Fin 3) : Measurable
      (fun p : C(ℝ≥0, Fin 4 → ℝ) => c * p τ i.castSucc) :=
    measurable_const.mul ((measurable_pi_apply i.castSucc).comp (continuous_eval_const τ).measurable)
  have hi := (hI.precomp (Fin.castSucc_injective 3)).comp
    (fun _ : Fin 3 => fun f : C(ℝ≥0, ℝ) => c * f τ)
    (fun _ => measurable_const.mul (continuous_eval_const τ).measurable)
  have hl : HasLaw (fun p (i : Fin 3) => c * p τ i.castSucc)
      (Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)) W₄ := by
    refine ⟨(measurable_pi_iff.mpr hm).aemeasurable, ?_⟩
    rw [hi.map_fun_eq_pi_map (fun i => (hm i).aemeasurable)]
    congr 1
    funext i
    simpa only [mul_one] using ((hB i.castSucc).smul hτ).hasLaw_eval 1 |>.map_eq
  have hr := (hasLaw_map (by fun_prop : AEMeasurable
    (fun x : Fin 3 → ℝ => Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2))
    (Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)))).comp hl
  have hr' : HasLaw (fun p => c * radial3Path (firstThreePath p) τ)
      ((Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)).map
        (fun x => Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2))) W₄ := by
    simpa only [radial3Path, firstThreePath, ContinuousMap.coe_mk, Function.comp_def,
      sqrt_three_smul c _ _ _ (by positivity)] using hr
  have hp := scalarPitman_endpoint_hasLaw_weightedGaussian W₄ hB hI
  have hid : IdentDistrib (fun p => scalarPitman (pathCoordinate p 0) 1)
      (fun p => c * radial3Path (firstThreePath p) τ) W₄ W₄ :=
    ⟨hp.aemeasurable, hr'.aemeasurable,
      hp.map_eq.trans (gaussian_sq_weighted_abs_eq_radial3.trans hr'.map_eq.symm)⟩
  have hh := ((scalarPitman_rescaled_identDistrib W₄ (hB 0) τ hτ).trans hid).const_mul (Real.sqrt τ)
  have hs : Real.sqrt (τ : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast pos_of_ne_zero hτ)
  simpa only [c, ← mul_assoc, mul_inv_cancel₀ hs, one_mul] using hh
































end DirectedDistances.Probability
