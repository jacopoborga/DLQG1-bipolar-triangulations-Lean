/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.PitmanBessel3D
public import DirectedDistances.RandomWalk.IIDWalkFunctionalConvergence

/-! Helper toward Lemma 4.11: the Brownian side of the discrete approximation
route, with the source variance `2/3` removed explicitly. No radial limit is
assumed. All path topologies below are locally uniform. -/

public section
namespace DirectedDistances.Probability
open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.RandomWalk
open scoped NNReal Topology

local instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    MeasurableSpace C(X, Y) := borel _
local instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    BorelSpace C(X, Y) := ⟨rfl⟩
local instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [LocallyCompactSpace X] [SecondCountableTopology Y] :
    SecondCountableTopology C(X, Y) := continuousPath_secondCountable

/-- Helper toward Lemma 4.11: normalize the first source coordinate to
variance one. The positive factor is fixed across all times and scales. -/
@[expose] noncomputable def standardFirstPath (f : C(ℝ≥0, ℝ × ℝ)) : C(ℝ≥0, ℝ) :=
  ⟨fun t => (f t).1 / Real.sqrt (2 / 3), f.continuous.fst.div_const _⟩

/-- Helper toward Lemma 4.11: normalization is continuous on entire paths. -/
theorem continuous_standardFirstPath : Continuous standardFirstPath := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.fst.div_const _

/-- Helper toward Lemma 4.11: the normalized candidate is exactly coordinate
zero of the four-coordinate Brownian realization. -/
theorem standardFirstPath_iidBrownianPath (p : C(ℝ≥0, Fin 4 → ℝ)) :
    standardFirstPath (iidBrownianPath p) = pathCoordinate p 0 := by
  ext t
  change Real.sqrt (2 / 3) * p t 0 / Real.sqrt (2 / 3) = p t 0
  exact mul_div_cancel_left₀ _ (by positivity)

/-- Helper toward Lemma 4.11: normalization commutes with the first coordinate
of the vector Pitman transform, as an identity of entire continuous paths. -/
theorem standardFirstPath_vectorPitman (f : C(ℝ≥0, ℝ × ℝ)) :
    standardFirstPath (continuousVectorPitman f) = scalarPitman (standardFirstPath f) := by
  let g : C(ℝ≥0, ℝ) := ⟨fun t => (f t).1, f.continuous.fst⟩
  ext t
  have hm := runningMinimum_const_mul g (Real.sqrt (2 / 3))⁻¹ (by positivity) t
  change ((f t).1 - 2 * sInf ((fun s => (f s).1) '' Set.Icc 0 t)) /
    Real.sqrt (2 / 3) = (f t).1 / Real.sqrt (2 / 3) -
      2 * sInf ((fun s => (f s).1 / Real.sqrt (2 / 3)) '' Set.Icc 0 t)
  simp only [g, ContinuousMap.coe_mk, continuousRunningMinimum_apply,
    ← div_eq_inv_mul] at hm
  rw [hm]
  ring

/-- Helper toward Lemma 4.11: the normalized scalar walk and its continuous
Pitman transform converge jointly as entire paths. Brownian identification of
the first component is proved; the second is still the scalar Pitman image. -/
theorem codeWalk_scalarPitman_joint_functional_tendsto
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄) :
    TendstoInDistribution (fun n ω =>
      (standardFirstPath (diffusiveInterpolation n (codeWalk ω)),
        scalarPitman (standardFirstPath (diffusiveInterpolation n (codeWalk ω))))) atTop
      (fun p => (pathCoordinate p 0, scalarPitman (pathCoordinate p 0)))
      (fun _ => iidCodeMeasure) W₄ := by
  have h := TendstoInDistribution.continuous_comp
    (continuous_standardFirstPath.prodMk
      (continuous_scalarPitman.comp continuous_standardFirstPath))
    (codeWalk_interpolation_functional_tendsto W₄ hB hI)
  simpa only [Function.comp_def, standardFirstPath_iidBrownianPath] using h

private theorem inv_sqrt_nat_tendsto :
    Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

/-- Helper toward Lemma 4.11: the actual discrete original and Pitman
endpoints converge jointly to the Brownian endpoint and scalar Pitman endpoint.
This is the continuous-limit side of the finite probability difference formula
in `PitmanBessel3D`, with no assumption of a BES(3) law. -/
theorem codeWalk_scalarPitman_joint_endpoint_tendsto
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄) :
    TendstoInDistribution (fun n ω =>
      (((codeWalk ω n).1 : ℝ) / Real.sqrt n / Real.sqrt (2 / 3),
        ((vectorPitman (codeWalk ω) n).1 : ℝ) / Real.sqrt n / Real.sqrt (2 / 3))) atTop
      (fun p => (p 1 0, scalarPitman (pathCoordinate p 0) 1))
      (fun _ => iidCodeMeasure) W₄ := by
  let X (n : ℕ) (ω : ℕ → Fin 3) : ℝ × ℝ :=
    (standardFirstPath (diffusiveInterpolation n (codeWalk ω)) 1,
      scalarPitman (standardFirstPath (diffusiveInterpolation n (codeWalk ω))) 1)
  let Y (n : ℕ) (ω : ℕ → Fin 3) : ℝ × ℝ :=
    (((codeWalk ω n).1 : ℝ) / Real.sqrt n / Real.sqrt (2 / 3),
      ((vectorPitman (codeWalk ω) n).1 : ℝ) / Real.sqrt n / Real.sqrt (2 / 3))
  have hX : TendstoInDistribution X atTop
      (fun p => (p 1 0, scalarPitman (pathCoordinate p 0) 1))
      (fun _ => iidCodeMeasure) W₄ :=
    TendstoInDistribution.continuous_comp
      (((continuous_eval_const (1 : ℝ≥0)).comp continuous_fst).prodMk
        ((continuous_eval_const (1 : ℝ≥0)).comp continuous_snd))
      (codeWalk_scalarPitman_joint_functional_tendsto W₄ hB hI)
  have hY (n : ℕ) : Measurable (Y n) := by
    have hc := (measurable_pi_apply n).comp measurable_codeWalk
    have hv := (measurable_pi_apply n).comp
      (measurable_vectorPitmanPath.comp measurable_codeWalk)
    exact ((((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp hc.fst).div_const _).div_const _).prodMk
      ((((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp hv.fst).div_const _).div_const _)
  apply tendstoInDistribution_of_tendstoInMeasure_sub Y _ hX _ (fun n => (hY n).aemeasurable)
  apply tendstoInMeasure_of_tendsto_ae
    (fun n => ((hY n).aemeasurable.sub (hX.forall_aemeasurable n)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro ω
  have hb : Tendsto (fun n : ℕ => 3 / Real.sqrt n / Real.sqrt (2 / 3)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div, div_eq_mul_inv, zero_mul] using
      ((tendsto_const_nhds (x := (3 : ℝ))).mul inv_sqrt_nat_tendsto).div_const
        (Real.sqrt (2 / 3))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Pi.zero_apply, sub_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hb
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hg := diffusiveInterpolation_grid n hn (codeWalk ω) n
  have hs := diffusiveStep_grid n hn (vectorPitman (codeWalk ω)) n
  rw [div_self hn0] at hg hs
  have he := (diffusiveStep_vectorPitman_sub_abs_le n hn (codeWalk ω)
    (codeWalk_real_coord_increment_abs_le ω) 1).1
  rw [hs] at he
  have hp := congrArg (fun f : C(ℝ≥0, ℝ) => f 1)
    (standardFirstPath_vectorPitman (diffusiveInterpolation n (codeWalk ω)))
  change (continuousVectorPitman (diffusiveInterpolation n (codeWalk ω)) 1).1 /
    Real.sqrt (2 / 3) = _ at hp
  change ‖Y n ω - X n ω‖ ≤ _
  rw [Prod.norm_def]
  apply max_le
  · change |((codeWalk ω n).1 : ℝ) / Real.sqrt n / Real.sqrt (2 / 3) -
      (diffusiveInterpolation n (codeWalk ω) 1).1 / Real.sqrt (2 / 3)| ≤ _
    rw [hg, sub_self, abs_zero]
    positivity
  · change |((vectorPitman (codeWalk ω) n).1 : ℝ) / Real.sqrt n / Real.sqrt (2 / 3) -
      scalarPitman (standardFirstPath (diffusiveInterpolation n (codeWalk ω))) 1| ≤ _
    rw [← hp, ← sub_div, abs_div, abs_of_pos (show 0 < Real.sqrt (2 / 3 : ℝ) by positivity)]
    exact div_le_div_of_nonneg_right he (Real.sqrt_nonneg _)

private theorem sourceCode_independent :
    iIndepFun (fun i (ω : ℕ → Fin 3) => ω (i + 1)) iidCodeMeasure := by
  let g : ℤ × ℤ → Fin 3 := fun z => if z.1 = -1 then 0 else if z.1 = 0 then 1 else 2
  have hg (c : Fin 3) : g (lazyTwoDimensionalStep c) = c := by
    fin_cases c <;> simp [g, lazyTwoDimensionalStep]
  simpa only [Function.comp_def, codeWalk_succ_sub, hg] using
    iIndepFun_codeWalk_increments.comp (fun _ => g) (fun _ => measurable_of_countable g)

private theorem sourceCode_uniform (i : ℕ) :
    iidCodeMeasure.map (fun ω => ω (i + 1)) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin 3)) := by
  have he : MeasurableEmbedding lazyTwoDimensionalStep := by
    refine ⟨?_, measurable_of_countable _, fun _ _ => (Set.to_countable _).measurableSet⟩
    intro a b h
    have hf := congrArg Prod.fst h
    change (a.val : ℤ) - 1 = (b.val : ℤ) - 1 at hf
    apply Fin.ext
    omega
  apply he.map_injective
  rw [Measure.map_map he.measurable (measurable_pi_apply (i + 1)),
    map_uniform_lazyTwoDimensionalStep]
  have hset : ({(-1, 0), (0, 1), (1, -1)} : Finset (ℤ × ℤ)) =
      {(1, -1), (-1, 0), (0, 1)} := by decide
  simpa only [Function.comp_def, codeWalk_succ_sub, hset] using map_codeWalk_increment i

/-- Helper toward Lemma 4.11: the finite scalar path underlying the actual
code walk has exactly the uniform lazy-path law used by the reflection formula. -/
theorem codeWalk_lazyPrefix_hasLaw (n : ℕ) :
    HasLaw (lazyIIDPrefix (fun i (ω : ℕ → Fin 3) => ω (i + 1)) n)
      (uniformLazyPath n).toMeasure iidCodeMeasure :=
  ⟨(measurable_lazyIIDPrefix (fun i => measurable_pi_apply (i + 1)) n).aemeasurable,
    map_lazyIIDPrefix_eq_uniform (fun i => measurable_pi_apply (i + 1))
      sourceCode_independent sourceCode_uniform n⟩

private theorem sourceScalarWalk_eq (ω : ℕ → Fin 3) :
    globalIIDLazyWalk (fun i (v : ℕ → Fin 3) => v (i + 1)) ω =
      fun n => (codeWalk ω n).1 := by
  funext n
  simp only [globalIIDLazyWalk, codeWalk, Prod.fst_sum, lazyTwoDimensionalStep]

/-- Helper toward Lemma 4.11: the original and transformed endpoint pair in
the exact finite lazy-path model converges to `(B₁, Pitman(B)₁)`. This ties the
reflection difference to the Brownian limit on precisely the same carrier. -/
theorem uniformLazyPath_scalarPitman_joint_endpoint_tendsto
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄) :
    TendstoInDistribution (fun n (p : LazyPath n) =>
      ((p.val (Fin.last n) : ℝ) / Real.sqrt n / Real.sqrt (2 / 3),
        ((lazyPhi p).val.val (Fin.last n) : ℝ) / Real.sqrt n / Real.sqrt (2 / 3))) atTop
      (fun p => (p 1 0, scalarPitman (pathCoordinate p 0) 1))
      (fun n => (uniformLazyPath n).toMeasure) W₄ := by
  have h := codeWalk_scalarPitman_joint_endpoint_tendsto W₄ hB hI
  have hlaw (n : ℕ) : HasLaw (fun ω =>
      (((codeWalk ω n).1 : ℝ) / Real.sqrt n / Real.sqrt (2 / 3),
        ((vectorPitman (codeWalk ω) n).1 : ℝ) / Real.sqrt n / Real.sqrt (2 / 3)))
      ((uniformLazyPath n).toMeasure.map (fun p =>
        ((p.val (Fin.last n) : ℝ) / Real.sqrt n / Real.sqrt (2 / 3),
          ((lazyPhi p).val.val (Fin.last n) : ℝ) / Real.sqrt n / Real.sqrt (2 / 3))))
      iidCodeMeasure := by
    have hh := (hasLaw_map (measurable_of_countable (fun p : LazyPath n =>
      ((p.val (Fin.last n) : ℝ) / Real.sqrt n / Real.sqrt (2 / 3),
        ((lazyPhi p).val.val (Fin.last n) : ℝ) / Real.sqrt n / Real.sqrt (2 / 3)))).aemeasurable).comp
      (codeWalk_lazyPrefix_hasLaw n)
    have hq (ω : ℕ → Fin 3) :
        (lazyPhi (lazyIIDPrefix (fun i (v : ℕ → Fin 3) => v (i + 1)) n ω)).val.val
          (Fin.last n) = (vectorPitman (codeWalk ω) n).1 := by
      change (pitmanIIDPrefix (fun i (v : ℕ → Fin 3) => v (i + 1)) n ω).val
        (Fin.last n) = _
      rw [pitmanIIDPrefix_apply_global, sourceScalarWalk_eq]
      rfl
    simpa only [Function.comp_def, lazyIIDPrefix_apply, sourceScalarWalk_eq,
      Fin.val_last, hq] using hh
  refine ⟨fun n => (measurable_of_countable _).aemeasurable, h.aemeasurable_limit, ?_⟩
  apply h.tendsto.congr'
  apply Filter.Eventually.of_forall
  intro n
  exact ProbabilityMeasure.toMeasure_injective (hlaw n).map_eq

/-- Helper toward Lemma 4.11: the bounded sinc identity on the code-walk
probability space, derived from its exact finite uniform path law. -/
theorem codeWalk_endpoint_sinc_link (n : ℕ) (x : ℝ) :
    Real.sinc x * (∫ ω, Real.cos (x * ((codeWalk ω n).1 : ℝ)) ∂iidCodeMeasure) =
      ∫ ω, Real.sinc (x * ((vectorPitman (codeWalk ω) n).1 + 1 : ℝ)) ∂iidCodeMeasure := by
  have hc := (codeWalk_lazyPrefix_hasLaw n).integral_comp
    (measurable_of_countable (fun p : LazyPath n =>
      Real.cos (x * (p.val (Fin.last n) : ℝ)))).aestronglyMeasurable
  have hs := (codeWalk_lazyPrefix_hasLaw n).integral_comp
    (measurable_of_countable (fun p : LazyPath n =>
      Real.sinc (x * ((lazyPhi p).val.val (Fin.last n) + 1 : ℝ)))).aestronglyMeasurable
  have hq (ω : ℕ → Fin 3) :
      (lazyPhi (lazyIIDPrefix (fun i (v : ℕ → Fin 3) => v (i + 1)) n ω)).val.val
        (Fin.last n) = (vectorPitman (codeWalk ω) n).1 := by
    change (pitmanIIDPrefix (fun i (v : ℕ → Fin 3) => v (i + 1)) n ω).val
      (Fin.last n) = _
    rw [pitmanIIDPrefix_apply_global, sourceScalarWalk_eq]
    rfl
  simp only [Function.comp_def, lazyIIDPrefix_apply, sourceScalarWalk_eq, Fin.val_last] at hc
  simp only [Function.comp_def, hq] at hs
  rw [hc, hs]
  exact lazyPitman_endpoint_sinc_link n x

/-- Helper toward Lemma 4.11: the scalar Pitman endpoint has the sinc
transform of a Brownian endpoint's cosine transform. This is an unconditional
one-time identity under the stated Brownian-coordinate assumptions; no
reflection formula or Bessel identification is used as a premise. -/
theorem scalarPitman_endpoint_sinc_eq_cos
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄) (a : ℝ) :
    (∫ p, Real.sinc (a * scalarPitman (pathCoordinate p 0) 1) ∂W₄) =
      ∫ p, Real.cos (a * p 1 0) ∂W₄ := by
  let d (n : ℕ) : ℝ := (Real.sqrt n)⁻¹ / Real.sqrt (2 / 3)
  have hd : Tendsto d atTop (𝓝 0) := by
    simpa only [zero_div] using inv_sqrt_nat_tendsto.div_const (Real.sqrt (2 / 3))
  have h := codeWalk_scalarPitman_joint_endpoint_tendsto W₄ hB hI
  let fc : BoundedContinuousFunction (ℝ × ℝ) ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun z => Real.cos (a * z.1), by fun_prop⟩ 2 (by
      intro z w
      rw [Real.dist_eq]
      apply (abs_sub _ _).trans
      simpa only [ContinuousMap.coe_mk, show (1 : ℝ) + 1 = 2 by norm_num] using
        add_le_add (Real.abs_cos_le_one (a * z.1)) (Real.abs_cos_le_one (a * w.1)))
  let fs : BoundedContinuousFunction ℝ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun z => Real.sinc (a * z), by fun_prop⟩ 2 (by
      intro z w
      rw [Real.dist_eq]
      apply (abs_sub _ _).trans
      simpa only [ContinuousMap.coe_mk, show (1 : ℝ) + 1 = 2 by norm_num] using
        add_le_add (Real.abs_sinc_le_one (a * z)) (Real.abs_sinc_le_one (a * w)))
  have hc := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    h.forall_aemeasurable h.aemeasurable_limit).mp h fc
  simp only [fc, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk] at hc
  have hr := h.continuous_comp continuous_snd
  have hdM : TendstoInMeasure iidCodeMeasure (fun n (_ : ℕ → Fin 3) => d n) atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Filter.Eventually.of_forall (fun _ => hd))
  have hrs := hr.add_of_tendstoInMeasure_const hdM (fun _ => aemeasurable_const)
  have hs := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    hrs.forall_aemeasurable hrs.aemeasurable_limit).mp hrs fs
  simp only [fs, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk,
    Function.comp_apply, Pi.add_apply, add_zero] at hs
  have hs₀ : Tendsto (fun n => Real.sinc (a * d n)) atTop (𝓝 1) := by
    simpa only [mul_zero, Real.sinc_zero, Function.comp_def] using
      Real.continuous_sinc.continuousAt.tendsto.comp (tendsto_const_nhds.mul hd)
  have hh := hs₀.mul hc
  simp only [one_mul] at hh
  apply tendsto_nhds_unique hs
  convert hh using 1
  · funext n
    have he := codeWalk_endpoint_sinc_link n (a * d n)
    dsimp [Function.comp_def, Pi.add_apply, d] at he ⊢
    convert he.symm using 2 <;> congr 1 <;> funext ω <;> congr 1 <;> ring

/-- Helper toward Lemma 4.11: the explicit sinc transform of the scalar
Pitman marginal at time one, at every real frequency. -/
theorem scalarPitman_endpoint_sinc
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄) (a : ℝ) :
    (∫ p, Real.sinc (a * scalarPitman (pathCoordinate p 0) 1) ∂W₄) =
      Real.exp (-(a ^ 2) / 2) := by
  rw [scalarPitman_endpoint_sinc_eq_cos W₄ hB hI a]
  have hev := ((hB 0).hasLaw_eval 1).integral_comp (by fun_prop :
    AEStronglyMeasurable (fun x : ℝ => Real.cos (a * x)) (gaussianReal 0 1))
  simp only [Function.comp_apply] at hev
  rw [hev]
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

/-- Helper toward Lemma 4.11: the scalar Pitman image is nonnegative
simultaneously at every time on the Brownian zero-start event. -/
theorem scalarPitman_nonneg_ae
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ))
    (hB : IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t 0) W₄) :
    ∀ᵐ p ∂W₄, ∀ t : ℝ≥0, 0 ≤ scalarPitman (pathCoordinate p 0) t := by
  filter_upwards [hB.eval_zero_ae_eq_zero] with p hp
  intro t
  obtain ⟨u, hu, he, hmin⟩ :=
    continuousRunningMinimum_exists_eq_and_le (pathCoordinate p 0) t
  have h₀ := hmin 0 ⟨le_rfl, zero_le⟩
  have ht := hmin t ⟨zero_le, le_rfl⟩
  change (pathCoordinate p 0) t - 2 * continuousRunningMinimum (pathCoordinate p 0) t ≥ 0
  rw [he]
  change (pathCoordinate p 0) u ≤ p 0 0 at h₀
  rw [hp] at h₀
  linarith only [h₀, ht]





































end DirectedDistances.Probability
