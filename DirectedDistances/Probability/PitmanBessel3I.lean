/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.PitmanBessel3H
public import DirectedDistances.Probability.PitmanOneTime

/-! Helper toward Lemma 4.11: the uniform endpoint link survives jointly with
arbitrarily many past Pitman evaluations. This is a multi-time intertwining
identity, not yet the Pitman–BES(3) whole-path theorem. -/

public section
namespace DirectedDistances.Probability
open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.RandomWalk
open scoped NNReal Topology

local instance pitman3IContinuousMapMeasurableSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    MeasurableSpace C(X, Y) := borel _
local instance pitman3IContinuousMapBorelSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    BorelSpace C(X, Y) := ⟨rfl⟩
local instance pitman3IContinuousMapSecondCountable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [LocallyCompactSpace X] [SecondCountableTopology Y] :
    SecondCountableTopology C(X, Y) := continuousPath_secondCountable

/-- Helper toward Lemma 4.11: the discrete sinc link remains valid after
weighting by an arbitrary test of the entire transformed finite path. -/
theorem lazyPitman_weighted_endpoint_sinc_link (n : ℕ) (x : ℝ)
    (F : NonnegativeLazyPath n → ℝ) :
    Real.sinc x * (∫ p, F (lazyPhi p) * Real.cos (x * (p.val (Fin.last n) : ℝ))
      ∂(uniformLazyPath n).toMeasure) =
      ∫ p, F (lazyPhi p) * Real.sinc (x * ((lazyPhi p).val.val (Fin.last n) + 1 : ℝ))
        ∂(uniformLazyPath n).toMeasure := by
  classical
  rw [PMF.integral_eq_sum, PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  rw [lazyPitman_joint_endpoint_uniform_link n
      (fun q z => F q * Real.cos (x * z)),
    lazyPitman_joint_endpoint_uniform_link n
      (fun q _ => F q * Real.sinc (x * (q.val.val (Fin.last n) + 1 : ℝ))),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  have he : (((q.val.val (Fin.last n)).toNat : ℕ) : ℝ) =
      (q.val.val (Fin.last n) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (q.property (Fin.last n))
  have hh := finite_uniform_endpoint_sinc (q.val.val (Fin.last n)).toNat x
  simp only [he] at hh
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hne : ((q.val.val (Fin.last n)).toNat + 1 : ℝ) ≠ 0 := by positivity
  calc
    _ = (pitmanLazyPathLaw n q).toReal * F q *
        (Real.sinc x * ((∑ i : Fin ((q.val.val (Fin.last n)).toNat + 1),
          Real.cos (x * ((q.val.val (Fin.last n) : ℝ) - 2 * i.val))) /
            ((q.val.val (Fin.last n)).toNat + 1))) := by ring
    _ = (pitmanLazyPathLaw n q).toReal * F q *
        Real.sinc (x * (q.val.val (Fin.last n) + 1 : ℝ)) := by rw [he, hh]
    _ = _ := by field_simp

/-- Helper toward Lemma 4.11: a past-weighted sinc link on the actual code
probability space, retaining all finite observations and their common scaling. -/
theorem codePitmanFiniteData_weighted_sinc_link {k : ℕ}
    (t : Fin k → ℝ≥0) (ht : ∀ i, t i ≤ 1) (j : Fin k) (hj : t j = 1)
    (n : ℕ) (a : ℝ) (F : (Fin k → ℝ) → ℝ) :
    let d := (Real.sqrt (n : ℝ))⁻¹ / Real.sqrt (2 / 3)
    Real.sinc (a * d) *
      (∫ ω, F (fun i => (codePitmanFiniteData t n ω).2 i + d) *
        Real.cos (a * (codePitmanFiniteData t n ω).1) ∂iidCodeMeasure) =
      ∫ ω, F (fun i => (codePitmanFiniteData t n ω).2 i + d) *
        Real.sinc (a * ((codePitmanFiniteData t n ω).2 j + d)) ∂iidCodeMeasure := by
  dsimp only
  let d : ℝ := (Real.sqrt (n : ℝ))⁻¹ / Real.sqrt (2 / 3)
  let G (q : NonnegativeLazyPath n) : ℝ := F (fun i =>
    (q.val.val ⟨⌊(n : ℝ) * t i⌋₊,
      Nat.lt_succ_of_le (pitman_floor_le n (t i) (ht i))⟩ : ℝ) /
        Real.sqrt n / Real.sqrt (2 / 3) + d)
  have hc := (codeWalk_lazyPrefix_hasLaw n).integral_comp
    (measurable_of_countable (fun p : LazyPath n =>
      F (fun i => (lazyPitmanFiniteData t ht n p).2 i + d) *
        Real.cos (a * (lazyPitmanFiniteData t ht n p).1))).aestronglyMeasurable
  have hs := (codeWalk_lazyPrefix_hasLaw n).integral_comp
    (measurable_of_countable (fun p : LazyPath n =>
      F (fun i => (lazyPitmanFiniteData t ht n p).2 i + d) *
        Real.sinc (a * ((lazyPitmanFiniteData t ht n p).2 j + d)))).aestronglyMeasurable
  simp only [Function.comp_def, lazyPitmanFiniteData_prefix] at hc hs
  change Real.sinc (a * d) * _ = _
  rw [hc, hs]
  have hlast : (⟨⌊(n : ℝ) * t j⌋₊,
      Nat.lt_succ_of_le (pitman_floor_le n (t j) (ht j))⟩ : Fin (n + 1)) = Fin.last n := by
    apply Fin.ext
    simp only [hj, NNReal.coe_one, mul_one, Nat.floor_natCast, Fin.val_last]
  have h := lazyPitman_weighted_endpoint_sinc_link n (a * d) G
  convert h using 2
  · congr 1
    funext p
    dsimp [G, lazyPitmanFiniteData, d]
    congr 2
    ring
  · funext p
    dsimp [G, lazyPitmanFiniteData]
    rw [hlast]
    congr 2
    dsimp [d]
    ring

private noncomputable def bounded_cos_test {k : ℕ}
    (F : BoundedContinuousFunction (Fin k → ℝ) ℝ) (a : ℝ) :
    BoundedContinuousFunction (ℝ × (Fin k → ℝ)) ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun z => F z.2 * Real.cos (a * z.1), by fun_prop⟩ (2 * ‖F‖) (by
      intro z w
      apply BoundedContinuousFunction.dist_le_two_norm'
      intro v
      simp only [ContinuousMap.coe_mk, Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans
        (by simpa only [mul_one, Real.norm_eq_abs] using F.norm_coe_le_norm v.2))

private noncomputable def bounded_sinc_test {k : ℕ}
    (F : BoundedContinuousFunction (Fin k → ℝ) ℝ) (a : ℝ) (j : Fin k) :
    BoundedContinuousFunction (ℝ × (Fin k → ℝ)) ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun z => F z.2 * Real.sinc (a * z.2 j), by fun_prop⟩ (2 * ‖F‖) (by
      intro z w
      apply BoundedContinuousFunction.dist_le_two_norm'
      intro v
      simp only [ContinuousMap.coe_mk, Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one _) (abs_nonneg _)).trans
        (by simpa only [mul_one, Real.norm_eq_abs] using F.norm_coe_le_norm v.2))

/-- Helper toward Lemma 4.11: the Brownian uniform endpoint link holds jointly
with any finite set of past Pitman observations and every bounded continuous
test of those observations. Times may coincide and may include zero. -/
theorem scalarPitman_finite_past_sinc_link
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    {k : ℕ} (t : Fin k → ℝ≥0) (ht : ∀ i, t i ≤ 1)
    (j : Fin k) (hj : t j = 1)
    (F : BoundedContinuousFunction (Fin k → ℝ) ℝ) (a : ℝ) :
    (∫ p, F (fun i => scalarPitman (pathCoordinate p 0) (t i)) *
      Real.cos (a * p 1 0) ∂W₄) =
    ∫ p, F (fun i => scalarPitman (pathCoordinate p 0) (t i)) *
      Real.sinc (a * scalarPitman (pathCoordinate p 0) 1) ∂W₄ := by
  let d (n : ℕ) : ℝ := (Real.sqrt (n : ℝ))⁻¹ / Real.sqrt (2 / 3)
  let D (n : ℕ) : ℝ × (Fin k → ℝ) := (0, fun _ => d n)
  have hd : Tendsto d atTop (𝓝 0) := by
    have hi : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    simpa only [zero_div] using hi.div_const (Real.sqrt (2 / 3))
  have hD : Tendsto D atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (0 : ℝ))).prodMk_nhds (tendsto_pi_nhds.mpr fun _ => hd)
  have hDM : TendstoInMeasure iidCodeMeasure (fun n (_ : ℕ → Fin 3) => D n) atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Filter.Eventually.of_forall (fun _ => hD))
  have h := (codePitmanFiniteData_tendsto W₄ hB hI t).add_of_tendstoInMeasure_const
    hDM (fun _ => aemeasurable_const)
  have hc := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    h.forall_aemeasurable h.aemeasurable_limit).mp h (bounded_cos_test F a)
  have hs := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    h.forall_aemeasurable h.aemeasurable_limit).mp h (bounded_sinc_test F a j)
  simp only [bounded_cos_test, bounded_sinc_test, BoundedContinuousFunction.mkOfBound_coe,
    ContinuousMap.coe_mk, Pi.add_apply, Prod.fst_add, Prod.snd_add,
    D, add_zero, hj] at hc hs
  have hs₀ : Tendsto (fun n => Real.sinc (a * d n)) atTop (𝓝 1) := by
    simpa only [mul_zero, Real.sinc_zero, Function.comp_def] using
      Real.continuous_sinc.continuousAt.tendsto.comp (tendsto_const_nhds.mul hd)
  have hh := hs₀.mul hc
  simp only [one_mul] at hh
  apply tendsto_nhds_unique hh
  convert hs using 1
  funext n
  exact codePitmanFiniteData_weighted_sinc_link t ht j hj n a F

/-- Helper toward Lemma 4.11: the uniform endpoint link with an arbitrary
finite collection of earlier observation times; no endpoint must be inserted
in the test by the caller. -/
theorem scalarPitman_past_sinc_link_one
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    {k : ℕ} (t : Fin k → ℝ≥0) (ht : ∀ i, t i ≤ 1)
    (F : BoundedContinuousFunction (Fin k → ℝ) ℝ) (a : ℝ) :
    (∫ p, F (fun i => scalarPitman (pathCoordinate p 0) (t i)) *
      Real.cos (a * p 1 0) ∂W₄) =
    ∫ p, F (fun i => scalarPitman (pathCoordinate p 0) (t i)) *
      Real.sinc (a * scalarPitman (pathCoordinate p 0) 1) ∂W₄ := by
  let G := F.compContinuous ⟨fun x : Fin (k + 1) → ℝ => fun i => x i.succ, by fun_prop⟩
  let u : Fin (k + 1) → ℝ≥0 := Fin.cons 1 t
  have hu : ∀ i : Fin (k + 1), u i ≤ 1 := by
    intro i
    refine Fin.cases le_rfl (fun j => ?_) i
    exact ht j
  exact scalarPitman_finite_past_sinc_link W₄ hB hI u hu 0 rfl G a

/-- Helper toward Lemma 4.11: the finite-past uniform endpoint link at every
positive terminal time, with the same test applied jointly to all past values. -/
theorem scalarPitman_past_sinc_link
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (T : ℝ≥0) (hT : T ≠ 0) {k : ℕ} (t : Fin k → ℝ≥0)
    (ht : ∀ i, t i ≤ T)
    (F : BoundedContinuousFunction (Fin k → ℝ) ℝ) (a : ℝ) :
    (∫ p, F (fun i => scalarPitman (pathCoordinate p 0) (t i)) *
      Real.cos (a * p T 0) ∂W₄) =
    ∫ p, F (fun i => scalarPitman (pathCoordinate p 0) (t i)) *
      Real.sinc (a * scalarPitman (pathCoordinate p 0) T) ∂W₄ := by
  let u (i : Fin k) : ℝ≥0 := t i / T
  let c : ℝ := Real.sqrt T
  have hc : c ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast pos_of_ne_zero hT)
  let G := F.compContinuous ⟨fun x : Fin k → ℝ => fun i => c * x i, by fun_prop⟩
  have hu : ∀ i, u i ≤ 1 := fun i => (div_le_one (pos_of_ne_zero hT)).mpr (ht i)
  have hlink := scalarPitman_past_sinc_link_one W₄ hB hI u hu G (a * c)
  have hd := brownianScalarPath_identDistrib
    ((continuous_brownianScalePath T).comp (continuous_pathCoordinate 0)).measurable
    (continuous_pathCoordinate 0).measurable ((hB 0).smul hT) (hB 0)
  let fc (f : C(ℝ≥0, ℝ)) : ℝ :=
    G (fun i => scalarPitman f (u i)) * Real.cos ((a * c) * f 1)
  let fs (f : C(ℝ≥0, ℝ)) : ℝ :=
    G (fun i => scalarPitman f (u i)) * Real.sinc ((a * c) * scalarPitman f 1)
  have hobs : Continuous (fun f : C(ℝ≥0, ℝ) => fun i => scalarPitman f (u i)) :=
    continuous_pi fun i => (continuous_eval_const (u i)).comp continuous_scalarPitman
  have hfc : Measurable fc :=
    ((G.continuous.comp hobs).mul (Real.continuous_cos.comp
      (continuous_const.mul (continuous_eval_const (1 : ℝ≥0))))).measurable
  have hfs : Measurable fs :=
    ((G.continuous.comp hobs).mul (Real.continuous_sinc.comp
      (continuous_const.mul ((continuous_eval_const (1 : ℝ≥0)).comp
        continuous_scalarPitman)))).measurable
  have hec := (hd.comp hfc).integral_eq
  have hes := (hd.comp hfs).integral_eq
  have he (f : C(ℝ≥0, ℝ)) (i : Fin k) :
      c * scalarPitman (brownianScalePath T f) (u i) = scalarPitman f (t i) := by
    rw [scalarPitman_brownianScalePath f T hT]
    dsimp [u]
    rw [mul_div_cancel₀ _ hT]
    change c * (c⁻¹ * scalarPitman f (t i)) = _
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have he₁ (f : C(ℝ≥0, ℝ)) :
      (a * c) * scalarPitman (brownianScalePath T f) 1 = a * scalarPitman f T := by
    rw [scalarPitman_brownianScalePath f T hT, mul_one]
    change (a * c) * (c⁻¹ * scalarPitman f T) = _
    rw [← mul_assoc, mul_assoc a c, mul_inv_cancel₀ hc, mul_one]
  have he₂ (f : C(ℝ≥0, ℝ)) : (a * c) * brownianScalePath T f 1 = a * f T := by
    change (a * c) * (c⁻¹ * f (T * 1)) = _
    rw [mul_one, ← mul_assoc, mul_assoc a c, mul_inv_cancel₀ hc, mul_one]
  change (∫ p, fc (brownianScalePath T (pathCoordinate p 0)) ∂W₄) =
    ∫ p, fc (pathCoordinate p 0) ∂W₄ at hec
  change (∫ p, fs (brownianScalePath T (pathCoordinate p 0)) ∂W₄) =
    ∫ p, fs (pathCoordinate p 0) ∂W₄ at hes
  change (∫ p, fc (pathCoordinate p 0) ∂W₄) =
    ∫ p, fs (pathCoordinate p 0) ∂W₄ at hlink
  have hfinal := hec.trans (hlink.trans hes.symm)
  simpa only [fc, fs, G, BoundedContinuousFunction.compContinuous_apply,
    ContinuousMap.coe_mk, he, he₁, he₂, pathCoordinate] using hfinal

/-- Helper toward Lemma 4.11: freeze a continuous scalar path at a deterministic
time, preserving all its earlier values as a continuous path on the half-line. -/
@[expose] noncomputable def pitmanStoppedPath (s : ℝ≥0) (f : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) :=
  ⟨fun t => f (min t s), f.continuous.comp (continuous_id.min continuous_const)⟩

/-- Helper toward Lemma 4.11: deterministic stopping is continuous in the
compact-open path topology. -/
theorem continuous_pitmanStoppedPath (s : ℝ≥0) : Continuous (pitmanStoppedPath s) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp (continuous_fst.prodMk (continuous_snd.min continuous_const))

/-- Helper toward Lemma 4.11: stopping after an observation does not change
that Pitman observation, including its entire running-minimum interval. -/
theorem scalarPitman_stoppedPath (s : ℝ≥0) (f : C(ℝ≥0, ℝ))
    (t : ℝ≥0) (ht : t ≤ s) :
    scalarPitman (pitmanStoppedPath s f) t = scalarPitman f t := by
  have he : (pitmanStoppedPath s f) '' Set.Icc 0 t = f '' Set.Icc 0 t := by
    apply Set.image_congr
    intro u hu
    exact congrArg f (min_eq_left (hu.2.trans ht))
  change f (min t s) - 2 * sInf ((pitmanStoppedPath s f) '' Set.Icc 0 t) =
    f t - 2 * sInf (f '' Set.Icc 0 t)
  rw [min_eq_left ht, he]

/-- Helper toward Lemma 4.11: the Brownian increment after a deterministic
time is independent of the entire stopped continuous past, hence of all its
Pitman observations simultaneously. -/
theorem brownian_increment_indep_stoppedPath
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ))
    (hB : IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t 0) W₄)
    (s u : ℝ≥0) :
    IndepFun (fun p => p (s + u) 0 - p s 0)
      (fun p => pitmanStoppedPath s (pathCoordinate p 0)) W₄ := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  let : Countable D := hDc.to_subtype
  let ev : C(ℝ≥0, ℝ) → D → ℝ := fun f t => f t
  have hevc : Continuous ev := continuous_pi (fun t => continuous_eval_const t.val)
  have hev : MeasurableEmbedding ev := hevc.measurableEmbedding (by
    intro f g h
    apply DFunLike.ext'
    apply f.continuous.ext_on hDd g.continuous
    intro t ht
    exact congrFun h ⟨t, ht⟩)
  have hi := (hB.toIsPreBrownianReal.indepFun_shift s).comp
    (measurable_pi_apply u)
    (measurable_pi_iff.mpr (fun t : D =>
      measurable_pi_apply (⟨min t.val s, min_le_right _ _⟩ : Set.Iic s)))
  change IndepFun (fun p => p (s + u) 0 - p s 0)
    (ev ∘ fun p => pitmanStoppedPath s (pathCoordinate p 0)) W₄ at hi
  unfold IndepFun Kernel.IndepFun at hi ⊢
  rw [← MeasurableSpace.comap_comp, hev.comap_eq] at hi
  exact hi

private theorem gaussian_cos_sin (v : ℝ≥0) (a : ℝ) :
    (∫ x, Real.cos (a * x) ∂gaussianReal 0 v) = Real.exp (-(v : ℝ) * a ^ 2 / 2) ∧
    (∫ x, Real.sin (a * x) ∂gaussianReal 0 v) = 0 := by
  have hi : Integrable (fun x : ℝ => Complex.exp ((a : ℂ) * x * Complex.I))
      (gaussianReal 0 v) := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
    exact Filter.Eventually.of_forall (fun x => by simp [Complex.norm_exp])
  have hc := charFun_gaussianReal (μ := 0) (v := v) a
  rw [charFun_apply_real] at hc
  constructor
  · have hr := congrArg Complex.re hc
    have hire := integral_re hi
    change (∫ x : ℝ, (Complex.exp ((a : ℂ) * x * Complex.I)).re ∂gaussianReal 0 v) =
      (∫ x : ℝ, Complex.exp ((a : ℂ) * x * Complex.I) ∂gaussianReal 0 v).re at hire
    rw [← hire] at hr
    simpa [← Complex.ofReal_pow, Complex.exp_re, neg_div] using hr
  · have hr := congrArg Complex.im hc
    have him := integral_im hi
    change (∫ x : ℝ, (Complex.exp ((a : ℂ) * x * Complex.I)).im ∂gaussianReal 0 v) =
      (∫ x : ℝ, Complex.exp ((a : ℂ) * x * Complex.I) ∂gaussianReal 0 v).im at him
    rw [← him] at hr
    simpa [← Complex.ofReal_pow, Complex.exp_im, neg_div] using hr

/-- Helper toward Lemma 4.11: a Brownian cosine at a later time, weighted by
any bounded continuous test of finitely many past Pitman values, propagates
by the exact Gaussian exponential factor. -/
theorem brownian_cos_pitman_past
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t 0) W₄)
    (s u : ℝ≥0) {k : ℕ} (t : Fin k → ℝ≥0) (ht : ∀ i, t i ≤ s)
    (F : BoundedContinuousFunction (Fin k → ℝ) ℝ) (a : ℝ) :
    (∫ p, F (fun i => scalarPitman (pathCoordinate p 0) (t i)) *
      Real.cos (a * p (s + u) 0) ∂W₄) =
    Real.exp (-(u : ℝ) * a ^ 2 / 2) *
      ∫ p, F (fun i => scalarPitman (pathCoordinate p 0) (t i)) *
        Real.cos (a * p s 0) ∂W₄ := by
  let A (p : C(ℝ≥0, Fin 4 → ℝ)) := F (fun i => scalarPitman (pathCoordinate p 0) (t i))
  let X (p : C(ℝ≥0, Fin 4 → ℝ)) := p (s + u) 0 - p s 0
  let C (f : C(ℝ≥0, ℝ)) := F (fun i => scalarPitman f (t i)) * Real.cos (a * f s)
  let S (f : C(ℝ≥0, ℝ)) := F (fun i => scalarPitman f (t i)) * Real.sin (a * f s)
  have hobs : Continuous (fun f : C(ℝ≥0, ℝ) => fun i => scalarPitman f (t i)) :=
    continuous_pi fun i => (continuous_eval_const (t i)).comp continuous_scalarPitman
  have hC : Measurable C := ((F.continuous.comp hobs).mul
    (Real.continuous_cos.comp (continuous_const.mul (continuous_eval_const s)))).measurable
  have hS : Measurable S := ((F.continuous.comp hobs).mul
    (Real.continuous_sin.comp (continuous_const.mul (continuous_eval_const s)))).measurable
  have hmA : Measurable A := (F.continuous.comp
    (hobs.comp (continuous_pathCoordinate 0))).measurable
  have hmX : Measurable X := by dsimp [X]; fun_prop
  have hstop := (continuous_pitmanStoppedPath s).measurable.comp
    (continuous_pathCoordinate (0 : Fin 4)).measurable
  have hce (p : C(ℝ≥0, Fin 4 → ℝ)) : C (pitmanStoppedPath s (pathCoordinate p 0)) =
      A p * Real.cos (a * p s 0) := by
    have he := funext (fun i => scalarPitman_stoppedPath s (pathCoordinate p 0) (t i) (ht i))
    dsimp only [C, A]
    rw [he]
    simp only [pitmanStoppedPath, ContinuousMap.coe_mk, min_self, pathCoordinate]
  have hse (p : C(ℝ≥0, Fin 4 → ℝ)) : S (pitmanStoppedPath s (pathCoordinate p 0)) =
      A p * Real.sin (a * p s 0) := by
    have he := funext (fun i => scalarPitman_stoppedPath s (pathCoordinate p 0) (t i) (ht i))
    dsimp only [S, A]
    rw [he]
    simp only [pitmanStoppedPath, ContinuousMap.coe_mk, min_self, pathCoordinate]
  have hind := brownian_increment_indep_stoppedPath W₄ hB s u
  have hc := (hind.comp (by fun_prop : Measurable (fun x : ℝ => Real.cos (a * x))) hC).symm
  have hs := (hind.comp (by fun_prop : Measurable (fun x : ℝ => Real.sin (a * x))) hS).symm
  have hcint := hc.integral_fun_mul_eq_mul_integral
    (hC.comp hstop).aestronglyMeasurable (by fun_prop : AEStronglyMeasurable (fun p => Real.cos (a * X p)) W₄)
  have hsint := hs.integral_fun_mul_eq_mul_integral
    (hS.comp hstop).aestronglyMeasurable (by fun_prop : AEStronglyMeasurable (fun p => Real.sin (a * X p)) W₄)
  simp only [Function.comp_def, hce, hse] at hcint hsint
  have hlaw := (hB.toIsPreBrownianReal.shift s).hasLaw_eval u
  have hec := hlaw.integral_comp (by fun_prop : AEStronglyMeasurable
    (fun x : ℝ => Real.cos (a * x)) (gaussianReal 0 u))
  have hes := hlaw.integral_comp (by fun_prop : AEStronglyMeasurable
    (fun x : ℝ => Real.sin (a * x)) (gaussianReal 0 u))
  change (∫ p, Real.cos (a * X p) ∂W₄) = _ at hec
  change (∫ p, Real.sin (a * X p) ∂W₄) = _ at hes
  rw [(gaussian_cos_sin u a).1] at hec
  rw [(gaussian_cos_sin u a).2] at hes
  rw [hec] at hcint
  rw [hes, mul_zero] at hsint
  have hb (p : C(ℝ≥0, Fin 4 → ℝ)) : |A p| ≤ ‖F‖ := F.norm_coe_le_norm _
  have hmB : Measurable (fun p : C(ℝ≥0, Fin 4 → ℝ) => p s 0) :=
    (measurable_pi_apply (0 : Fin 4)).comp (continuous_eval_const s).measurable
  have hmcosB := Real.continuous_cos.measurable.comp (hmB.const_mul a)
  have hmsinB := Real.continuous_sin.measurable.comp (hmB.const_mul a)
  have hmcosX := Real.continuous_cos.measurable.comp (hmX.const_mul a)
  have hmsinX := Real.continuous_sin.measurable.comp (hmX.const_mul a)
  have hic : Integrable (fun p => (A p * Real.cos (a * p s 0)) * Real.cos (a * X p)) W₄ := by
    apply Integrable.mono' (integrable_const ‖F‖)
      (((hmA.mul hmcosB).mul hmcosX).aestronglyMeasurable)
    apply Filter.Eventually.of_forall
    intro p
    simp only [Pi.mul_apply, Function.comp_apply, Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ |A p| * 1 * 1 := by gcongr <;> exact Real.abs_cos_le_one _
      _ ≤ ‖F‖ := by simpa only [mul_one] using hb p
  have his : Integrable (fun p => (A p * Real.sin (a * p s 0)) * Real.sin (a * X p)) W₄ := by
    apply Integrable.mono' (integrable_const ‖F‖)
      (((hmA.mul hmsinB).mul hmsinX).aestronglyMeasurable)
    apply Filter.Eventually.of_forall
    intro p
    simp only [Pi.mul_apply, Function.comp_apply, Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ |A p| * 1 * 1 := by gcongr <;> exact Real.abs_sin_le_one _
      _ ≤ ‖F‖ := by simpa only [mul_one] using hb p
  have he (p : C(ℝ≥0, Fin 4 → ℝ)) :
      A p * Real.cos (a * p (s + u) 0) =
        (A p * Real.cos (a * p s 0)) * Real.cos (a * X p) -
        (A p * Real.sin (a * p s 0)) * Real.sin (a * X p) := by
    have hx : a * p (s + u) 0 = a * p s 0 + a * X p := by dsimp [X]; ring
    rw [hx, Real.cos_add]
    ring
  change (∫ p, A p * Real.cos (a * p (s + u) 0) ∂W₄) = _
  simp_rw [he]
  rw [integral_sub hic his, hcint, hsint, sub_zero]
  exact mul_comm _ _

/-- Helper toward Lemma 4.11: the finite-past uniform endpoint link includes
the degenerate terminal time zero. -/
theorem scalarPitman_past_sinc_link_nonneg
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (T : ℝ≥0) {k : ℕ} (t : Fin k → ℝ≥0) (ht : ∀ i, t i ≤ T)
    (F : BoundedContinuousFunction (Fin k → ℝ) ℝ) (a : ℝ) :
    (∫ p, F (fun i => scalarPitman (pathCoordinate p 0) (t i)) *
      Real.cos (a * p T 0) ∂W₄) =
    ∫ p, F (fun i => scalarPitman (pathCoordinate p 0) (t i)) *
      Real.sinc (a * scalarPitman (pathCoordinate p 0) T) ∂W₄ := by
  by_cases hT : T = 0
  · subst T
    apply integral_congr_ae
    filter_upwards [(hB 0).eval_zero_ae_eq_zero] with p hp
    have hR : scalarPitman (pathCoordinate p 0) 0 = 0 := by
      change p 0 0 - 2 * continuousRunningMinimum (pathCoordinate p 0) 0 = 0
      rw [continuousRunningMinimum_zero]
      change p 0 0 - 2 * p 0 0 = 0
      rw [hp]
      ring
    rw [hp, hR, mul_zero, Real.cos_zero, Real.sinc_zero]
  · exact scalarPitman_past_sinc_link W₄ hB hI T hT t ht F a

/-- Helper toward Lemma 4.11: the exact multi-time sinc transition identity
for the scalar Brownian Pitman process. The test may observe arbitrarily many
times at or before `s`; the Gaussian factor depends on the elapsed time `u`.
This includes `s = 0`, `u = 0`, repeated observation times and an empty past. -/
theorem scalarPitman_past_sinc_transition
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (s u : ℝ≥0) {k : ℕ} (t : Fin k → ℝ≥0) (ht : ∀ i, t i ≤ s)
    (F : BoundedContinuousFunction (Fin k → ℝ) ℝ) (a : ℝ) :
    (∫ p, F (fun i => scalarPitman (pathCoordinate p 0) (t i)) *
      Real.sinc (a * scalarPitman (pathCoordinate p 0) (s + u)) ∂W₄) =
    Real.exp (-(u : ℝ) * a ^ 2 / 2) *
      ∫ p, F (fun i => scalarPitman (pathCoordinate p 0) (t i)) *
        Real.sinc (a * scalarPitman (pathCoordinate p 0) s) ∂W₄ := by
  rw [← scalarPitman_past_sinc_link_nonneg W₄ hB hI (s + u) t
    (fun i => (ht i).trans (le_add_of_nonneg_right zero_le)) F a]
  rw [brownian_cos_pitman_past W₄ (hB 0) s u t ht F a,
    scalarPitman_past_sinc_link_nonneg W₄ hB hI s t ht F a]

/-- Helper toward Lemma 4.11: the two-time Pitman sinc transform reduces
exactly to a one-time radial Gaussian integral. The one-time identification is
imported from its owner; no multi-time radial identification is assumed. -/
theorem scalarPitman_two_time_sinc
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (s u : ℝ≥0) (a b : ℝ) :
    (∫ p, Real.sinc (b * scalarPitman (pathCoordinate p 0) s) *
      Real.sinc (a * scalarPitman (pathCoordinate p 0) (s + u)) ∂W₄) =
    Real.exp (-(u : ℝ) * a ^ 2 / 2) *
      ∫ p, Real.sinc (b * radial3Path (firstThreePath p) s) *
        Real.sinc (a * radial3Path (firstThreePath p) s) ∂W₄ := by
  let F : BoundedContinuousFunction (Fin 1 → ℝ) ℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨fun x => Real.sinc (b * x 0), by fun_prop⟩ 2 (by
        intro x y
        apply (dist_le_norm_add_norm _ _).trans
        simpa only [ContinuousMap.coe_mk, Real.norm_eq_abs, show (1 : ℝ) + 1 = 2 by norm_num]
          using add_le_add (Real.abs_sinc_le_one (b * x 0)) (Real.abs_sinc_le_one (b * y 0)))
  have h := scalarPitman_past_sinc_transition W₄ hB hI s u
    (fun _ : Fin 1 => s) (fun _ => le_rfl) F a
  have he := ((scalarPitman_radial3_identDistrib_eval W₄ hB hI s).comp
    (by fun_prop : Measurable (fun x : ℝ => Real.sinc (b * x) * Real.sinc (a * x)))).integral_eq
  exact h.trans (congrArg (fun z => Real.exp (-(u : ℝ) * a ^ 2 / 2) * z) he)



































end DirectedDistances.Probability
