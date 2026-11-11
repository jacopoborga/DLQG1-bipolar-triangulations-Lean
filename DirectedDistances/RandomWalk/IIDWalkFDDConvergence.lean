module

public import DirectedDistances.RandomWalk.IIDWalkEndpointCLT
public import DirectedDistances.RandomWalk.ConditionedFunctionalInterpolation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Finite dimensional helpers toward Lemma 4.11

These are unconditioned walk helpers, not a functional convergence theorem. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

/-- Helper toward Lemma 4.11: the number of steps in a rescaled grid block. -/
@[expose] noncomputable def iidGridBlockLength (s t : ℝ≥0) (n : ℕ) : ℕ :=
  ⌊(n : ℝ) * t⌋₊ - ⌊(n : ℝ) * s⌋₊

/-- Helper toward Lemma 4.11: grid block lengths have the correct macroscopic ratio. -/
theorem tendsto_iidGridBlockLength_div (s t : ℝ≥0) (hst : s ≤ t) :
    Tendsto (fun n : ℕ => (iidGridBlockLength s t n : ℝ) / n)
      atTop (𝓝 ((t : ℝ) - s)) := by
  have ht := (tendsto_nat_floor_mul_div_atTop t.coe_nonneg).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hs := (tendsto_nat_floor_mul_div_atTop s.coe_nonneg).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  convert ht.sub hs using 1
  funext n
  rw [iidGridBlockLength, Nat.cast_sub (Nat.floor_mono
    (mul_le_mul_of_nonneg_left (show (s : ℝ) ≤ t from hst) (Nat.cast_nonneg n)))]
  simp only [Function.comp_apply, mul_comm, sub_div]

/-- Helper toward Lemma 4.11: a block of positive macroscopic duration grows to infinity. -/
theorem tendsto_iidGridBlockLength_atTop (s t : ℝ≥0) (hst : s < t) :
    Tendsto (iidGridBlockLength s t) atTop atTop := by
  have hp : 0 < (t : ℝ) - s := sub_pos.mpr hst
  have hr := tendsto_iidGridBlockLength_div s t hst.le
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  have hm := hr.pos_mul_atTop hp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply hm.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact div_mul_cancel₀ _ (by exact_mod_cast hn.ne')

/-- Helper toward Lemma 4.11: the CLT at the varying length of a shifted grid block. -/
theorem codeWalk_grid_block_length_clt (s t : ℝ≥0) (hst : s < t) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt (iidGridBlockLength s t n : ℝ))⁻¹ •
        (((codeWalk ω ⌊(n : ℝ) * t⌋₊ - codeWalk ω ⌊(n : ℝ) * s⌋₊).1 : ℝ),
         ((codeWalk ω ⌊(n : ℝ) * t⌋₊ - codeWalk ω ⌊(n : ℝ) * s⌋₊).2 : ℝ)))
      atTop (fun z : ℝ × ℝ => (z.1, (z.2 - z.1) / 2))
      (fun _ : ℕ => iidCodeMeasure) iidEndpointLimitLaw := by
  have hi (n : ℕ) := identDistrib_codeWalk_normalized_block
    ⌊(n : ℝ) * s⌋₊ (iidGridBlockLength s t n)
  have he (n : ℕ) : ⌊(n : ℝ) * s⌋₊ + iidGridBlockLength s t n =
      ⌊(n : ℝ) * t⌋₊ := Nat.add_sub_of_le (Nat.floor_mono
        (mul_le_mul_of_nonneg_left (show (s : ℝ) ≤ t from hst.le) (Nat.cast_nonneg n)))
  simp only [he] at hi
  refine ⟨fun n => (hi n).aemeasurable_fst,
    codeWalk_endpoint_clt.aemeasurable_limit, ?_⟩
  have h := codeWalk_endpoint_clt.tendsto.comp (tendsto_iidGridBlockLength_atTop s t hst)
  apply h.congr'
  exact Eventually.of_forall (fun n => Subtype.ext (hi n).map_eq.symm)

/-- Helper toward Lemma 4.11: shifted grid increments satisfy the two dimensional CLT,
with the explicit scaled inverse diagonal Gaussian map. -/
theorem codeWalk_grid_block_clt (s t : ℝ≥0) (hst : s < t) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt (n : ℝ))⁻¹ •
        (((codeWalk ω ⌊(n : ℝ) * t⌋₊ - codeWalk ω ⌊(n : ℝ) * s⌋₊).1 : ℝ),
         ((codeWalk ω ⌊(n : ℝ) * t⌋₊ - codeWalk ω ⌊(n : ℝ) * s⌋₊).2 : ℝ)))
      atTop (fun z : ℝ × ℝ => Real.sqrt ((t : ℝ) - s) • (z.1, (z.2 - z.1) / 2))
      (fun _ : ℕ => iidCodeMeasure) iidEndpointLimitLaw := by
  have hr : Tendsto (fun n : ℕ =>
      Real.sqrt ((iidGridBlockLength s t n : ℝ) / n))
      atTop (𝓝 (Real.sqrt ((t : ℝ) - s))) :=
    (tendsto_iidGridBlockLength_div s t hst.le).sqrt
  have hm : TendstoInMeasure iidCodeMeasure
      (fun (n : ℕ) (_ : ℕ → Fin 3) => Real.sqrt ((iidGridBlockLength s t n : ℝ) / n))
      atTop (fun _ => Real.sqrt ((t : ℝ) - s)) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ (fun _ => hr))
  have h := (codeWalk_grid_block_length_clt s t hst).continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : (ℝ × ℝ) × ℝ => p.2 • p.1) (by fun_prop) hm
      (fun _ => aemeasurable_const)
  refine h.congr (fun n => ae_of_all _ (fun ω => ?_)) (ae_of_all _ (fun _ => rfl))
  dsimp only
  rw [smul_smul]
  by_cases hz : iidGridBlockLength s t n = 0
  · have he : ⌊(n : ℝ) * t⌋₊ = ⌊(n : ℝ) * s⌋₊ := by
      have hf := Nat.floor_mono (mul_le_mul_of_nonneg_left
        (show (s : ℝ) ≤ t from hst.le) (Nat.cast_nonneg n))
      unfold iidGridBlockLength at hz
      omega
    simp only [he, sub_self, Prod.fst_zero, Prod.snd_zero, Int.cast_zero,
      show ((0 : ℝ), (0 : ℝ)) = 0 from rfl, smul_zero]
  · rw [Real.sqrt_div (Nat.cast_nonneg _), div_eq_mul_inv,
      mul_right_comm, mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr
        (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz))), one_mul]

/-- Helper toward Lemma 4.11: evaluation of the interpolated iid walk is measurable. -/
theorem measurable_codeWalk_diffusiveInterpolation (n : ℕ) (t : ℝ≥0) :
    Measurable (fun ω => diffusiveInterpolation n (codeWalk ω) t) := by
  have h (k : ℕ) : Measurable (fun ω => codeWalk ω k) :=
    (measurable_pi_apply k).comp measurable_codeWalk
  have hr (k : ℕ) : Measurable (fun ω =>
      (((codeWalk ω k).1 : ℝ), ((codeWalk ω k).2 : ℝ))) :=
    (measurable_of_countable (fun z : ℤ × ℤ => ((z.1 : ℝ), (z.2 : ℝ)))).comp (h k)
  unfold diffusiveInterpolation walkLinearScalar
  dsimp only [ContinuousMap.coe_mk]
  exact (((hr _).fst.add (measurable_const.mul ((hr _).fst.sub (hr _).fst))).div_const _).prodMk
    (((hr _).snd.add (measurable_const.mul ((hr _).snd.sub (hr _).snd))).div_const _)

/-- Helper toward Lemma 4.11: evaluation of the grid step iid walk is measurable. -/
theorem measurable_codeWalk_diffusiveStep (n : ℕ) (t : ℝ≥0) :
    Measurable (fun ω => diffusiveStep n (codeWalk ω) t) := by
  exact (measurable_of_countable (fun z : ℤ × ℤ =>
    ((z.1 : ℝ) / Real.sqrt n, (z.2 : ℝ) / Real.sqrt n))).comp
    ((measurable_pi_apply _).comp measurable_codeWalk)

/-- Helper toward Lemma 4.11: the interpolation error in the actual product norm is uniform. -/
theorem norm_codeWalk_diffusiveStep_sub_interpolation_le (n : ℕ) (ω : ℕ → Fin 3)
    (t : ℝ≥0) :
    ‖diffusiveStep n (codeWalk ω) t - diffusiveInterpolation n (codeWalk ω) t‖ ≤
      1 / Real.sqrt n := by
  have h := diffusiveStep_sub_interpolation_abs_le n (codeWalk ω)
    (codeWalk_real_coord_increment_abs_le ω) t
  simpa only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs, max_le_iff] using h

/-- Helper toward Lemma 4.11: the deterministic interpolation error vanishes pointwise. -/
theorem codeWalk_interpolation_sub_step_tendsto (t : ℝ≥0) (ω : ℕ → Fin 3) :
    Tendsto (fun n : ℕ => diffusiveInterpolation n (codeWalk ω) t -
      diffusiveStep n (codeWalk ω) t) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (g := fun n : ℕ => 1 / Real.sqrt n) (fun _ => norm_nonneg _)
    (fun n => ?_)
    (tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))))
  rw [norm_sub_rev]
  exact norm_codeWalk_diffusiveStep_sub_interpolation_le n ω t

/-- Helper toward Lemma 4.11: the deterministic interpolation error vanishes in probability. -/
theorem codeWalk_interpolation_sub_step_tendstoInMeasure (t : ℝ≥0) :
    TendstoInMeasure iidCodeMeasure
      (fun (n : ℕ) ω => diffusiveInterpolation n (codeWalk ω) t -
        diffusiveStep n (codeWalk ω) t) atTop 0 := by
  exact tendstoInMeasure_of_tendsto_ae
    (fun n => ((measurable_codeWalk_diffusiveInterpolation n t).sub
      (measurable_codeWalk_diffusiveStep n t)).aestronglyMeasurable)
    (ae_of_all _ (codeWalk_interpolation_sub_step_tendsto t))

/-- Helper toward Lemma 4.11: interpolation increments have the same scaled Gaussian limit
as their grid increments. -/
theorem codeWalk_interpolation_block_clt (s t : ℝ≥0) (hst : s < t) :
    TendstoInDistribution
      (fun (n : ℕ) ω => diffusiveInterpolation n (codeWalk ω) t -
        diffusiveInterpolation n (codeWalk ω) s)
      atTop (fun z : ℝ × ℝ => Real.sqrt ((t : ℝ) - s) • (z.1, (z.2 - z.1) / 2))
      (fun _ : ℕ => iidCodeMeasure) iidEndpointLimitLaw := by
  have hg : TendstoInDistribution
      (fun (n : ℕ) ω => diffusiveStep n (codeWalk ω) t -
        diffusiveStep n (codeWalk ω) s)
      atTop (fun z : ℝ × ℝ => Real.sqrt ((t : ℝ) - s) • (z.1, (z.2 - z.1) / 2))
      (fun _ : ℕ => iidCodeMeasure) iidEndpointLimitLaw := by
    convert codeWalk_grid_block_clt s t hst using 1
    funext n ω
    ext <;> simp only [diffusiveStep, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul, Int.cast_sub, div_eq_mul_inv, mul_comm, mul_sub]
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ _ hg
  · apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact (((measurable_codeWalk_diffusiveInterpolation n t).sub
        (measurable_codeWalk_diffusiveInterpolation n s)).sub
        ((measurable_codeWalk_diffusiveStep n t).sub
        (measurable_codeWalk_diffusiveStep n s))).aestronglyMeasurable
    · apply ae_of_all
      intro ω
      have h := (codeWalk_interpolation_sub_step_tendsto t ω).sub
        (codeWalk_interpolation_sub_step_tendsto s ω)
      convert h using 1
      · funext n
        dsimp only [Pi.sub_apply]
        abel
      · simp only [sub_self, Pi.zero_apply]
  · intro n
    exact ((measurable_codeWalk_diffusiveInterpolation n t).sub
      (measurable_codeWalk_diffusiveInterpolation n s)).aemeasurable

/-- Helper toward Lemma 4.11: endpoints of finitely many ordered disjoint blocks are
jointly independent, retaining the walk's literal increment indexing. -/
theorem iIndepFun_codeWalk_disjoint_blocks {k : ℕ} (a m : Fin k → ℕ)
    (hsep : ∀ i j, i < j → a i + m i ≤ a j) :
    iIndepFun (fun i ω => codeWalk ω (a i + m i) - codeWalk ω (a i))
      iidCodeMeasure := by
  classical
  let e : (i : Fin k) × Fin (m i) → ℕ := fun p => a p.1 + p.2.val
  have he : Function.Injective e := by
    rintro ⟨i, p⟩ ⟨j, q⟩ h
    change a i + p.val = a j + q.val at h
    by_cases hij : i = j
    · subst j
      have hpq : p = q := Fin.ext (Nat.add_left_cancel h)
      subst q
      rfl
    · rcases lt_or_gt_of_ne hij with hij | hji
      · have hs := hsep i j hij
        have hp := p.isLt
        omega
      · have hs := hsep j i hji
        have hq := q.isLt
        omega
  let X (i : Fin k) (j : Fin (m i)) (ω : ℕ → Fin 3) :=
    codeWalk ω (a i + j.val + 1) - codeWalk ω (a i + j.val)
  have hm (i : Fin k) (j : Fin (m i)) : Measurable (X i j) :=
    measurable_codeWalk_increment _
  have hi := iIndepFun_codeWalk_increments.precomp he
  have hmap := hi.map_fun_eq_infinitePi_map
    (fun p => measurable_codeWalk_increment (e p))
  have hi' (i : Fin k) : iIndepFun (X i) iidCodeMeasure :=
    iIndepFun_codeWalk_increments.precomp
      (show Function.Injective (fun j : Fin (m i) => a i + j.val) from
        fun _ _ h => Fin.ext (Nat.add_left_cancel h))
  have hg : iIndepFun (fun i ω => fun j => X i j ω) iidCodeMeasure := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map
      (fun i => Measurable.of_eval (hm i))]
    have hc := congrArg
      (fun μ : Measure ((p : (i : Fin k) × Fin (m i)) → ℤ × ℤ) =>
        μ.map (MeasurableEquiv.piCurry (fun (i : Fin k) (_ : Fin (m i)) => ℤ × ℤ))) hmap
    rw [Measure.map_map (by fun_prop)
      (Measurable.of_eval (fun p => measurable_codeWalk_increment (e p)))] at hc
    change iidCodeMeasure.map (fun ω i j => X i j ω) =
      (Measure.infinitePi (fun p : (i : Fin k) × Fin (m i) =>
        iidCodeMeasure.map (X p.1 p.2))).map
          (MeasurableEquiv.piCurry (fun (i : Fin k) (_ : Fin (m i)) => ℤ × ℤ)) at hc
    rw [Measure.infinitePi_map_piCurry (μ := fun i j => iidCodeMeasure.map (X i j))] at hc
    change iidCodeMeasure.map (fun ω i j => X i j ω) =
      Measure.infinitePi (fun i => Measure.infinitePi
        (fun j => iidCodeMeasure.map (X i j))) at hc
    rw [hc]
    congr 1
    funext i
    exact (hi' i).map_fun_eq_infinitePi_map (hm i) |>.symm
  have hsum := hg.comp (fun i q => ∑ j : Fin (m i), q j) (by fun_prop)
  convert hsum using 1
  funext i ω
  dsimp only [Function.comp_def, X]
  simpa only [Fin.sum_univ_eq_sum_range
    (fun j => codeWalk ω (a i + j + 1) - codeWalk ω (a i + j))] using
      codeWalk_block_eq_sum ω (a i) (m i)

/-- Helper toward Lemma 4.11: joint grid increments over finitely many ordered disjoint
positive-duration blocks converge to independent scaled Gaussian vectors. The product
sample law and every scaling map are explicit. -/
theorem codeWalk_grid_disjoint_blocks_clt {k : ℕ} (s t : Fin k → ℝ≥0)
    (hst : ∀ i, s i < t i) (hsep : ∀ i j, i < j → t i ≤ s j) :
    TendstoInDistribution
      (fun (n : ℕ) ω i => (Real.sqrt (n : ℝ))⁻¹ •
        (((codeWalk ω ⌊(n : ℝ) * t i⌋₊ - codeWalk ω ⌊(n : ℝ) * s i⌋₊).1 : ℝ),
         ((codeWalk ω ⌊(n : ℝ) * t i⌋₊ - codeWalk ω ⌊(n : ℝ) * s i⌋₊).2 : ℝ)))
      atTop (fun z : Fin k → ℝ × ℝ => fun i =>
        Real.sqrt ((t i : ℝ) - s i) • ((z i).1, ((z i).2 - (z i).1) / 2))
      (fun _ : ℕ => iidCodeMeasure) (Measure.pi (fun _ : Fin k => iidEndpointLimitLaw)) := by
  classical
  let E := WithLp 2 (ℝ × ℝ)
  let X (n : ℕ) (i : Fin k) (ω : ℕ → Fin 3) : E :=
    WithLp.toLp 2 ((Real.sqrt (n : ℝ))⁻¹ •
      (((codeWalk ω ⌊(n : ℝ) * t i⌋₊ - codeWalk ω ⌊(n : ℝ) * s i⌋₊).1 : ℝ),
       ((codeWalk ω ⌊(n : ℝ) * t i⌋₊ - codeWalk ω ⌊(n : ℝ) * s i⌋₊).2 : ℝ)))
  let Y (i : Fin k) (z : ℝ × ℝ) : E :=
    WithLp.toLp 2 (Real.sqrt ((t i : ℝ) - s i) • (z.1, (z.2 - z.1) / 2))
  let ν := Measure.pi (fun _ : Fin k => iidEndpointLimitLaw)
  have hX (n : ℕ) (i : Fin k) : Measurable (X n i) := by
    apply (WithLp.measurable_toLp 2 (ℝ × ℝ)).comp
    exact (measurable_of_countable (fun z : ℤ × ℤ =>
      (Real.sqrt (n : ℝ))⁻¹ • ((z.1 : ℝ), (z.2 : ℝ)))).comp
      (((measurable_pi_apply _).comp measurable_codeWalk).sub
        ((measurable_pi_apply _).comp measurable_codeWalk))
  have hY (i : Fin k) : Measurable (Y i) := by
    exact (WithLp.measurable_toLp 2 (ℝ × ℝ)).comp (by fun_prop)
  have hclt (i : Fin k) : TendstoInDistribution (fun n => X n i) atTop (Y i)
      (fun _ => iidCodeMeasure) iidEndpointLimitLaw :=
    (codeWalk_grid_block_clt (s i) (t i) (hst i)).continuous_comp
      (WithLp.prod_continuous_toLp 2 ℝ ℝ)
  have hind (n : ℕ) : iIndepFun (X n) iidCodeMeasure := by
    let a (i : Fin k) := ⌊(n : ℝ) * s i⌋₊
    let m (i : Fin k) := iidGridBlockLength (s i) (t i) n
    have he (i : Fin k) : a i + m i = ⌊(n : ℝ) * t i⌋₊ :=
      Nat.add_sub_of_le (Nat.floor_mono (mul_le_mul_of_nonneg_left
        (show (s i : ℝ) ≤ t i from (hst i).le) (Nat.cast_nonneg n)))
    have hi := iIndepFun_codeWalk_disjoint_blocks a m (fun i j hij => by
      rw [he i]
      exact Nat.floor_mono (mul_le_mul_of_nonneg_left
        (show (t i : ℝ) ≤ s j from hsep i j hij) (Nat.cast_nonneg n)))
    have h := hi.comp (fun _ z => WithLp.toLp 2
      ((Real.sqrt (n : ℝ))⁻¹ • ((z.1 : ℝ), (z.2 : ℝ))))
      (fun _ => (WithLp.measurable_toLp 2 (ℝ × ℝ)).comp (measurable_of_countable _))
    simpa only [he, Function.comp_def] using h
  have hindY : iIndepFun (fun i z => Y i (z i)) ν :=
    iIndepFun_pi (fun i => (hY i).aemeasurable)
  have hmapY (i : Fin k) : ν.map (fun z => Y i (z i)) = iidEndpointLimitLaw.map (Y i) := by
    change ν.map (Y i ∘ Function.eval i) = _
    rw [← Measure.map_map (hY i) (measurable_pi_apply i),
      (measurePreserving_eval (fun _ : Fin k => iidEndpointLimitLaw) i).map_eq]
  have hj : TendstoInDistribution
      (fun n ω => WithLp.toLp 2 (fun i => X n i ω)) atTop
      (fun z => WithLp.toLp 2 (fun i => Y i (z i))) (fun _ => iidCodeMeasure) ν := by
    apply TendstoInDistribution.of_tendsto_charFun
    · intro n
      exact (WithLp.measurable_toLp 2 (Fin k → E)).comp
        (Measurable.of_eval (hX n)) |>.aemeasurable
    · exact (WithLp.measurable_toLp 2 (Fin k → E)).comp
        (Measurable.of_eval (fun i => (hY i).comp (measurable_pi_apply i))) |>.aemeasurable
    · intro u
      have he (n : ℕ) := (iIndepFun_iff_charFun_pi
        (fun i => (hX n i).aemeasurable)).mp (hind n) u
      have heY := (iIndepFun_iff_charFun_pi
        (fun i => ((hY i).comp (measurable_pi_apply i)).aemeasurable)).mp hindY u
      simp only [Function.comp_apply] at heY
      have hp := tendsto_finsetProd Finset.univ
        (fun i _ => (hclt i).tendsto_charFun (u i))
      have hl : charFun (ν.map (fun z => WithLp.toLp 2 (fun i => Y i (z i)))) u =
          ∏ i, charFun (iidEndpointLimitLaw.map (Y i)) (u i) := by
        rw [heY]
        exact Finset.prod_congr rfl (fun i _ => congrArg (fun μ => charFun μ (u i)) (hmapY i))
      rw [hl]
      exact hp.congr' (Eventually.of_forall (fun n => (he n).symm))
  have hc : Continuous (fun p : PiLp 2 (fun _ : Fin k => E) =>
      fun i => WithLp.ofLp (p i)) :=
    continuous_pi (fun i => (WithLp.prod_continuous_ofLp 2 ℝ ℝ).comp
      (PiLp.continuous_apply 2 (fun _ : Fin k => E) i))
  simpa only [Function.comp_def, WithLp.ofLp_toLp, PiLp.toLp_apply] using hj.continuous_comp hc

/-- Helper toward Lemma 4.11: joint polygonal increments on finitely many ordered disjoint
blocks converge to the product of the explicitly scaled endpoint Gaussian laws. -/
theorem codeWalk_interpolation_disjoint_blocks_clt {k : ℕ} (s t : Fin k → ℝ≥0)
    (hst : ∀ i, s i < t i) (hsep : ∀ i j, i < j → t i ≤ s j) :
    TendstoInDistribution
      (fun (n : ℕ) ω i => diffusiveInterpolation n (codeWalk ω) (t i) -
        diffusiveInterpolation n (codeWalk ω) (s i))
      atTop (fun z : Fin k → ℝ × ℝ => fun i =>
        Real.sqrt ((t i : ℝ) - s i) • ((z i).1, ((z i).2 - (z i).1) / 2))
      (fun _ : ℕ => iidCodeMeasure) (Measure.pi (fun _ : Fin k => iidEndpointLimitLaw)) := by
  have hg : TendstoInDistribution
      (fun (n : ℕ) ω i => diffusiveStep n (codeWalk ω) (t i) -
        diffusiveStep n (codeWalk ω) (s i))
      atTop (fun z : Fin k → ℝ × ℝ => fun i =>
        Real.sqrt ((t i : ℝ) - s i) • ((z i).1, ((z i).2 - (z i).1) / 2))
      (fun _ : ℕ => iidCodeMeasure) (Measure.pi (fun _ : Fin k => iidEndpointLimitLaw)) := by
    convert codeWalk_grid_disjoint_blocks_clt s t hst hsep using 1
    funext n ω i
    ext <;> simp only [diffusiveStep, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul, Int.cast_sub, div_eq_mul_inv, mul_comm, mul_sub]
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ _ hg
  · apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact (Measurable.of_eval (fun i =>
        (((measurable_codeWalk_diffusiveInterpolation n (t i)).sub
          (measurable_codeWalk_diffusiveInterpolation n (s i))).sub
          ((measurable_codeWalk_diffusiveStep n (t i)).sub
            (measurable_codeWalk_diffusiveStep n (s i)))))).aestronglyMeasurable
    · apply ae_of_all
      intro ω
      apply tendsto_pi_nhds.mpr
      intro i
      have h := (codeWalk_interpolation_sub_step_tendsto (t i) ω).sub
        (codeWalk_interpolation_sub_step_tendsto (s i) ω)
      convert h using 1
      · funext n
        dsimp only [Pi.sub_apply]
        abel
      · simp only [sub_self, Pi.zero_apply]
  · intro n
    exact (Measurable.of_eval (fun i =>
      (measurable_codeWalk_diffusiveInterpolation n (t i)).sub
        (measurable_codeWalk_diffusiveInterpolation n (s i)))).aemeasurable

/-- Helper toward Lemma 4.11: for strictly increasing observation times, consecutive
polygonal increments converge jointly to independent Gaussian increments. -/
theorem codeWalk_interpolation_consecutive_blocks_clt {k : ℕ} (t : Fin (k + 1) → ℝ≥0)
    (ht : StrictMono t) :
    TendstoInDistribution
      (fun (n : ℕ) ω (i : Fin k) => diffusiveInterpolation n (codeWalk ω) (t i.succ) -
        diffusiveInterpolation n (codeWalk ω) (t i.castSucc))
      atTop (fun z : Fin k → ℝ × ℝ => fun i =>
        Real.sqrt ((t i.succ : ℝ) - t i.castSucc) •
          ((z i).1, ((z i).2 - (z i).1) / 2))
      (fun _ : ℕ => iidCodeMeasure) (Measure.pi (fun _ : Fin k => iidEndpointLimitLaw)) :=
  codeWalk_interpolation_disjoint_blocks_clt (fun i => t i.castSucc) (fun i => t i.succ)
    (fun i => ht i.castSucc_lt_succ)
    (fun _ _ hij => ht.monotone (Fin.succ_le_castSucc_iff.mpr hij))

end DirectedDistances.RandomWalk
