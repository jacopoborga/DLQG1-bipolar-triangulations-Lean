/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.PitmanBessel3I
public import DirectedDistances.Probability.PitmanOneTime




public section

namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace WholePathSinc

private theorem finite_weight {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] (μ : Measure (X × ℝ)) [IsFiniteMeasure μ]
    (F : BoundedContinuousFunction X ℝ) (hF : ∀ x, 0 ≤ F x) :
    IsFiniteMeasure (μ.withDensity (fun p => ENNReal.ofReal (F p.1))) := by
  apply isFiniteMeasure_withDensity
  apply (lintegral_ofReal_ne_top_iff_integrable
    (f := fun p : X × ℝ => F p.1)
    (F.continuous.comp continuous_fst).measurable.aestronglyMeasurable
    (Eventually.of_forall (fun p => hF p.1))).2
  exact Integrable.mono' (integrable_const ‖F‖)
    (F.continuous.comp continuous_fst).measurable.aestronglyMeasurable
    (Eventually.of_forall (fun p => F.norm_coe_le_norm p.1))

private theorem weighted_integral {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] (μ : Measure (X × ℝ)) [IsFiniteMeasure μ]
    (F : BoundedContinuousFunction X ℝ) (hF : ∀ x, 0 ≤ F x)
    (g : ℝ → ℝ) (hg : Measurable g) :
    (∫ y, g y ∂(μ.withDensity (fun p => ENNReal.ofReal (F p.1))).map Prod.snd) =
      ∫ p, F p.1 * g p.2 ∂μ := by
  rw [integral_map (by fun_prop) hg.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hF _), smul_eq_mul]

/-- Helper toward Lemma 4.11: nonnegative bounded past weights turn joint sinc
tests into equality of finite measures on the terminal nonnegative coordinate. -/
theorem weighted_snd_map_eq_of_integral_sinc_eq
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    (μ ν : Measure (X × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ p ∂μ, 0 ≤ p.2) (hν : ∀ᵐ p ∂ν, 0 ≤ p.2)
    (F : BoundedContinuousFunction X ℝ) (hF : ∀ x, 0 ≤ F x)
    (h : ∀ a : ℝ, (∫ p, F p.1 * Real.sinc (a * p.2) ∂μ) =
      ∫ p, F p.1 * Real.sinc (a * p.2) ∂ν) :
    (μ.withDensity (fun p => ENNReal.ofReal (F p.1))).map Prod.snd =
      (ν.withDensity (fun p => ENNReal.ofReal (F p.1))).map Prod.snd := by
  have := finite_weight μ F hF
  have := finite_weight ν F hF
  apply OneTimeSinc.measure_eq_of_integral_sinc_eq_of_nonneg
  · exact (ae_map_iff (by fun_prop) measurableSet_Ici).mpr
      ((withDensity_absolutelyContinuous μ _).ae_le hμ)
  · exact (ae_map_iff (by fun_prop) measurableSet_Ici).mpr
      ((withDensity_absolutelyContinuous ν _).ae_le hν)
  · intro a
    rw [weighted_integral μ F hF _ (by fun_prop),
      weighted_integral ν F hF _ (by fun_prop)]
    exact h a

/-- Helper toward Lemma 4.11: a finite joint law with nonnegative terminal
coordinate is determined by all bounded continuous past tests times all sinc
tests of the terminal coordinate. The past space may in particular be `Fin k → ℝ`.
No density, moment, or conditional-law hypothesis is required. -/
theorem measure_eq_of_integral_mul_sinc_eq_of_nonneg
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [HasOuterApproxClosed X]
    (μ ν : Measure (X × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ p ∂μ, 0 ≤ p.2) (hν : ∀ᵐ p ∂ν, 0 ≤ p.2)
    (h : ∀ (F : BoundedContinuousFunction X ℝ) (a : ℝ),
      (∫ p, F p.1 * Real.sinc (a * p.2) ∂μ) =
        ∫ p, F p.1 * Real.sinc (a * p.2) ∂ν) : μ = ν := by
  have hr (t : Set ℝ) (ht : MeasurableSet t) :
      (μ.restrict (Prod.snd ⁻¹' t)).map Prod.fst =
        (ν.restrict (Prod.snd ⁻¹' t)).map Prod.fst := by
    apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
    intro f
    let F : BoundedContinuousFunction X ℝ :=
      ⟨⟨fun x => (f x : ℝ), NNReal.continuous_coe.comp f.continuous⟩, f.map_bounded'⟩
    have he := congrArg (fun ρ : Measure ℝ => ρ t)
      (weighted_snd_map_eq_of_integral_sinc_eq μ ν hμ hν F
        (fun x => (f x).coe_nonneg) (h F))
    rw [Measure.map_apply measurable_snd ht,
      Measure.map_apply measurable_snd ht,
      withDensity_apply _ (measurable_snd ht),
      withDensity_apply _ (measurable_snd ht)] at he
    rw [lintegral_map (by fun_prop) measurable_fst,
      lintegral_map (by fun_prop) measurable_fst]
    change (∫⁻ p in Prod.snd ⁻¹' t, ENNReal.ofReal (f p.1 : ℝ) ∂μ) =
      ∫⁻ p in Prod.snd ⁻¹' t, ENNReal.ofReal (f p.1 : ℝ) ∂ν at he
    simpa only [ENNReal.ofReal_coe_nnreal] using he
  apply Measure.ext_prod
  intro s t hs ht
  have he := congrArg (fun ρ : Measure X => ρ s) (hr t ht)
  rw [Measure.map_apply measurable_fst hs,
    Measure.map_apply measurable_fst hs,
    Measure.restrict_apply (measurable_fst hs),
    Measure.restrict_apply (measurable_fst hs)] at he
  exact he

/-- Helper toward Lemma 4.11: the joint sinc uniqueness statement on the
literal product of a finite real vector with the nonnegative half-line. -/
theorem measure_eq_of_integral_mul_sinc_eq_nnreal {k : ℕ}
    (μ ν : Measure ((Fin k → ℝ) × ℝ≥0))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (F : BoundedContinuousFunction (Fin k → ℝ) ℝ) (a : ℝ),
      (∫ p, F p.1 * Real.sinc (a * (p.2 : ℝ)) ∂μ) =
        ∫ p, F p.1 * Real.sinc (a * (p.2 : ℝ)) ∂ν) : μ = ν := by
  let e : ((Fin k → ℝ) × ℝ≥0) → ((Fin k → ℝ) × ℝ) :=
    fun p => (p.1, p.2)
  have he : MeasurableEmbedding e :=
    (continuous_fst.prodMk (NNReal.continuous_coe.comp continuous_snd)).measurableEmbedding
      (by
        intro p q hpq
        apply Prod.ext
        · exact congrArg (fun z : (Fin k → ℝ) × ℝ => z.1) hpq
        · exact NNReal.coe_injective
            (congrArg (fun z : (Fin k → ℝ) × ℝ => z.2) hpq))
  apply he.map_injective
  apply measure_eq_of_integral_mul_sinc_eq_of_nonneg
  · exact (ae_map_iff he.measurable.aemeasurable
      (measurableSet_Ici.preimage measurable_snd)).mpr
        (Eventually.of_forall (fun p => p.2.coe_nonneg))
  · exact (ae_map_iff he.measurable.aemeasurable
      (measurableSet_Ici.preimage measurable_snd)).mpr
        (Eventually.of_forall (fun p => p.2.coe_nonneg))
  · intro F a
    rw [integral_map he.measurable.aemeasurable (by fun_prop),
      integral_map he.measurable.aemeasurable (by fun_prop)]
    exact h F a

/-- Helper toward Lemma 4.11: past-weighted sinc expectations identify the
joint distribution of a finite real vector and a nonnegative terminal value,
also when the two random vectors live on different finite measure spaces. -/
theorem identDistrib_prod_of_integral_mul_sinc_eq_of_nonneg
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {k : ℕ} {X : Ω → Fin k → ℝ} {Y : Ω' → Fin k → ℝ}
    {U : Ω → ℝ} {V : Ω' → ℝ}
    (hXU : AEMeasurable (fun ω => (X ω, U ω)) P)
    (hYV : AEMeasurable (fun ω => (Y ω, V ω)) Q)
    (hU : ∀ᵐ ω ∂P, 0 ≤ U ω) (hV : ∀ᵐ ω ∂Q, 0 ≤ V ω)
    (h : ∀ (F : BoundedContinuousFunction (Fin k → ℝ) ℝ) (a : ℝ),
      (∫ ω, F (X ω) * Real.sinc (a * U ω) ∂P) =
        ∫ ω, F (Y ω) * Real.sinc (a * V ω) ∂Q) :
    IdentDistrib (fun ω => (X ω, U ω)) (fun ω => (Y ω, V ω)) P Q := by
  refine ⟨hXU, hYV, measure_eq_of_integral_mul_sinc_eq_of_nonneg _ _
    ((ae_map_iff hXU (measurableSet_Ici.preimage measurable_snd)).mpr hU)
    ((ae_map_iff hYV (measurableSet_Ici.preimage measurable_snd)).mpr hV) ?_⟩
  intro F a
  rw [integral_map hXU (by fun_prop), integral_map hYV (by fun_prop)]
  exact h F a

end WholePathSinc

local instance pitmanWholePathContinuousMapMeasurableSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    MeasurableSpace C(X, Y) := borel _
local instance pitmanWholePathContinuousMapBorelSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    BorelSpace C(X, Y) := ⟨rfl⟩
local instance pitmanWholePathContinuousMapSecondCountable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [LocallyCompactSpace X] [SecondCountableTopology Y] :
    SecondCountableTopology C(X, Y) := continuousPath_secondCountable

open DirectedDistances.RandomWalk

/-- Helper toward Lemma 4.11: the centered radial Gaussian sinc formula
has the exact elapsed-time variance factor, including zero variance. -/
theorem integral_sinc_gaussian_radial3_variance (u : ℝ≥0) (a : ℝ) :
    (∫ x : Fin 3 → ℝ,
      Real.sinc (a * Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2))
        ∂Measure.pi (fun _ : Fin 3 => gaussianReal 0 u)) =
      Real.exp (-(u : ℝ) * a ^ 2 / 2) := by
  let S (x : Fin 3 → ℝ) (i : Fin 3) := Real.sqrt u * x i
  have hmap : (Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)).map S =
      Measure.pi (fun _ : Fin 3 => gaussianReal 0 u) := by
    rw [Measure.pi_map_pi (fun _ =>
      (by fun_prop : AEMeasurable (fun x : ℝ => Real.sqrt u * x) (gaussianReal 0 1)))]
    congr 1
    funext i
    rw [gaussianReal_map_const_mul]
    congr 1
    · exact mul_zero _
    · apply NNReal.coe_injective
      simp only [NNReal.coe_mk, mul_one]
      exact Real.sq_sqrt u.coe_nonneg
  rw [← hmap, integral_map (by fun_prop : AEMeasurable S
    (Measure.pi (fun _ : Fin 3 => gaussianReal 0 1))) (by fun_prop)]
  have he (x : Fin 3 → ℝ) :
      Real.sqrt ((S x 0)^2 + (S x 1)^2 + (S x 2)^2) =
        Real.sqrt u * Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2) :=
    sqrt_sum_three_sq_const_mul _ (Real.sqrt_nonneg _) x
  simp_rw [he, ← mul_assoc]
  rw [integral_sinc_gaussian_radial3]
  congr 1
  rw [mul_pow, Real.sq_sqrt u.coe_nonneg]
  ring

/-- Helper toward Lemma 4.11: the three-coordinate increment has the exact
product centered Gaussian law with variance equal to the elapsed time. -/
theorem firstThree_increment_hasLaw
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (s u : ℝ≥0) :
    HasLaw (fun p (i : Fin 3) => p (s + u) i.castSucc - p s i.castSucc)
      (Measure.pi (fun _ : Fin 3 => gaussianReal 0 u)) W₄ := by
  have hi := (hI.precomp (Fin.castSucc_injective 3)).comp
    (fun _ : Fin 3 => fun f : C(ℝ≥0, ℝ) => f (s + u) - f s)
    (fun _ => (by fun_prop : Measurable (fun f : C(ℝ≥0, ℝ) => f (s + u) - f s)))
  exact hi.hasLaw_pi (fun i => (hB i.castSucc).toIsPreBrownianReal.shift s |>.hasLaw_eval u)

/-- Helper toward Lemma 4.11: the full three-coordinate future increment is
independent of every finite observation of the three-coordinate past. Times
may repeat, may equal `s`, or form the empty family. -/
theorem firstThree_increment_indep_past
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (s u : ℝ≥0) {k : ℕ} (t : Fin k → ℝ≥0) (ht : ∀ j, t j ≤ s) :
    IndepFun (fun p (i : Fin 3) => p (s + u) i.castSucc - p s i.castSucc)
      (fun p (i : Fin 3) (j : Fin k) => p (t j) i.castSucc) W₄ := by
  let A (i : Fin 3) (p : C(ℝ≥0, Fin 4 → ℝ)) (j : Fin k) := p (t j) i.castSucc
  let D (i : Fin 3) (p : C(ℝ≥0, Fin 4 → ℝ)) := p (s + u) i.castSucc - p s i.castSucc
  have hmA (i : Fin 3) : Measurable (A i) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_pi_apply i.castSucc).comp
      (continuous_eval_const (t j)).measurable
  have hAi (i : Fin 3) : HasLaw (A i) (W₄.map (A i)) W₄ :=
    ⟨(hmA i).aemeasurable, rfl⟩
  have hDi (i : Fin 3) : HasLaw (D i) (gaussianReal 0 u) W₄ :=
    (hB i.castSucc).toIsPreBrownianReal.shift s |>.hasLaw_eval u
  have hind (i : Fin 3) : IndepFun (D i) (A i) W₄ := by
    exact ((hB i.castSucc).toIsPreBrownianReal.indepFun_shift s).comp
      (measurable_pi_apply u)
      (measurable_pi_iff.mpr (fun j =>
        measurable_pi_apply (⟨t j, ht j⟩ : Set.Iic s)))
  have hJi := (hI.precomp (Fin.castSucc_injective 3)).comp
    (fun _ : Fin 3 => fun f : C(ℝ≥0, ℝ) =>
      (f (s + u) - f s, fun j : Fin k => f (t j)))
    (fun _ => (by fun_prop : Measurable (fun f : C(ℝ≥0, ℝ) =>
      (f (s + u) - f s, fun j : Fin k => f (t j)))))
  have hjoint := hJi.hasLaw_pi (fun i => (hind i).hasLaw_prod (hDi i) (hAi i))
  have hswap := measurePreserving_arrowProdEquivProdArrow ℝ (Fin k → ℝ) (Fin 3)
    (fun _ => gaussianReal 0 u) (fun i => W₄.map (A i))
  have hlaw := hswap.hasLaw.comp hjoint
  have hAp := (hI.precomp (Fin.castSucc_injective 3)).comp
    (fun _ : Fin 3 => fun f : C(ℝ≥0, ℝ) => fun j : Fin k => f (t j))
    (fun _ => (continuous_pi (fun j => continuous_eval_const (t j))).measurable)
  exact (indepFun_iff_hasLaw_prodMk_prod (firstThree_increment_hasLaw W₄ hB hI s u)
    (hAp.hasLaw_pi hAi)).mpr hlaw




theorem radial3_past_sinc_eq_gaussian_integral
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (s u : ℝ≥0) {k : ℕ} (t : Fin k → ℝ≥0) (ht : ∀ j, t j ≤ s)
    (F : BoundedContinuousFunction (Fin k → ℝ) ℝ) (a : ℝ) :
    (∫ p, F (fun j => radial3Path (firstThreePath p) (t j)) *
      Real.sinc (a * radial3Path (firstThreePath p) (s + u)) ∂W₄) =
    ∫ p, F (fun j => radial3Path (firstThreePath p) (t j)) *
      (∫ d : Fin 3 → ℝ, Real.sinc (a * Real.sqrt
        ((p s 0 + d 0)^2 + (p s 1 + d 1)^2 + (p s 2 + d 2)^2))
          ∂Measure.pi (fun _ : Fin 3 => gaussianReal 0 u)) ∂W₄ := by
  let τ : Fin (k + 1) → ℝ≥0 := Fin.snoc t s
  have hτ : ∀ j, τ j ≤ s := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [τ]
    · simpa [τ] using ht i
  let A (p : C(ℝ≥0, Fin 4 → ℝ)) (i : Fin 3) (j : Fin (k + 1)) :=
    p (τ j) i.castSucc
  let D (p : C(ℝ≥0, Fin 4 → ℝ)) (i : Fin 3) :=
    p (s + u) i.castSucc - p s i.castSucc
  let G := Measure.pi (fun _ : Fin 3 => gaussianReal 0 u)
  let K (z : (Fin 3 → Fin (k + 1) → ℝ) × (Fin 3 → ℝ)) :=
    F (fun j : Fin k => Real.sqrt
      ((z.1 0 j.castSucc)^2 + (z.1 1 j.castSucc)^2 + (z.1 2 j.castSucc)^2)) *
      Real.sinc (a * Real.sqrt
        ((z.1 0 (Fin.last k) + z.2 0)^2 +
         (z.1 1 (Fin.last k) + z.2 1)^2 +
         (z.1 2 (Fin.last k) + z.2 2)^2))
  have hmA : Measurable A := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_pi_apply i.castSucc).comp (continuous_eval_const (τ j)).measurable
  have hK : Continuous K := by dsimp [K]; fun_prop
  have hKi : Integrable K ((W₄.map A).prod G) := by
    apply Integrable.mono' (integrable_const ‖F‖) hK.measurable.aestronglyMeasurable
    filter_upwards [] with z
    dsimp only [K]
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one _) (abs_nonneg _)).trans
      (by simpa only [mul_one, Real.norm_eq_abs] using F.norm_coe_le_norm _)
  have hlaw := (firstThree_increment_indep_past W₄ hB hI s u τ hτ).symm.hasLaw_prod
    (hasLaw_map hmA.aemeasurable) (firstThree_increment_hasLaw W₄ hB hI s u)
  have he := hlaw.integral_comp hK.measurable.aestronglyMeasurable
  rw [integral_prod K hKi] at he
  have hmInner : AEStronglyMeasurable
      (fun z => ∫ d, K (z, d) ∂G) (W₄.map A) := hKi.integral_prod_left.aestronglyMeasurable
  rw [integral_map hmA.aemeasurable hmInner] at he
  have hleft : (fun p => K (A p, D p)) =
      (fun p => F (fun j => radial3Path (firstThreePath p) (t j)) *
        Real.sinc (a * radial3Path (firstThreePath p) (s + u))) := by
    funext p
    dsimp [K, A, D, τ, radial3Path, firstThreePath]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, add_sub_cancel]
  change (∫ p, K (A p, D p) ∂W₄) = _ at he
  rw [hleft] at he
  exact he.trans (integral_congr_ae (Eventually.of_forall (fun p => by
    dsimp [K, A, τ, radial3Path, firstThreePath, G]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    exact integral_const_mul _ _)))











































end DirectedDistances.Probability
