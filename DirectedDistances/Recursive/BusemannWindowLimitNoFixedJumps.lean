module

public import DirectedDistances.Recursive.BusemannWindowLimit
public import DirectedDistances.Recursive.BusemannWindowLimitSDP
public import DirectedDistances.Probability.SkorokhodJ1WindowContinuityTimes
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Real.Cardinality

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.RandomWalk DirectedDistances.Probability
open scoped Topology ENNReal

/-- Helper toward Theorem 1.6 (thm-busemann-conv); conditional on hind/hsym;
For a càdlàg path, increments across sequences approaching from either side
converge to its fixed-time jump. -/
theorem cadlag_window_increment_tendsto_jump
    {T : ℝ} (hT : 0 < T) (x : J1WindowD T hT) (t : J1Window T)
    (s s' : ℕ → J1Window T)
    (hs : Tendsto s atTop (𝓝[<] t))
    (hs' : Tendsto s' atTop (𝓝[>] t)) :
    Tendsto (fun n => x.path.1 (s' n) - x.path.1 (s n)) atTop
      (𝓝 (x.path.1 t - x.path.1.leftLim t)) := by
  have hleft := (x.path.2.tendsto_nhdsLT_leftLim t).comp hs
  have hright := (x.path.2.isRightContinuous t).tendsto.comp hs'
  exact hright.sub hleft

/-- Helper toward Theorem 1.6 (thm-busemann-conv); conditional on hind/hsym;
If real random variables converge almost everywhere and their characteristic
functions converge to those of zero, the limit has the Dirac law at zero. -/
theorem measure_map_eq_dirac_of_ae_tendsto_charFun
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXn : ∀ n, AEMeasurable (Xn n) μ) (hX : AEMeasurable X μ)
    (hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => Xn n x) atTop (𝓝 (X x)))
    (hcf : ∀ u : ℝ, Tendsto (fun n => charFun (μ.map (Xn n)) u)
      atTop (𝓝 1)) :
    μ.map X = Measure.dirac (0 : ℝ) := by
  have hbound : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
  have hchar_eq (u : ℝ) : charFun (μ.map X) u = 1 := by
    let g : ℝ → ℂ := fun r => Complex.exp ((u : ℂ) * (r : ℂ) * Complex.I)
    let F : ℕ → Ω → ℂ := fun n x => g (Xn n x)
    let f : Ω → ℂ := fun x => g (X x)
    have hgcont : Continuous g := by fun_prop
    have hgmeas : Measurable g := hgcont.measurable
    have hmeas (n : ℕ) : AEStronglyMeasurable (F n) μ := by
      exact (hgmeas.comp_aemeasurable (hXn n)).aestronglyMeasurable
    have hboundF (n : ℕ) : ∀ᵐ x ∂μ, ‖F n x‖ ≤ (fun _ : Ω => (1 : ℝ)) x := by
      filter_upwards [] with x
      simp [F, g, ← Complex.ofReal_mul]
    have hpointF : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
      filter_upwards [hpoint] with x hx
      exact hgcont.continuousAt.tendsto.comp hx
    have hInt := tendsto_integral_of_dominated_convergence
      (F := F) (f := f) (fun _ => 1) hmeas hbound hboundF hpointF
    have hmapXn (n : ℕ) : charFun (μ.map (Xn n)) u = ∫ x, F n x ∂μ := by
      rw [charFun_apply_real, integral_map (hXn n) (by fun_prop)]
    have hmapX : charFun (μ.map X) u = ∫ x, f x ∂μ := by
      rw [charFun_apply_real, integral_map hX (by fun_prop)]
    have hInt' := hInt.congr' (Eventually.of_forall fun n => (hmapXn n).symm)
    have hInt'' : Tendsto (fun n => charFun (μ.map (Xn n)) u) atTop
        (𝓝 (charFun (μ.map X) u)) := by
      simpa only [hmapX] using hInt'
    exact tendsto_nhds_unique hInt'' (hcf u)
  apply Measure.ext_of_charFun
  funext u
  rw [hchar_eq]
  simp [charFun_dirac]

private theorem charFun_map_finTwo_secondCoord
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) (u : ℝ) :
    charFun (μ.map (fun z => z (1 : Fin 2))) u =
      charFun μ (EuclideanSpace.single (1 : Fin 2) u) := by
  let p : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
    PiLp.proj (p := 2) (β := fun _ : Fin 2 => ℝ) 1
  have hp : (fun z : EuclideanSpace ℝ (Fin 2) => z (1 : Fin 2)) = p := by
    funext z
    rfl
  rw [hp, charFun_map_eq_charFunDual_smul]
  have hdual : u • p =
      InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin 2))
        (EuclideanSpace.single (1 : Fin 2) u) := by
    ext z
    simp [p, EuclideanSpace.inner_single_left]
  rw [hdual, ← charFun_eq_charFunDual_toDualMap]

private theorem cumulativeSum_finTwo_diff
    (z : EuclideanSpace ℝ (Fin 2)) :
    (WithLp.ofLp (cumulativeSum z) (1 : Fin 2)) -
        (WithLp.ofLp (cumulativeSum z) (0 : Fin 2)) = z 1 := by
  let e : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (Fin 2 → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)
  have he (y : Fin 2 → ℝ) (i : Fin 2) : (e.symm y) i = y i := by
    change e (e.symm y) i = y i
    rw [e.apply_symm_apply]
  have hz (i : Fin 2) : (e z) i = z i := rfl
  have happly (i : Fin 2) : (WithLp.ofLp (cumulativeSum z)) i =
      ∑ j ∈ Finset.Iic i, z j := by
    change (e.symm ((ContinuousLinearMap.pi fun r =>
      ∑ j ∈ Finset.Iic r,
        ContinuousLinearMap.proj (ι := Fin 2) (φ := fun _ : Fin 2 => ℝ) j)
      (e z))) i = _
    rw [he]
    simp only [ContinuousLinearMap.pi_apply, sum_apply,
      ContinuousLinearMap.proj_apply]
    exact Finset.sum_congr rfl fun j _ => hz j
  have h0 := happly (0 : Fin 2)
  have h1 := happly (1 : Fin 2)
  have h0' : Finset.Iic (0 : Fin 2) = {0} := by
    ext i
    simp only [Finset.mem_Iic, Finset.mem_singleton]
    omega
  have h1' : Finset.Iic (1 : Fin 2) = Finset.univ := by
    ext i
    simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
    omega
  rw [h0'] at h0
  rw [h1'] at h1
  simp only [Finset.sum_singleton] at h0
  have hsum : (∑ i : Fin 2, z i) = z 0 + z 1 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_one]
    rfl
  rw [hsum] at h1
  rw [h1, h0]
  ring

/-- The two-coordinate FDD law gives the stable characteristic function of a
window increment. -/
private theorem window_increment_charFun_of_fdd
    {T : ℝ} {hT : 0 < T} (ν : ProbabilityMeasure (J1WindowD T hT))
    (t : ℕ → J1Window T) (L : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    (κ : ℂ) (α u : ℝ) (hα : α ≠ 0)
    (hEval : ν.map (windowEvalVec (fun i : Fin 2 => t (i.val + 1))) =
      (L.map (cumulativeSum (k := 2))).map WithLp.ofLp)
    (hchar : ∀ θ : EuclideanSpace ℝ (Fin 2),
      charFun (L : Measure _) θ = ∏ i : Fin 2, Complex.exp
        (-((((t (i.val + 1) : ℝ) - (t i.val : ℝ) : ℝ) : ℂ) *
          ((if 0 ≤ θ i then κ else star κ) * (|θ i| ^ α : ℝ))))) :
    charFun ((ν : Measure _).map
      (fun x : J1WindowD T hT => x.path.1 (t 2) - x.path.1 (t 1))) u =
      Complex.exp (-((((t 2 : ℝ) - (t 1 : ℝ) : ℝ) : ℂ) *
        ((if 0 ≤ u then κ else star κ) * (|u| ^ α : ℝ)))) := by
  let d : (Fin 2 → ℝ) → ℝ := fun v => v 1 - v 0
  have hd : Measurable d := by fun_prop
  have heval : Measurable (windowEvalVec
      (fun i : Fin 2 => t (i.val + 1)) : J1WindowD T hT → Fin 2 → ℝ) :=
    measurable_windowEvalVec _
  have hEval' : ((ν : Measure _).map (windowEvalVec
      (fun i : Fin 2 => t (i.val + 1)))) =
      (((L : Measure _).map (cumulativeSum (k := 2))).map WithLp.ofLp) :=
    congrArg (fun p : ProbabilityMeasure (Fin 2 → ℝ) =>
      (p : Measure (Fin 2 → ℝ))) hEval
  have hmap : ((ν : Measure _).map
      (fun x : J1WindowD T hT => x.path.1 (t 2) - x.path.1 (t 1))) =
      (((ν : Measure _).map (windowEvalVec
        (fun i : Fin 2 => t (i.val + 1)))).map d) := by
    rw [Measure.map_map hd heval]
    rfl
  have hcomp : (fun z : EuclideanSpace ℝ (Fin 2) =>
      d (WithLp.ofLp (cumulativeSum z))) = fun z => z 1 := by
    funext z
    dsimp [d]
    exact cumulativeSum_finTwo_diff z
  have hlaw : ((ν : Measure _).map
      (fun x : J1WindowD T hT => x.path.1 (t 2) - x.path.1 (t 1))) =
      (L : Measure _).map (fun z : EuclideanSpace ℝ (Fin 2) => z 1) := by
    rw [hmap, hEval']
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
  rw [hlaw, charFun_map_finTwo_secondCoord, hchar
    (EuclideanSpace.single (1 : Fin 2) u)]
  simp [EuclideanSpace.single, PiLp.single_apply, hα]

private theorem dense_of_countable_compl_window {T : ℝ} (hT : 0 < T)
    (E : Set (J1Window T)) (hE : Eᶜ.Countable) : Dense E := by
  rw [Metric.dense_iff]
  intro x r hr
  let a : ℝ := max 0 ((x : ℝ) - r / 2)
  let b : ℝ := min T ((x : ℝ) + r / 2)
  have hab : a < b := by
    dsimp [a, b]
    exact max_lt (lt_min hT (by linarith [x.property.1]))
      (lt_min (by linarith [x.property.2]) (by linarith))
  let B : Set ℝ := Subtype.val '' Eᶜ
  have hB : B.Countable := hE.image Subtype.val
  have hnot : ¬ Set.Ioo a b ⊆ B := by
    intro hsub
    exact (not_le_of_gt hab)
      (Cardinal.Real.Ioo_countable_iff.mp (hB.mono hsub))
  obtain ⟨y, hy, hyB⟩ := Set.not_subset.mp hnot
  have hy0 : 0 ≤ y := (le_max_left _ _).trans hy.1.le
  have hyT : y ≤ T := hy.2.le.trans (min_le_left _ _)
  let z : J1Window T := ⟨y, hy0, hyT⟩
  refine ⟨z, ?_, ?_⟩
  · change |y - (x : ℝ)| < r
    have hlo := (le_max_right 0 ((x : ℝ) - r / 2)).trans_lt hy.1
    have hhi := hy.2.trans_le (min_le_right T ((x : ℝ) + r / 2))
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · by_contra hz
    exact hyB ⟨z, hz, rfl⟩

private theorem fixed_time_continuous_of_increment_charFun
    {T : ℝ} (hT : 0 < T) (ν : ProbabilityMeasure (J1WindowD T hT))
    (t : J1Window T) (ht0 : 0 < (t : ℝ)) (_htT : (t : ℝ) < T)
    (s s' : ℕ → J1Window T)
    (hs : Tendsto s atTop (𝓝[<] t))
    (hs' : Tendsto s' atTop (𝓝[>] t))
    (hcf : ∀ u : ℝ, Tendsto
      (fun n => charFun ((ν : Measure _).map
        (fun x : J1WindowD T hT => x.path.1 (s' n) - x.path.1 (s n))) u)
      atTop (𝓝 1)) :
    ∀ᵐ x : J1WindowD T hT ∂(ν : Measure (J1WindowD T hT)),
      ContinuousAt x.path.1 t := by
  let Xn : ℕ → J1WindowD T hT → ℝ := fun n x =>
    x.path.1 (s' n) - x.path.1 (s n)
  let X : J1WindowD T hT → ℝ := fun x => x.path.1 t - x.path.1.leftLim t
  have hXn (n : ℕ) : AEMeasurable (Xn n) (ν : Measure _) := by
    exact ((measurable_j1WindowD_eval hT (s' n)).sub
      (measurable_j1WindowD_eval hT (s n))).aemeasurable
  have hXmeas : Measurable X := by
    exact (measurable_j1WindowD_eval hT t).sub
      (measurable_j1WindowD_leftLim hT t ht0)
  have hX : AEMeasurable X (ν : Measure _) := hXmeas.aemeasurable
  have hpoint : ∀ᵐ x : J1WindowD T hT ∂(ν : Measure _),
      Tendsto (fun n => Xn n x) atTop (𝓝 (X x)) := by
    filter_upwards [] with x
    exact cadlag_window_increment_tendsto_jump hT x t s s' hs hs'
  have hdirac := measure_map_eq_dirac_of_ae_tendsto_charFun
    (ν : Measure _) Xn X hXn hX hpoint hcf
  have hmass : (ν : Measure _) {x | X x = 0} = 1 := by
    have h := congrArg (fun μ : Measure ℝ => μ {0}) hdirac
    rw [Measure.map_apply hXmeas (measurableSet_singleton 0)] at h
    have hset : X ⁻¹' ({0} : Set ℝ) = {x | X x = 0} := by
      ext x
      rfl
    rw [hset] at h
    simpa using h
  have hzero : ∀ᵐ x ∂(ν : Measure _), X x = 0 := by
    rw [ae_iff]
    have hbadset : {x | X x ≠ 0} = {x | ¬ X x = 0} := by
      ext x
      simp
    have hcompl : {x | ¬ X x = 0} = {x | X x = 0}ᶜ := by
      ext x
      simp
    have hbad : (ν : Measure _) {x | X x ≠ 0} = 0 := by
      have hc := measure_compl (μ := (ν : Measure (J1WindowD T hT)))
        (s := {x | X x = 0}) (hXmeas (measurableSet_singleton 0))
        (measure_ne_top (ν : Measure (J1WindowD T hT)) {x | X x = 0})
      rw [hmass] at hc
      rw [measure_univ, tsub_self] at hc
      rw [← hcompl] at hc
      rw [hbadset]
      exact hc
    rw [← hbadset]
    exact hbad
  filter_upwards [hzero] with x hx
  apply (cadlag_continuousAt_iff_j1WindowJump_eq_zero x t).2
  simp [j1WindowJump, ne_of_gt ht0, X, hx]

private theorem fixed_time_continuous_of_stable_fdd
    {T : ℝ} (hT : 0 < T) (ν : ProbabilityMeasure (J1WindowD T hT))
    (S : Set (J1Window T)) (hS : Sᶜ.Countable) (κ : ℂ) (α : ℝ)
    (hfdd : ∀ (q : ℕ → J1Window T), (q 0 : ℝ) = 0 → Monotone q →
      q 1 ∈ S → q 2 ∈ S →
      ∃ L : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)),
        (∀ θ : EuclideanSpace ℝ (Fin 2),
          charFun (L : Measure _) θ = ∏ i : Fin 2, Complex.exp
            (-((((q (i.val + 1) : ℝ) - (q i.val : ℝ) : ℝ) : ℂ) *
              ((if 0 ≤ θ i then κ else star κ) * (|θ i| ^ α : ℝ))))) ∧
        ν.map (windowEvalVec (fun i : Fin 2 => q (i.val + 1))) =
          (L.map (cumulativeSum (k := 2))).map WithLp.ofLp)
    (hα : α ≠ 0) (t : J1Window T) (ht0 : 0 < (t : ℝ))
    (htT : (t : ℝ) < T) :
    ∀ᵐ x : J1WindowD T hT ∂(ν : Measure (J1WindowD T hT)),
      ContinuousAt x.path.1 t := by
  classical
  have hdense := dense_of_countable_compl_window hT S hS
  let zero : J1Window T := ⟨0, le_rfl, hT.le⟩
  let endpoint : J1Window T := ⟨T, hT.le, le_rfl⟩
  obtain ⟨s, _, hsmem, hsnhds⟩ :=
    hdense.exists_seq_strictMono_tendsto_of_lt (x := t) (y := zero) ht0
  have htEnd : t < endpoint := by
    change (t : ℝ) < T
    exact htT
  obtain ⟨s', _, hspmem, hspnhds⟩ :=
    hdense.exists_seq_strictAnti_tendsto_of_lt (x := t) (y := endpoint) htEnd
  have hs : Tendsto s atTop (𝓝[<] t) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within s hsnhds
      (Filter.Eventually.of_forall fun n => (hsmem n).1.2)
  have hs' : Tendsto s' atTop (𝓝[>] t) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within s' hspnhds
      (Filter.Eventually.of_forall fun n => (hspmem n).1.1)
  let q : ℕ → ℕ → J1Window T := fun n j =>
    if j = 0 then zero else if j = 1 then s n else s' n
  have hqzero (n : ℕ) : (q n 0 : ℝ) = 0 := by
    simp [q, zero]
  have hpair (n : ℕ) : s n < s' n :=
    (hsmem n).1.2.trans (hspmem n).1.1
  have hqmono (n : ℕ) : Monotone (q n) := by
    intro i j hij
    by_cases hi0 : i = 0
    · subst i
      change (0 : ℝ) ≤ (q n j : ℝ)
      exact (q n j).property.1
    · have hj0 : j ≠ 0 := by omega
      by_cases hi1 : i = 1
      · subst i
        by_cases hj1 : j = 1
        · subst j
          rfl
        · have hle : (s n : ℝ) ≤ (s' n : ℝ) := le_of_lt (hpair n)
          simpa [q, hj0, hj1] using hle
      · have hj1 : j ≠ 1 := by omega
        simp [q, hi0, hi1, hj0, hj1]
  have hqone (n : ℕ) : q n 1 = s n := by simp [q]
  have hqtwo (n : ℕ) : q n 2 = s' n := by simp [q]
  have hcf : ∀ u : ℝ, Tendsto
      (fun n => charFun ((ν : Measure _).map
        (fun x : J1WindowD T hT => x.path.1 (s' n) - x.path.1 (s n))) u)
      atTop (𝓝 1) := by
    intro u
    let c : ℂ := (if 0 ≤ u then κ else star κ) * (|u| ^ α : ℝ)
    let deltaC : ℕ → ℂ := fun n => (((s' n : ℝ) - (s n : ℝ) : ℝ) : ℂ)
    have hformula (n : ℕ) :
        charFun ((ν : Measure _).map
          (fun x : J1WindowD T hT => x.path.1 (s' n) - x.path.1 (s n))) u =
          Complex.exp (-(deltaC n * c)) := by
      obtain ⟨L, hchar, hEval⟩ := hfdd (q n) (hqzero n) (hqmono n)
        (by simpa [hqone] using (hsmem n).2)
        (by simpa [hqtwo] using (hspmem n).2)
      have hh := window_increment_charFun_of_fdd ν (q n) L κ α u hα hEval hchar
      simpa [q, c, deltaC] using hh
    have hsval : Tendsto (fun n => (s n : ℝ)) atTop (𝓝 (t : ℝ)) :=
      tendsto_subtype_rng.1 (hs.mono_right nhdsWithin_le_nhds)
    have hspval : Tendsto (fun n => (s' n : ℝ)) atTop (𝓝 (t : ℝ)) :=
      tendsto_subtype_rng.1 (hs'.mono_right nhdsWithin_le_nhds)
    have hdelta : Tendsto (fun n => (s' n : ℝ) - (s n : ℝ))
        atTop (𝓝 (0 : ℝ)) := by
      simpa using hspval.sub hsval
    have hdeltaC : Tendsto
        deltaC atTop (𝓝 (0 : ℂ)) := by
      change Tendsto (Complex.ofReal ∘
        (fun n => (s' n : ℝ) - (s n : ℝ))) atTop (𝓝 (0 : ℂ))
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp hdelta
    have harg : Tendsto
        (fun n => -(deltaC n * c)) atTop (𝓝 (0 : ℂ)) := by
      simpa [c] using (hdeltaC.mul_const c).neg
    have hexp0 : Tendsto
        (fun n => Complex.exp (-(deltaC n * c)))
        atTop (𝓝 (Complex.exp 0)) := by
      change Tendsto (Complex.exp ∘ fun n => -(deltaC n * c))
        atTop (𝓝 (Complex.exp 0))
      exact Complex.continuous_exp.continuousAt.tendsto.comp harg
    have hexp : Tendsto
        (fun n => Complex.exp (-(deltaC n * c))) atTop (𝓝 1) := by
      simpa only [Complex.exp_zero] using hexp0
    exact hexp.congr' (Filter.Eventually.of_forall fun n => (hformula n).symm)
  exact fixed_time_continuous_of_increment_charFun hT ν t ht0 htT s s' hs hs' hcf

private theorem ldp_selected_window_continuity
    {T : ℝ} (hT : 0 < T)
    (ν : ProbabilityMeasure (J1WindowD T hT)) (S : Set (J1Window T))
    (hS : Sᶜ.Countable)
    (hfdd : ∀ (m : ℕ) (t : ℕ → J1Window T), (t 0 : ℝ) = 0 → Monotone t →
      (∀ i : Fin m, t (i.val + 1) ∈ S) →
      let a : ℝ := ((3 + ldpF iidCodeMeasure busemannLDPMeasurableVersion 0) / 2) ^
        (1 / 3 : ℝ)
      let κ : ℂ := ((1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (a : ℂ)
      0 < a ∧ ∃ L : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)),
        (∀ θ : EuclideanSpace ℝ (Fin m), charFun (L : Measure _) θ = ∏ i : Fin m,
          Complex.exp (-((((t (i.val + 1) : ℝ) - (t i.val : ℝ) : ℝ) : ℂ) *
            ((if 0 ≤ θ i then κ else star κ) * (|θ i| ^ (2 / 3 : ℝ) : ℝ))))) ∧
        ν.map (windowEvalVec (fun i : Fin m => t (i.val + 1))) =
          (L.map (cumulativeSum (k := m))).map WithLp.ofLp)
    (t : J1Window T) (ht0 : 0 < (t : ℝ)) (htT : (t : ℝ) < T) :
    ∀ᵐ x : J1WindowD T hT ∂(ν : Measure (J1WindowD T hT)),
      ContinuousAt x.path.1 t := by
  let a : ℝ := ((3 + ldpF iidCodeMeasure busemannLDPMeasurableVersion 0) / 2) ^
    (1 / 3 : ℝ)
  let κ : ℂ := ((1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (a : ℂ)
  let α : ℝ := 2 / 3
  have hfdd' : ∀ (q : ℕ → J1Window T), (q 0 : ℝ) = 0 → Monotone q →
      q 1 ∈ S → q 2 ∈ S →
      ∃ L : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)),
        (∀ θ : EuclideanSpace ℝ (Fin 2),
          charFun (L : Measure _) θ = ∏ i : Fin 2, Complex.exp
            (-((((q (i.val + 1) : ℝ) - (q i.val : ℝ) : ℝ) : ℂ) *
              ((if 0 ≤ θ i then κ else star κ) * (|θ i| ^ α : ℝ))))) ∧
        ν.map (windowEvalVec (fun i : Fin 2 => q (i.val + 1))) =
          (L.map (cumulativeSum (k := 2))).map WithLp.ofLp := by
    intro q hq0 hqmono hq1 hq2
    have htimes : ∀ i : Fin 2, q (i.val + 1) ∈ S := by
      intro i
      fin_cases i
      · simpa using hq1
      · simpa using hq2
    obtain ⟨_, L, hchar, hEval⟩ := hfdd 2 q hq0 hqmono htimes
    refine ⟨L, ?_, hEval⟩
    simpa [κ, a, α] using hchar
  exact fixed_time_continuous_of_stable_fdd hT ν S hS κ α hfdd'
    (by norm_num [α]) t ht0 htT

private theorem sdp_selected_window_continuity
    {T : ℝ} (hT : 0 < T)
    (ν : ProbabilityMeasure (J1WindowD T hT)) (S : Set (J1Window T))
    (hS : Sᶜ.Countable)
    (hfdd : ∀ (m : ℕ) (t : ℕ → J1Window T), (t 0 : ℝ) = 0 → Monotone t →
      (∀ i : Fin m, t (i.val + 1) ∈ S) →
      let b : ℝ := (SDPMasterFromLaw.sdpG iidCodeMeasure
        busemannSDPMeasurableVersion (-1)) ^ (2 / 3 : ℝ)
      let κ : ℂ := ((1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (b : ℂ)
      0 < b ∧ ∃ L : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)),
        (∀ θ : EuclideanSpace ℝ (Fin m), charFun (L : Measure _) θ = ∏ i : Fin m,
          Complex.exp (-((((t (i.val + 1) : ℝ) - (t i.val : ℝ) : ℝ) : ℂ) *
            ((if 0 ≤ θ i then κ else star κ) * (|θ i| ^ (4 / 3 : ℝ) : ℝ))))) ∧
        ν.map (windowEvalVec (fun i : Fin m => t (i.val + 1))) =
          (L.map (cumulativeSum (k := m))).map WithLp.ofLp)
    (t : J1Window T) (ht0 : 0 < (t : ℝ)) (htT : (t : ℝ) < T) :
    ∀ᵐ x : J1WindowD T hT ∂(ν : Measure (J1WindowD T hT)),
      ContinuousAt x.path.1 t := by
  let b : ℝ := (SDPMasterFromLaw.sdpG iidCodeMeasure
    busemannSDPMeasurableVersion (-1)) ^ (2 / 3 : ℝ)
  let κ : ℂ := ((1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (b : ℂ)
  let α : ℝ := 4 / 3
  have hfdd' : ∀ (q : ℕ → J1Window T), (q 0 : ℝ) = 0 → Monotone q →
      q 1 ∈ S → q 2 ∈ S →
      ∃ L : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)),
        (∀ θ : EuclideanSpace ℝ (Fin 2),
          charFun (L : Measure _) θ = ∏ i : Fin 2, Complex.exp
            (-((((q (i.val + 1) : ℝ) - (q i.val : ℝ) : ℝ) : ℂ) *
              ((if 0 ≤ θ i then κ else star κ) * (|θ i| ^ α : ℝ))))) ∧
        ν.map (windowEvalVec (fun i : Fin 2 => q (i.val + 1))) =
          (L.map (cumulativeSum (k := 2))).map WithLp.ofLp := by
    intro q hq0 hqmono hq1 hq2
    have htimes : ∀ i : Fin 2, q (i.val + 1) ∈ S := by
      intro i
      fin_cases i
      · simpa using hq1
      · simpa using hq2
    obtain ⟨_, L, hchar, hEval⟩ := hfdd 2 q hq0 hqmono htimes
    refine ⟨L, ?_, hEval⟩
    simpa [κ, b, α] using hchar
  exact fixed_time_continuous_of_stable_fdd hT ν S hS κ α hfdd'
    (by norm_num [α]) t ht0 htT

/-- Helper toward Theorem 1.6 (thm-busemann-conv); conditional on hind/hsym;
The selected LDP window limit has almost surely continuous paths at each fixed
time strictly before the window endpoint. -/
theorem ldp_busemann_window_fixed_time_continuous
    (hind : iIndepFun (fun j ω =>
      ldpIncrement busemannLDPMeasurableVersion j ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω =>
        -ldpIncrement busemannLDPMeasurableVersion 0 ω))
    {T : ℝ} (hT : 0 < T) :
    let ν := Classical.choose (ldp_busemann_window_tendsto hind hsym hT)
    ∀ t : J1Window T, (t : ℝ) < T →
      ∀ᵐ x ∂(ν : Measure (J1WindowD T hT)), ContinuousAt x.path.1 t := by
  classical
  dsimp only
  let ν : ProbabilityMeasure (J1WindowD T hT) :=
    Classical.choose (ldp_busemann_window_tendsto hind hsym hT)
  obtain ⟨_, S, hS, _, hfdd⟩ :=
    Classical.choose_spec (ldp_busemann_window_tendsto hind hsym hT)
  intro t htT
  by_cases htzero : (t : ℝ) = 0
  · have htEq : t = (⟨0, le_rfl, hT.le⟩ : J1Window T) := Subtype.ext htzero
    subst t
    exact DirectedDistances.Probability.zero_mem_continuityTimes
      (T := T) (hT := hT) (μ := (ν : Measure (J1WindowD T hT)))
  · have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm htzero)
    exact ldp_selected_window_continuity hT ν S hS hfdd t ht0 htT

/-- Helper toward Theorem 1.6 (thm-busemann-conv); conditional on hind/hsym;
The selected SDP window limit has almost surely continuous paths at each fixed
time strictly before the window endpoint. -/
theorem sdp_busemann_window_fixed_time_continuous
    (hind : iIndepFun (fun j ω => SDPMasterFromLaw.increment
      busemannSDPMeasurableVersion j ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map (SDPMasterFromLaw.increment
      busemannSDPMeasurableVersion 0) = iidCodeMeasure.map (fun ω =>
        -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω))
    {T : ℝ} (hT : 0 < T) :
    let ν := Classical.choose (sdp_busemann_window_tendsto hind hsym hT)
    ∀ t : J1Window T, (t : ℝ) < T →
      ∀ᵐ x ∂(ν : Measure (J1WindowD T hT)), ContinuousAt x.path.1 t := by
  classical
  dsimp only
  let ν : ProbabilityMeasure (J1WindowD T hT) :=
    Classical.choose (sdp_busemann_window_tendsto hind hsym hT)
  obtain ⟨_, S, hS, _, hfdd⟩ :=
    Classical.choose_spec (sdp_busemann_window_tendsto hind hsym hT)
  intro t htT
  by_cases htzero : (t : ℝ) = 0
  · have htEq : t = (⟨0, le_rfl, hT.le⟩ : J1Window T) := Subtype.ext htzero
    subst t
    exact DirectedDistances.Probability.zero_mem_continuityTimes
      (T := T) (hT := hT) (μ := (ν : Measure (J1WindowD T hT)))
  · have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm htzero)
    exact sdp_selected_window_continuity hT ν S hS hfdd t ht0 htT

end DirectedDistances.Recursive
