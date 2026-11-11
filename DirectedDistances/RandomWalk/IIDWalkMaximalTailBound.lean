module

public import DirectedDistances.RandomWalk.IIDWalkMaximal
public import DirectedDistances.RandomWalk.IIDWalkMaximalTail
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Moments.Basic

/-! # Maximal tail bound for iid walk blocks

This exponential maximum estimate supplies the within-block deviation input in
the block argument for `lem-walk-bdy-sum`
lines 182–190). -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open NormedSpace
open scoped BigOperators ENNReal NNReal
open scoped Nat

set_option backward.defeqAttrib.useBackward true in
private theorem complexHasSumCosPrime (z : ℂ) :
    HasSum (fun n : ℕ => (z * Complex.I) ^ (2 * n) / ↑(2 * n)!) (Complex.cos z) := by
  rw [Complex.cos, Complex.exp_eq_exp_ℂ]
  have h := ((expSeries_div_hasSum_exp (z * Complex.I)).add
    (expSeries_div_hasSum_exp (-z * Complex.I))).div_const 2
  have h := (Nat.divModEquiv 2).symm.hasSum_iff.mpr h
  dsimp [Function.comp_def] at h
  simp_rw [← mul_comm 2 _] at h
  refine h.prod_fiberwise fun k => ?_
  dsimp only
  convert hasSum_fintype (_ : Fin 2 → ℂ) using 1
  rw [Fin.sum_univ_two]
  simp_rw [Fin.val_zero, Fin.val_one, add_zero, pow_succ, pow_mul, mul_pow, neg_sq,
    ← two_mul, neg_mul, mul_neg, neg_div, add_neg_cancel, zero_div, add_zero,
    mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℂ) ≠ 0)]

private theorem complexHasSumCosh (z : ℂ) :
    HasSum (fun n : ℕ => z ^ (2 * n) / ↑(2 * n)!) (Complex.cosh z) := by
  simpa [mul_assoc, Complex.cos_mul_I] using complexHasSumCosPrime (z * Complex.I)

private theorem realHasSumCosh (x : ℝ) :
    HasSum (fun n : ℕ => x ^ (2 * n) / ↑(2 * n)!) (Real.cosh x) := by
  exact_mod_cast complexHasSumCosh (x : ℂ)

private theorem cosh_le_exp_half_sq (x : ℝ) :
    Real.cosh x ≤ Real.exp (x ^ 2 / 2) := by
  rw [← (realHasSumCosh x).tsum_eq, Real.exp_eq_exp_ℝ, exp_eq_tsum ℝ]
  refine (realHasSumCosh x).summable.tsum_le_tsum (fun i => ?_)
    (expSeries_summable' (x ^ 2 / 2))
  simp only [div_pow, pow_mul, smul_eq_mul, inv_mul_eq_div, div_div]
  gcongr
  norm_cast
  exact Nat.two_pow_mul_factorial_le_factorial_two_mul _

private theorem coordStepMGF_bounds (θ : ℝ) :
    1 ≤ (1 + 2 * Real.cosh θ) / 3 ∧
      (1 + 2 * Real.cosh θ) / 3 ≤ Real.exp (θ ^ 2 / 2) := by
  have hcosh := cosh_le_exp_half_sq θ
  have hexp : 1 ≤ Real.exp (θ ^ 2 / 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  constructor
  · nlinarith [Real.cosh_pos θ, Real.cosh_sq θ, sq_nonneg (Real.sinh θ)]
  · calc
      (1 + 2 * Real.cosh θ) / 3 ≤
          (Real.exp (θ ^ 2 / 2) + 2 * Real.exp (θ ^ 2 / 2)) / 3 := by
            nlinarith [hcosh, hexp]
      _ = Real.exp (θ ^ 2 / 2) := by ring

private theorem codeWalkCoordPartial_mgf_le (s m : ℕ) (j : Fin 2) (θ : ℝ) :
    ∫ ω, Real.exp (θ * codeWalkCoordPartial s j m ω) ∂iidCodeMeasure ≤
      Real.exp ((θ ^ 2 / 2) * (m : ℝ)) := by
  rw [codeWalkCoordPartial_mgf]
  have hq := (coordStepMGF_bounds θ).2
  have hq0 : 0 ≤ (1 + 2 * Real.cosh θ) / 3 := by
    linarith [(coordStepMGF_bounds θ).1]
  calc
    ((1 + 2 * Real.cosh θ) / 3) ^ m ≤
        (Real.exp (θ ^ 2 / 2)) ^ m := pow_le_pow_left₀ hq0 hq m
    _ = Real.exp ((m : ℝ) * (θ ^ 2 / 2)) := by rw [← Real.exp_nat_mul]
    _ = Real.exp ((θ ^ 2 / 2) * (m : ℝ)) := by rw [mul_comm]

private theorem codeWalkCoordIncrement_abs_le_one (s i : ℕ) (j : Fin 2)
    (ω : ℕ → Fin 3) : |codeWalkCoordIncrement s j i ω| ≤ 1 := by
  by_cases hj : j.val = 0
  · simp [codeWalkCoordIncrement, codeWalkCoordIncrementInt, hj,
      Nat.add_assoc]
    exact_mod_cast (codeWalk_succ_sub_coord_abs_le_one ω (s + i)).1
  · simp [codeWalkCoordIncrement, codeWalkCoordIncrementInt, hj,
      Nat.add_assoc]
    exact_mod_cast (codeWalk_succ_sub_coord_abs_le_one ω (s + i)).2

private def coordFiltration (s : ℕ) (j : Fin 2) :
    Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Fin 3)) where
  seq k := ⨆ i ∈ Set.Iio k,
    MeasurableSpace.comap (codeWalkCoordIncrement s j i) inferInstance
  mono' := by
    intro k l hkl
    refine iSup₂_le fun i hi => ?_
    exact le_iSup_of_le i <| le_iSup_of_le (lt_of_lt_of_le hi hkl) le_rfl
  le' := by
    intro k
    refine iSup₂_le fun i hi => ?_
    exact measurable_iff_comap_le.mp (measurable_codeWalkCoordIncrement s j i)

private noncomputable def coordExpProcess (s : ℕ) (j : Fin 2) (θ : ℝ) :
    ℕ → (ℕ → Fin 3) → ℝ :=
  fun k ω => Real.exp (θ * codeWalkCoordPartial s j k ω)

private theorem coordExpProcess_stronglyAdapted (s : ℕ) (j : Fin 2) (θ : ℝ) :
    StronglyAdapted (coordFiltration s j) (coordExpProcess s j θ) := by
  intro k
  have hsum : Measurable[coordFiltration s j k] (codeWalkCoordPartial s j k) := by
    change Measurable[coordFiltration s j k]
      (fun ω => ∑ i : Fin k, codeWalkCoordIncrement s j i.val ω)
    apply Finset.univ.measurable_sum
    intro i hi
    apply measurable_iff_comap_le.mpr
    exact le_iSup_of_le i.val <| le_iSup_of_le i.isLt le_rfl
  change StronglyMeasurable[coordFiltration s j k]
    (fun ω => Real.exp (θ * codeWalkCoordPartial s j k ω))
  exact (((measurable_const_mul θ).comp hsum).exp).stronglyMeasurable

private theorem coordExpProcess_integrable (s : ℕ) (j : Fin 2) (θ : ℝ) (k : ℕ) :
    Integrable (coordExpProcess s j θ k) iidCodeMeasure := by
  let X : Fin k → (ℕ → Fin 3) → ℝ := fun i ω => codeWalkCoordIncrement s j i.val ω
  have hX : iIndepFun X iidCodeMeasure :=
    (iIndepFun_codeWalkCoordIncrement s j).precomp Fin.val_injective
  have hmeas (i : Fin k) : Measurable (X i) :=
    measurable_codeWalkCoordIncrement s j i.val
  have hint (i : Fin k) :
      Integrable (fun ω => Real.exp (θ * X i ω)) iidCodeMeasure := by
    apply ProbabilityTheory.integrable_exp_mul_of_mem_Icc (hmeas i).aemeasurable
    filter_upwards [] with ω
    exact abs_le.mp (codeWalkCoordIncrement_abs_le_one s i.val j ω)
  have h := hX.integrable_exp_mul_sum hmeas (s := Finset.univ)
    (fun i hi => hint i)
  change Integrable
    (fun ω => Real.exp (θ * codeWalkCoordPartial s j k ω)) iidCodeMeasure
  simpa [codeWalkCoordPartial, X] using h

private theorem coordPartial_succ (s k : ℕ) (j : Fin 2) (ω : ℕ → Fin 3) :
    codeWalkCoordPartial s j (k + 1) ω =
      codeWalkCoordPartial s j k ω + codeWalkCoordIncrement s j k ω := by
  simp [codeWalkCoordPartial, Fin.sum_univ_castSucc]

private theorem coordExpProcess_submartingale (s : ℕ) (j : Fin 2) (θ : ℝ) :
    Submartingale (coordExpProcess s j θ) (coordFiltration s j) iidCodeMeasure := by
  apply submartingale_of_setIntegral_le_succ
  · exact coordExpProcess_stronglyAdapted s j θ
  · intro k
    exact coordExpProcess_integrable s j θ k
  · intro k A hA
    let X : (ℕ → Fin 3) → ℝ := codeWalkCoordIncrement s j k
    let G : (ℕ → Fin 3) → ℝ := fun ω => Real.exp (θ * X ω)
    let H : (ℕ → Fin 3) → ℝ := fun ω => A.indicator (coordExpProcess s j θ k) ω
    have hspaces : iIndep
        (fun i : ℕ => MeasurableSpace.comap (codeWalkCoordIncrement s j i) inferInstance)
        iidCodeMeasure :=
      (iIndepFun_iff_iIndep _ _ _).mp (iIndepFun_codeWalkCoordIncrement s j)
    have hle : ∀ i, MeasurableSpace.comap (codeWalkCoordIncrement s j i) inferInstance ≤
        (inferInstance : MeasurableSpace (ℕ → Fin 3)) := by
      intro i
      exact measurable_iff_comap_le.mp (measurable_codeWalkCoordIncrement s j i)
    have hst : Disjoint (Set.Iio k) ({k} : Set ℕ) := by simp
    have hspace : Indep (coordFiltration s j k)
        (MeasurableSpace.comap X inferInstance) iidCodeMeasure := by
      change Indep (⨆ i ∈ Set.Iio k,
        MeasurableSpace.comap (codeWalkCoordIncrement s j i) inferInstance)
        (MeasurableSpace.comap X inferInstance) iidCodeMeasure
      have h : Indep
          (⨆ i ∈ Set.Iio k,
            MeasurableSpace.comap (codeWalkCoordIncrement s j i) inferInstance)
          (⨆ i ∈ ({k} : Set ℕ),
            MeasurableSpace.comap (codeWalkCoordIncrement s j i) inferInstance)
          iidCodeMeasure := indep_iSup_of_disjoint hle hspaces hst
      simpa only [iSup_singleton] using h
    have hmeasG : Measurable[MeasurableSpace.comap X inferInstance] G := by
      change Measurable[MeasurableSpace.comap X inferInstance]
        (fun ω => Real.exp (θ * X ω))
      exact ((measurable_const_mul θ).comp (Measurable.of_comap_le le_rfl)).exp
    have hmeasH : Measurable[coordFiltration s j k] H := by
      exact (coordExpProcess_stronglyAdapted s j θ k).measurable.indicator hA
    have hindHG : H ⟂ᵢ[iidCodeMeasure] G := by
      change Indep (MeasurableSpace.comap H inferInstance)
        (MeasurableSpace.comap G inferInstance) iidCodeMeasure
      exact indep_of_indep_of_le hspace
        (measurable_iff_comap_le.mp hmeasH) (measurable_iff_comap_le.mp hmeasG)
    have hGint : Integrable G iidCodeMeasure := by
      apply ProbabilityTheory.integrable_exp_mul_of_mem_Icc
        (measurable_codeWalkCoordIncrement s j k).aemeasurable
      filter_upwards [] with ω
      exact abs_le.mp (codeWalkCoordIncrement_abs_le_one s k j ω)
    have hA' : MeasurableSet A := (coordFiltration s j).le k A hA
    have hHint : Integrable H iidCodeMeasure :=
      (coordExpProcess_integrable s j θ k).indicator hA'
    have hfact := hindHG.integral_mul_eq_mul_integral
      hHint.aestronglyMeasurable hGint.aestronglyMeasurable
    have hqeq : ∫ ω, G ω ∂iidCodeMeasure = (1 + 2 * Real.cosh θ) / 3 := by
      have h := codeWalkCoordPartial_mgf (s + k) 1 j θ
      have hpt : codeWalkCoordPartial (s + k) j 1 = X := by
        funext ω
        simp [X, codeWalkCoordPartial, codeWalkCoordIncrement,
          codeWalkCoordIncrementInt, Nat.add_assoc]
      rw [hpt] at h
      simpa [G] using h
    have hq : 1 ≤ ∫ ω, G ω ∂iidCodeMeasure := by
      rw [hqeq]
      exact (coordStepMGF_bounds θ).1
    have hpoint :
        (A.indicator (coordExpProcess s j θ (k + 1))) = H * G := by
      funext ω
      by_cases hω : ω ∈ A
      · simp [H, G, X, hω, coordExpProcess, coordPartial_succ, mul_add, Real.exp_add]
      · simp [H, hω]
    calc
      ∫ ω in A, coordExpProcess s j θ (k + 1) ω ∂iidCodeMeasure =
          ∫ ω, H ω * G ω ∂iidCodeMeasure := by
            calc
              ∫ ω in A, coordExpProcess s j θ (k + 1) ω ∂iidCodeMeasure =
                  ∫ ω, A.indicator (coordExpProcess s j θ (k + 1)) ω ∂iidCodeMeasure :=
                    (integral_indicator hA').symm
              _ = ∫ ω, H ω * G ω ∂iidCodeMeasure := by
                    exact congrArg (fun f : (ℕ → Fin 3) → ℝ =>
                      ∫ ω, f ω ∂iidCodeMeasure) hpoint
      _ = (∫ ω, H ω ∂iidCodeMeasure) * (∫ ω, G ω ∂iidCodeMeasure) := hfact
      _ = (∫ ω in A, coordExpProcess s j θ k ω ∂iidCodeMeasure) *
          (∫ ω, G ω ∂iidCodeMeasure) := by
            change (∫ ω, A.indicator (coordExpProcess s j θ k) ω ∂iidCodeMeasure) * _ = _
            rw [integral_indicator hA']
      _ ≥ ∫ ω in A, coordExpProcess s j θ k ω ∂iidCodeMeasure := by
            exact le_mul_of_one_le_right
              (integral_nonneg (fun ω => (Real.exp_pos _).le)) hq

private theorem coordPositiveMaxTail (s m : ℕ) (hm : 0 < m) (j : Fin 2)
    (a : ℝ) (ha : 0 < a) :
    iidCodeMeasure.real {ω | ∃ k ≤ m, a ≤ codeWalkCoordPartial s j k ω} ≤
      Real.exp (-(a ^ 2) / (2 * (m : ℝ))) := by
  let θ : ℝ := a / (m : ℝ)
  let ε : ℝ≥0 := ⟨Real.exp (θ * a), (Real.exp_pos _).le⟩
  let E : Set (ℕ → Fin 3) :=
    {ω | ∃ k ≤ m, a ≤ codeWalkCoordPartial s j k ω}
  have hε : (ε : ℝ) = Real.exp (θ * a) := rfl
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hθ : 0 < θ := by dsimp [θ]; exact div_pos ha hmR
  have hrange : (Finset.range (m + 1)).Nonempty := ⟨0, by simp⟩
  have hevent :
      {ω | (ε : ℝ) ≤ (Finset.range (m + 1)).sup' hrange
        (fun k => coordExpProcess s j θ k ω)} = E := by
    ext ω
    constructor
    · intro h
      obtain ⟨k, hk, hkexp⟩ :=
        (Finset.le_sup'_iff (s := Finset.range (m + 1)) (H := hrange)
          (f := fun k => coordExpProcess s j θ k ω) (a := (ε : ℝ))).mp h
      refine ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), ?_⟩
      have hExp : Real.exp (θ * a) ≤ Real.exp
          (θ * codeWalkCoordPartial s j k ω) := by
        simpa only [coordExpProcess, show (ε : ℝ) = Real.exp (θ * a) from rfl] using hkexp
      have hExp' := Real.exp_le_exp.mp hExp
      exact (mul_le_mul_iff_right₀ hθ).mp hExp'
    · rintro ⟨k, hk, hkS⟩
      apply (Finset.le_sup'_iff (s := Finset.range (m + 1)) (H := hrange)
        (f := fun k => coordExpProcess s j θ k ω) (a := (ε : ℝ))).mpr
      refine ⟨k, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk), ?_⟩
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul_iff_right₀ hθ).mpr hkS
  have hmax := MeasureTheory.maximal_ineq (ε := ε)
    (coordExpProcess_submartingale s j θ)
    (fun k ω => (Real.exp_pos _).le) m
  rw [hevent] at hmax
  have hset : ∫ ω in E, coordExpProcess s j θ m ω ∂iidCodeMeasure ≤
      ∫ ω, coordExpProcess s j θ m ω ∂iidCodeMeasure :=
    setIntegral_le_integral (coordExpProcess_integrable s j θ m)
      (ae_of_all _ fun ω => (Real.exp_pos _).le)
  have hmgf := codeWalkCoordPartial_mgf_le s m j θ
  have hB : 0 ≤ Real.exp ((θ ^ 2 / 2) * (m : ℝ)) := (Real.exp_pos _).le
  have hIntBound :
      ∫ ω in E, coordExpProcess s j θ m ω ∂iidCodeMeasure ≤
        Real.exp ((θ ^ 2 / 2) * (m : ℝ)) := by
    exact hset.trans (by simpa [coordExpProcess] using hmgf)
  have hwrap : ENNReal.ofReal ((ε : ℝ) * iidCodeMeasure.real E) ≤
      ENNReal.ofReal (Real.exp ((θ ^ 2 / 2) * (m : ℝ))) := by
    calc
      ENNReal.ofReal ((ε : ℝ) * iidCodeMeasure.real E) =
          (ε : ℝ≥0∞) * iidCodeMeasure E := by
            rw [ENNReal.ofReal_mul (show 0 ≤ (ε : ℝ) by positivity),
              ENNReal.ofReal_coe_nnreal,
              MeasureTheory.ofReal_measureReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal (∫ ω in E,
            coordExpProcess s j θ m ω ∂iidCodeMeasure) := hmax
      _ ≤ ENNReal.ofReal (Real.exp ((θ ^ 2 / 2) * (m : ℝ))) :=
            ENNReal.ofReal_le_ofReal hIntBound
  have hprob : (ε : ℝ) * iidCodeMeasure.real E ≤
      Real.exp ((θ ^ 2 / 2) * (m : ℝ)) :=
    (ENNReal.ofReal_le_ofReal_iff hB).mp hwrap
  have hprob' : Real.exp (θ * a) * iidCodeMeasure.real E ≤
      Real.exp ((θ ^ 2 / 2) * (m : ℝ)) := by
    simpa only [hε] using hprob
  have hdivide : iidCodeMeasure.real E ≤
      Real.exp ((θ ^ 2 / 2) * (m : ℝ)) / (ε : ℝ) := by
    apply (le_div_iff₀ (Real.exp_pos _)).2
    simpa [mul_comm, hε] using hprob'
  calc
    iidCodeMeasure.real E ≤
        Real.exp ((θ ^ 2 / 2) * (m : ℝ)) / Real.exp (θ * a) := by
          simpa only [hε] using hdivide
    _ = Real.exp (-(a ^ 2) / (2 * (m : ℝ))) := by
          rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
          congr 1
          dsimp [θ]
          field_simp
          ; ring


private theorem coordNegativeMaxTail (s m : ℕ) (hm : 0 < m) (j : Fin 2)
    (a : ℝ) (ha : 0 < a) :
    iidCodeMeasure.real {ω | ∃ k ≤ m, a ≤ -codeWalkCoordPartial s j k ω} ≤
      Real.exp (-(a ^ 2) / (2 * (m : ℝ))) := by
  let θ : ℝ := a / (m : ℝ)
  let ε : ℝ≥0 := ⟨Real.exp (θ * a), (Real.exp_pos _).le⟩
  let E : Set (ℕ → Fin 3) :=
    {ω | ∃ k ≤ m, a ≤ -codeWalkCoordPartial s j k ω}
  have hε : (ε : ℝ) = Real.exp (θ * a) := rfl
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hθ : 0 < θ := by dsimp [θ]; exact div_pos ha hmR
  have hrange : (Finset.range (m + 1)).Nonempty := ⟨0, by simp⟩
  have hevent :
      {ω | (ε : ℝ) ≤ (Finset.range (m + 1)).sup' hrange
        (fun k => coordExpProcess s j (-θ) k ω)} = E := by
    ext ω
    constructor
    · intro h
      obtain ⟨k, hk, hkexp⟩ :=
        (Finset.le_sup'_iff (s := Finset.range (m + 1)) (H := hrange)
          (f := fun k => coordExpProcess s j (-θ) k ω) (a := (ε : ℝ))).mp h
      refine ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), ?_⟩
      have hExp : Real.exp (θ * a) ≤ Real.exp
          ((-θ) * codeWalkCoordPartial s j k ω) := by
        simpa only [coordExpProcess, show (ε : ℝ) = Real.exp (θ * a) from rfl] using hkexp
      have hExp' := Real.exp_le_exp.mp hExp
      have hmul : θ * a ≤ θ * (-codeWalkCoordPartial s j k ω) := by
        nlinarith [hExp']
      exact (mul_le_mul_iff_right₀ hθ).mp hmul
    · rintro ⟨k, hk, hkS⟩
      apply (Finset.le_sup'_iff (s := Finset.range (m + 1)) (H := hrange)
        (f := fun k => coordExpProcess s j (-θ) k ω) (a := (ε : ℝ))).mpr
      refine ⟨k, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk), ?_⟩
      apply Real.exp_le_exp.mpr
      have hmul : θ * a ≤ θ * (-codeWalkCoordPartial s j k ω) :=
        (mul_le_mul_iff_right₀ hθ).mpr hkS
      nlinarith [hmul]
  have hmax := MeasureTheory.maximal_ineq (ε := ε)
    (coordExpProcess_submartingale s j (-θ))
    (fun k ω => (Real.exp_pos _).le) m
  rw [hevent] at hmax
  have hset : ∫ ω in E, coordExpProcess s j (-θ) m ω ∂iidCodeMeasure ≤
      ∫ ω, coordExpProcess s j (-θ) m ω ∂iidCodeMeasure :=
    setIntegral_le_integral (coordExpProcess_integrable s j (-θ) m)
      (ae_of_all _ fun ω => (Real.exp_pos _).le)
  have hmgf := codeWalkCoordPartial_mgf_le s m j (-θ)
  have hsq : (-θ) ^ 2 = θ ^ 2 := by ring
  rw [hsq] at hmgf
  have hB : 0 ≤ Real.exp ((θ ^ 2 / 2) * (m : ℝ)) := (Real.exp_pos _).le
  have hIntBound :
      ∫ ω in E, coordExpProcess s j (-θ) m ω ∂iidCodeMeasure ≤
        Real.exp ((θ ^ 2 / 2) * (m : ℝ)) := by
    exact hset.trans (by simpa [coordExpProcess] using hmgf)
  have hwrap : ENNReal.ofReal ((ε : ℝ) * iidCodeMeasure.real E) ≤
      ENNReal.ofReal (Real.exp ((θ ^ 2 / 2) * (m : ℝ))) := by
    calc
      ENNReal.ofReal ((ε : ℝ) * iidCodeMeasure.real E) =
          (ε : ℝ≥0∞) * iidCodeMeasure E := by
            rw [ENNReal.ofReal_mul (show 0 ≤ (ε : ℝ) by positivity),
              ENNReal.ofReal_coe_nnreal,
              MeasureTheory.ofReal_measureReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal (∫ ω in E,
            coordExpProcess s j (-θ) m ω ∂iidCodeMeasure) := hmax
      _ ≤ ENNReal.ofReal (Real.exp ((θ ^ 2 / 2) * (m : ℝ))) :=
            ENNReal.ofReal_le_ofReal hIntBound
  have hprob : (ε : ℝ) * iidCodeMeasure.real E ≤
      Real.exp ((θ ^ 2 / 2) * (m : ℝ)) :=
    (ENNReal.ofReal_le_ofReal_iff hB).mp hwrap
  have hprob' : Real.exp (θ * a) * iidCodeMeasure.real E ≤
      Real.exp ((θ ^ 2 / 2) * (m : ℝ)) := by
    simpa only [hε] using hprob
  have hdivide : iidCodeMeasure.real E ≤
      Real.exp ((θ ^ 2 / 2) * (m : ℝ)) / (ε : ℝ) := by
    apply (le_div_iff₀ (Real.exp_pos _)).2
    simpa [mul_comm, hε] using hprob'
  calc
    iidCodeMeasure.real E ≤
        Real.exp ((θ ^ 2 / 2) * (m : ℝ)) / Real.exp (θ * a) := by
          simpa only [hε] using hdivide
    _ = Real.exp (-(a ^ 2) / (2 * (m : ℝ))) := by
          rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
          congr 1
          dsimp [θ]
          field_simp
          ring


/-- The scalar coordinate block sum is the corresponding coordinate displacement
of the source walk (`lem-walk-bdy-sum`, -/
theorem codeWalkCoordPartial_eq_codeWalk_sub (s k : ℕ) (j : Fin 2)
    (ω : ℕ → Fin 3) :
    codeWalkCoordPartial s j k ω =
      if j.val = 0 then
        (((codeWalk ω (s + k) - codeWalk ω s).1 : ℤ) : ℝ)
      else (((codeWalk ω (s + k) - codeWalk ω s).2 : ℤ) : ℝ) := by
  induction k with
  | zero => simp [codeWalkCoordPartial]
  | succ k ih =>
      have hstep : codeWalk ω (s + (k + 1)) - codeWalk ω (s + k) =
          lazyTwoDimensionalStep (ω (s + (k + 1))) := by
        simpa [Nat.add_assoc] using codeWalk_succ_sub ω (s + k)
      have htotal : codeWalk ω (s + (k + 1)) - codeWalk ω s =
          lazyTwoDimensionalStep (ω (s + (k + 1))) +
            (codeWalk ω (s + k) - codeWalk ω s) := by
        rw [← hstep]
        abel
      rw [coordPartial_succ, ih]
      by_cases hj : j.val = 0
      · simp [hj, codeWalkCoordIncrement, codeWalkCoordIncrementInt,
          hstep, htotal, Prod.fst_sub, Int.cast_sub, Nat.add_assoc]
        abel
      · simp [hj, codeWalkCoordIncrement, codeWalkCoordIncrementInt,
          hstep, htotal, Prod.snd_sub, Int.cast_sub, Nat.add_assoc]
        abel


/-- The maximum absolute coordinate displacement in an iid code-walk block has
a Gaussian tail, by the four signed coordinate estimates -/
theorem iidCodeWalk_blockMax_tail (s m : ℕ) (hm : 0 < m) (a : ℝ) (ha : 0 < a) :
    iidCodeMeasure.real {ω | ∃ k ≤ m,
      (a ≤ |(((codeWalk ω (s + k) - codeWalk ω s).1 : ℤ) : ℝ)| ∨
       a ≤ |(((codeWalk ω (s + k) - codeWalk ω s).2 : ℤ) : ℝ)|)} ≤
      4 * Real.exp (-(a ^ 2) / (2 * (m : ℝ))) := by
  let E0p : Set (ℕ → Fin 3) :=
    {ω | ∃ k ≤ m, a ≤ codeWalkCoordPartial s 0 k ω}
  let E0n : Set (ℕ → Fin 3) :=
    {ω | ∃ k ≤ m, a ≤ -codeWalkCoordPartial s 0 k ω}
  let E1p : Set (ℕ → Fin 3) :=
    {ω | ∃ k ≤ m, a ≤ codeWalkCoordPartial s 1 k ω}
  let E1n : Set (ℕ → Fin 3) :=
    {ω | ∃ k ≤ m, a ≤ -codeWalkCoordPartial s 1 k ω}
  have habs (x : ℝ) (hx : a ≤ |x|) : a ≤ x ∨ a ≤ -x := by
    rcases le_total 0 x with h | h
    · left
      simpa [abs_of_nonneg h] using hx
    · right
      simpa [abs_of_nonpos h] using hx
  have hsub :
      {ω | ∃ k ≤ m,
        (a ≤ |(((codeWalk ω (s + k) - codeWalk ω s).1 : ℤ) : ℝ)| ∨
         a ≤ |(((codeWalk ω (s + k) - codeWalk ω s).2 : ℤ) : ℝ)|)} ⊆
        E0p ∪ (E0n ∪ (E1p ∪ E1n)) := by
    intro ω hω
    obtain ⟨k, hk, hxy⟩ := hω
    rcases hxy with hx | hy
    · have htel : codeWalkCoordPartial s 0 k ω =
          (((codeWalk ω (s + k) - codeWalk ω s).1 : ℤ) : ℝ) := by
        simpa using codeWalkCoordPartial_eq_codeWalk_sub s k (0 : Fin 2) ω
      have hx' : a ≤ |codeWalkCoordPartial s 0 k ω| := by
        simpa only [htel] using hx
      rcases habs _ hx' with hxpos | hxneg
      · exact Or.inl ⟨k, hk, hxpos⟩
      · exact Or.inr (Or.inl ⟨k, hk, hxneg⟩)
    · have htel : codeWalkCoordPartial s 1 k ω =
          (((codeWalk ω (s + k) - codeWalk ω s).2 : ℤ) : ℝ) := by
        simpa using codeWalkCoordPartial_eq_codeWalk_sub s k (1 : Fin 2) ω
      have hy' : a ≤ |codeWalkCoordPartial s 1 k ω| := by
        simpa only [htel] using hy
      rcases habs _ hy' with hypos | hyneg
      · exact Or.inr (Or.inr (Or.inl ⟨k, hk, hypos⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨k, hk, hyneg⟩))
  have h0p := coordPositiveMaxTail s m hm 0 a ha
  have h0n := coordNegativeMaxTail s m hm 0 a ha
  have h1p := coordPositiveMaxTail s m hm 1 a ha
  have h1n := coordNegativeMaxTail s m hm 1 a ha
  let q : ℝ := Real.exp (-(a ^ 2) / (2 * (m : ℝ)))
  change iidCodeMeasure.real E0p ≤ q at h0p
  change iidCodeMeasure.real E0n ≤ q at h0n
  change iidCodeMeasure.real E1p ≤ q at h1p
  change iidCodeMeasure.real E1n ≤ q at h1n
  calc
    iidCodeMeasure.real {ω | ∃ k ≤ m,
        (a ≤ |(((codeWalk ω (s + k) - codeWalk ω s).1 : ℤ) : ℝ)| ∨
         a ≤ |(((codeWalk ω (s + k) - codeWalk ω s).2 : ℤ) : ℝ)|)} ≤
        iidCodeMeasure.real (E0p ∪ (E0n ∪ (E1p ∪ E1n))) := measureReal_mono hsub
    _ ≤ iidCodeMeasure.real E0p + iidCodeMeasure.real (E0n ∪ (E1p ∪ E1n)) :=
        measureReal_union_le E0p (E0n ∪ (E1p ∪ E1n))
    _ ≤ iidCodeMeasure.real E0p +
          (iidCodeMeasure.real E0n + iidCodeMeasure.real (E1p ∪ E1n)) :=
        add_le_add_right (measureReal_union_le E0n (E1p ∪ E1n)) _
    _ ≤ iidCodeMeasure.real E0p +
          (iidCodeMeasure.real E0n +
            (iidCodeMeasure.real E1p + iidCodeMeasure.real E1n)) := by
        have hcd := measureReal_union_le (μ := iidCodeMeasure) E1p E1n
        have hbcd := add_le_add_right hcd (iidCodeMeasure.real E0n)
        exact add_le_add_right hbcd (iidCodeMeasure.real E0p)
    _ ≤ 4 * Real.exp (-(a ^ 2) / (2 * (m : ℝ))) := by
        calc
          iidCodeMeasure.real E0p +
              (iidCodeMeasure.real E0n +
                (iidCodeMeasure.real E1p + iidCodeMeasure.real E1n)) ≤
              q + (q + (q + q)) :=
            add_le_add h0p (add_le_add h0n (add_le_add h1p h1n))
          _ = 4 * q := by ring
          _ = 4 * Real.exp (-(a ^ 2) / (2 * (m : ℝ))) := by rfl

example : ∀ (s m : ℕ), 0 < m → ∀ (a : ℝ), 0 < a →
    iidCodeMeasure.real {ω | ∃ k, k ≤ m ∧
      (a ≤ |((codeWalk ω (s + k) - codeWalk ω s).1 : ℝ)| ∨
       a ≤ |((codeWalk ω (s + k) - codeWalk ω s).2 : ℝ)|)} ≤
      4 * Real.exp (-(a ^ 2) / (2 * (m : ℝ))) :=
  fun s m hm a ha => iidCodeWalk_blockMax_tail s m hm a ha

end DirectedDistances.RandomWalk
