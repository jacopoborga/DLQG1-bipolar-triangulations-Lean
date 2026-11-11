module

public import DirectedDistances.RandomWalk.IIDWalkMaximal
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Probability.Independence.Integration

/-! # Exponential bounds for the iid vector walk

The block maximum estimate supplies the within-block deviation control in the
block argument for `lem-walk-bdy-sum`, in particular the tube event `E_N` -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open NormedSpace
open scoped BigOperators
open scoped Nat
open scoped ENNReal

/-- The integer-valued increment of one selected coordinate of the source walk.
It is the scalar input for the within-block deviation estimate in the
especially the event `E_N` at lines 182–190). -/
@[expose] def codeWalkCoordIncrementInt (s : ℕ) (j : Fin 2) (i : ℕ)
    (ω : ℕ → Fin 3) : ℤ :=
  if j.val = 0 then
    (codeWalk ω (s + i + 1) - codeWalk ω (s + i)).1
  else (codeWalk ω (s + i + 1) - codeWalk ω (s + i)).2

/-- The real-valued increment of one selected coordinate of the source walk.
It is the scalar input for the within-block deviation estimate in the
especially the event `E_N` at lines 182–190). -/
@[expose] def codeWalkCoordIncrement (s : ℕ) (j : Fin 2) (i : ℕ)
    (ω : ℕ → Fin 3) : ℝ := (codeWalkCoordIncrementInt s j i ω : ℝ)

/-- Coordinate increments in a block retain independence, the input needed
for the stopping-time split in the `lem-walk-bdy-sum` block bound -/
theorem iIndepFun_codeWalkCoordIncrement (s : ℕ) (j : Fin 2) :
    iIndepFun (fun i ω => codeWalkCoordIncrement s j i ω) iidCodeMeasure := by
  have hinj : Function.Injective (fun i : ℕ => s + i) := by
    intro i k hik
    exact Nat.add_left_cancel hik
  have h := iIndepFun_codeWalk_increments.precomp hinj
  have h' := h.comp (fun (_ : ℕ) (z : ℤ × ℤ) =>
      (((if j.val = 0 then z.1 else z.2 : ℤ) : ℝ)))
    (fun _ => measurable_of_countable _)
  convert h' using 1
  ext i ω
  simp [codeWalkCoordIncrement, codeWalkCoordIncrementInt, Int.cast_sub,
    Prod.fst_sub, Prod.snd_sub, Nat.add_assoc]

/-- Measurability of the coordinate block increments used in the
`lem-walk-bdy-sum` block deviation estimate -/
theorem measurable_codeWalkCoordIncrement (s : ℕ) (j : Fin 2) (i : ℕ) :
    Measurable (codeWalkCoordIncrement s j i) := by
  have hvec : Measurable (fun ω =>
      codeWalk ω (s + i + 1) - codeWalk ω (s + i)) :=
    (measurable_codeWalk.eval (a := s + i + 1)).sub
      (measurable_codeWalk.eval (a := s + i))
  have hcoord : Measurable (codeWalkCoordIncrementInt s j i) := by
    change Measurable (fun ω => if j.val = 0 then
      (codeWalk ω (s + i + 1) - codeWalk ω (s + i)).1
      else (codeWalk ω (s + i + 1) - codeWalk ω (s + i)).2)
    by_cases hj : j.val = 0
    · simpa [hj, Function.comp_def] using measurable_fst.comp hvec
    · simpa [hj, Function.comp_def] using measurable_snd.comp hvec
  change Measurable (fun ω => (codeWalkCoordIncrementInt s j i ω : ℝ))
  exact (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp hcoord

private def coordinateInt (j : Fin 2) (z : ℤ × ℤ) : ℤ :=
  if j.val = 0 then z.1 else z.2

private theorem map_uniform_vectorSteps_snd :
    (Measure.uniformOfFinset
      ({(1, -1), (-1, 0), (0, 1)} : Finset (ℤ × ℤ))).map Prod.snd =
      Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ) := by
  have hmap (c : ℝ≥0∞) (z : ℤ × ℤ) :
      (c • Measure.dirac z).map Prod.snd = c • Measure.dirac z.2 := by
    rw [Measure.map_smul c measurable_snd.aemeasurable, Measure.map_dirac]
  simp only [Measure.uniformOfFinset]
  norm_num [Measure.map_add, measurable_snd, hmap]

private theorem map_uniform_vectorSteps_fst_local :
    (Measure.uniformOfFinset
      ({(1, -1), (-1, 0), (0, 1)} : Finset (ℤ × ℤ))).map Prod.fst =
      Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ) := by
  have hmap (c : ℝ≥0∞) (z : ℤ × ℤ) :
      (c • Measure.dirac z).map Prod.fst = c • Measure.dirac z.1 := by
    rw [Measure.map_smul c measurable_fst.aemeasurable, Measure.map_dirac]
  simp only [Measure.uniformOfFinset]
  norm_num [Measure.map_add, measurable_fst, hmap]
  ac_rfl

/-- The scalar marginal is uniform on `{-1,0,1}`, as required for the
within-block estimate in the `lem-walk-bdy-sum` block bound -/
theorem map_codeWalkCoordIncrementInt (s i : ℕ) (j : Fin 2) :
    iidCodeMeasure.map (codeWalkCoordIncrementInt s j i) =
      Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ) := by
  have hvec := map_codeWalk_increment (s + i)
  have hf : Measurable (fun ω =>
      codeWalk ω ((s + i) + 1) - codeWalk ω (s + i)) := by
    rw [show (fun ω => codeWalk ω ((s + i) + 1) - codeWalk ω (s + i)) =
        fun ω => lazyTwoDimensionalStep (ω ((s + i) + 1)) by
          funext ω; exact codeWalk_succ_sub ω (s + i)]
    exact (measurable_of_countable lazyTwoDimensionalStep).comp
      (measurable_pi_apply ((s + i) + 1))
  have hproj :
      iidCodeMeasure.map (fun ω => if j.val = 0 then
        (codeWalk ω ((s + i) + 1) - codeWalk ω (s + i)).1
      else (codeWalk ω ((s + i) + 1) - codeWalk ω (s + i)).2) =
      Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ) := by
    rcases j with ⟨j, hj⟩
    interval_cases j
    · change iidCodeMeasure.map (fun ω =>
        (codeWalk ω ((s + i) + 1) - codeWalk ω (s + i)).1) = _
      rw [show (fun ω => (codeWalk ω ((s + i) + 1) - codeWalk ω (s + i)).1) =
          Prod.fst ∘ (fun ω => codeWalk ω ((s + i) + 1) - codeWalk ω (s + i)) by
            funext ω; rfl,
        ← Measure.map_map measurable_fst hf, hvec, map_uniform_vectorSteps_fst_local]
    · change iidCodeMeasure.map (fun ω =>
        (codeWalk ω ((s + i) + 1) - codeWalk ω (s + i)).2) = _
      rw [show (fun ω => (codeWalk ω ((s + i) + 1) - codeWalk ω (s + i)).2) =
          Prod.snd ∘ (fun ω => codeWalk ω ((s + i) + 1) - codeWalk ω (s + i)) by
            funext ω; rfl,
        ← Measure.map_map measurable_snd hf, hvec, map_uniform_vectorSteps_snd]
  change iidCodeMeasure.map (codeWalkCoordIncrementInt s j i) = _
  exact hproj

private theorem codeWalkCoordIncrement_mgf (s i : ℕ) (j : Fin 2) (θ : ℝ) :
    ∫ ω, Real.exp (θ * codeWalkCoordIncrement s j i ω) ∂iidCodeMeasure =
      (Real.exp (-θ) + 1 + Real.exp θ) / 3 := by
  have hvecmeas : Measurable (fun ω =>
      codeWalk ω (s + i + 1) - codeWalk ω (s + i)) :=
    (measurable_codeWalk.eval (a := s + i + 1)).sub
      (measurable_codeWalk.eval (a := s + i))
  have hmeas : Measurable (codeWalkCoordIncrementInt s j i) := by
    change Measurable (fun ω => if j.val = 0 then
      (codeWalk ω (s + i + 1) - codeWalk ω (s + i)).1
      else (codeWalk ω (s + i + 1) - codeWalk ω (s + i)).2)
    by_cases hj : j.val = 0
    · simpa [hj, Function.comp_def] using measurable_fst.comp hvecmeas
    · simpa [hj, Function.comp_def] using measurable_snd.comp hvecmeas
  have hunif :
      ∫ z : ℤ, Real.exp (θ * (z : ℝ)) ∂
        Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ) =
        (Real.exp (-θ) + 1 + Real.exp θ) / 3 := by
    rw [Measure.uniformOfFinset, integral_finsetSum_measure]
    · simp [integral_smul_measure, integral_dirac]
      ring
    · intro z hz
      exact (integrable_dirac (f := fun z : ℤ => Real.exp (θ * (z : ℝ))) (by simp)).smul_measure
        (by simp)
  have hsm : AEStronglyMeasurable (fun z : ℤ => Real.exp (θ * (z : ℝ)))
      (iidCodeMeasure.map (codeWalkCoordIncrementInt s j i)) := by
    fun_prop
  calc
    ∫ ω, Real.exp (θ * codeWalkCoordIncrement s j i ω) ∂iidCodeMeasure =
        ∫ ω, Real.exp (θ * ((codeWalkCoordIncrementInt s j i ω : ℤ) : ℝ))
          ∂iidCodeMeasure := rfl
    _ = ∫ z, Real.exp (θ * (z : ℝ)) ∂
          (iidCodeMeasure.map (codeWalkCoordIncrementInt s j i)) :=
        (integral_map hmeas.aemeasurable hsm).symm
    _ = ∫ z : ℤ, Real.exp (θ * (z : ℝ)) ∂
          Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ) := by
        rw [map_codeWalkCoordIncrementInt]
    _ = (Real.exp (-θ) + 1 + Real.exp θ) / 3 := hunif

/-- The `k`th partial sum of a coordinate block, used for the stopped
exponential moment in the `lem-walk-bdy-sum` block bound -/
@[expose] def codeWalkCoordPartial (s : ℕ) (j : Fin 2) (k : ℕ)
    (ω : ℕ → Fin 3) : ℝ :=
  ∑ i : Fin k, codeWalkCoordIncrement s j i.val ω

/-- The exponential moment of a length `m` coordinate block is the `m`th
power of the one-step moment. This supplies the endpoint moment in the
within-block deviation estimate for `lem-walk-bdy-sum` -/
theorem codeWalkCoordPartial_mgf (s m : ℕ) (j : Fin 2) (θ : ℝ) :
    ∫ ω, Real.exp (θ * codeWalkCoordPartial s j m ω) ∂iidCodeMeasure =
      ((1 + 2 * Real.cosh θ) / 3) ^ m := by
  let X : Fin m → (ℕ → Fin 3) → ℝ := fun i ω =>
    codeWalkCoordIncrement s j i.val ω
  have hX : iIndepFun X iidCodeMeasure := by
    exact (iIndepFun_codeWalkCoordIncrement s j).precomp Fin.val_injective
  have hf (i : Fin m) : AEMeasurable (X i) iidCodeMeasure := by
    dsimp [X]
    exact (measurable_codeWalkCoordIncrement s j i.val).aemeasurable
  have hg (i : Fin m) : AEStronglyMeasurable
      (fun x : ℝ => Real.exp (θ * x)) (iidCodeMeasure.map (X i)) := by
    fun_prop
  have hfac := hX.integral_fun_prod_comp hf hg
  have hpoint (ω : ℕ → Fin 3) :
      (∏ i : Fin m, Real.exp (θ * X i ω)) =
        Real.exp (θ * codeWalkCoordPartial s j m ω) := by
    rw [← Real.exp_sum]
    congr 1
    simp [Finset.mul_sum, codeWalkCoordPartial, X]
  have hstep (i : Fin m) :
      ∫ ω, Real.exp (θ * X i ω) ∂iidCodeMeasure =
        (1 + 2 * Real.cosh θ) / 3 := by
    dsimp [X]
    rw [codeWalkCoordIncrement_mgf]
    rw [Real.cosh_eq]
    ring
  calc
    ∫ ω, Real.exp (θ * codeWalkCoordPartial s j m ω) ∂iidCodeMeasure =
        ∫ ω, ∏ i : Fin m, Real.exp (θ * X i ω) ∂iidCodeMeasure := by
          congr 1
          funext ω
          exact (hpoint ω).symm
    _ = ∏ i : Fin m, ∫ ω, Real.exp (θ * X i ω) ∂iidCodeMeasure := by
          exact hfac
    _ = ∏ _i : Fin m, ((1 + 2 * Real.cosh θ) / 3) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact hstep i
    _ = ((1 + 2 * Real.cosh θ) / 3) ^ m := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

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

private theorem cosh_le_exp_half_sq_local (x : ℝ) :
    Real.cosh x ≤ Real.exp (x ^ 2 / 2) := by
  rw [← (realHasSumCosh x).tsum_eq, Real.exp_eq_exp_ℝ, exp_eq_tsum ℝ]
  refine (realHasSumCosh x).summable.tsum_le_tsum (fun i => ?_)
    (expSeries_summable' (x ^ 2 / 2))
  simp only [div_pow, pow_mul, smul_eq_mul, inv_mul_eq_div, div_div]
  gcongr
  norm_cast
  exact Nat.two_pow_mul_factorial_le_factorial_two_mul _

end DirectedDistances.RandomWalk
