/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ConditionedFunctionalInterpolation
public import DirectedDistances.RandomWalk.IIDWalkMaximalTail
public import DirectedDistances.Probability.CenteredSumMoments
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Fourth moment bounds toward Lemma 4.11

These estimates provide moment inputs for the conditioned functional limit
argument in Lemma 4.11. They do not assert a functional limit theorem. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory
open scoped BigOperators

private abbrev coordBlockIncrement (a : ℕ) (j : Fin 2) (i : ℕ)
    (ω : ℕ → Fin 3) : ℝ := codeWalkCoordIncrement a j i ω

private theorem measurable_codeWalkCoordIncrementInt (a : ℕ) (j : Fin 2) (i : ℕ) :
    Measurable (codeWalkCoordIncrementInt a j i) := by
  have hvec : Measurable (fun ω =>
      codeWalk ω (a + i + 1) - codeWalk ω (a + i)) :=
    (measurable_codeWalk.eval (a := a + i + 1)).sub
      (measurable_codeWalk.eval (a := a + i))
  change Measurable (fun ω => if j.val = 0 then
    (codeWalk ω (a + i + 1) - codeWalk ω (a + i)).1
    else (codeWalk ω (a + i + 1) - codeWalk ω (a + i)).2)
  by_cases hj : j.val = 0
  · simpa [hj, Function.comp_def] using measurable_fst.comp hvec
  · simpa [hj, Function.comp_def] using measurable_snd.comp hvec

private theorem map_codeWalkCoordIncrement (a : ℕ) (j : Fin 2) (i : ℕ) :
    iidCodeMeasure.map (codeWalkCoordIncrement a j i) =
      (Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ)).map
        (fun z : ℤ => (z : ℝ)) := by
  change iidCodeMeasure.map
      ((fun z : ℤ => (z : ℝ)) ∘ codeWalkCoordIncrementInt a j i) = _
  rw [← Measure.map_map (measurable_of_countable (fun z : ℤ => (z : ℝ)))
    (measurable_codeWalkCoordIncrementInt a j i),
    map_codeWalkCoordIncrementInt]

private theorem identDistrib_codeWalkCoordIncrement (a : ℕ) (j : Fin 2) (i : ℕ) :
    IdentDistrib (coordBlockIncrement a j i) (coordBlockIncrement a j 0)
      iidCodeMeasure iidCodeMeasure := by
  refine ⟨(measurable_codeWalkCoordIncrement a j i).aemeasurable,
    (measurable_codeWalkCoordIncrement a j 0).aemeasurable, ?_⟩
  change iidCodeMeasure.map (codeWalkCoordIncrement a j i) =
    iidCodeMeasure.map (codeWalkCoordIncrement a j 0)
  rw [map_codeWalkCoordIncrement a j i, map_codeWalkCoordIncrement a j 0]

private theorem coordBlockIncrement_mean (a : ℕ) (j : Fin 2) :
    ∫ ω, codeWalkCoordIncrement a j 0 ω ∂iidCodeMeasure = 0 := by
  have hmap := map_codeWalkCoordIncrement a j 0
  calc
    ∫ ω, codeWalkCoordIncrement a j 0 ω ∂iidCodeMeasure =
        ∫ x : ℝ, x ∂iidCodeMeasure.map (codeWalkCoordIncrement a j 0) := by
          symm
          exact integral_map (measurable_codeWalkCoordIncrement a j 0).aemeasurable
            (by fun_prop)
    _ = ∫ x : ℝ, x ∂(Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ)).map
          (fun z : ℤ => (z : ℝ)) := by rw [hmap]
    _ = ∫ z : ℤ, (z : ℝ) ∂Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ) := by
          rw [integral_map (measurable_of_countable (fun z : ℤ => (z : ℝ))).aemeasurable
            (by fun_prop)]
    _ = 0 := by
          rw [Measure.uniformOfFinset, integral_finsetSum_measure]
          · simp [integral_smul_measure, integral_dirac]
          · intro z hz
            exact (integrable_dirac (f := fun x : ℤ => (x : ℝ)) (by simp)).smul_measure (by simp)

private theorem coordBlockIncrement_second_moment (a : ℕ) (j : Fin 2) :
    ∫ ω, (codeWalkCoordIncrement a j 0 ω) ^ 2 ∂iidCodeMeasure = (2 : ℝ) / 3 := by
  have hmap := map_codeWalkCoordIncrement a j 0
  calc
    ∫ ω, (codeWalkCoordIncrement a j 0 ω) ^ 2 ∂iidCodeMeasure =
        ∫ x : ℝ, x ^ 2 ∂iidCodeMeasure.map (codeWalkCoordIncrement a j 0) := by
          symm
          exact integral_map (measurable_codeWalkCoordIncrement a j 0).aemeasurable
            (by fun_prop)
    _ = ∫ x : ℝ, x ^ 2 ∂(Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ)).map
          (fun z : ℤ => (z : ℝ)) := by rw [hmap]
    _ = ∫ z : ℤ, ((z : ℝ) ^ 2) ∂Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ) := by
          rw [integral_map (measurable_of_countable (fun z : ℤ => (z : ℝ))).aemeasurable
            (by fun_prop)]
    _ = (2 : ℝ) / 3 := by
          rw [Measure.uniformOfFinset, integral_finsetSum_measure]
          · simp [integral_smul_measure, integral_dirac]
            norm_num
          · intro z hz
            exact (integrable_dirac (f := fun x : ℤ => ((x : ℝ) ^ 2)) (by simp)).smul_measure (by simp)

private theorem coordBlockIncrement_fourth_moment (a : ℕ) (j : Fin 2) :
    ∫ ω, (codeWalkCoordIncrement a j 0 ω) ^ 4 ∂iidCodeMeasure = (2 : ℝ) / 3 := by
  have hmap := map_codeWalkCoordIncrement a j 0
  calc
    ∫ ω, (codeWalkCoordIncrement a j 0 ω) ^ 4 ∂iidCodeMeasure =
        ∫ x : ℝ, x ^ 4 ∂iidCodeMeasure.map (codeWalkCoordIncrement a j 0) := by
          symm
          exact integral_map (measurable_codeWalkCoordIncrement a j 0).aemeasurable
            (by fun_prop)
    _ = ∫ x : ℝ, x ^ 4 ∂(Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ)).map
          (fun z : ℤ => (z : ℝ)) := by rw [hmap]
    _ = ∫ z : ℤ, ((z : ℝ) ^ 4) ∂Measure.uniformOfFinset ({-1, 0, 1} : Finset ℤ) := by
          rw [integral_map (measurable_of_countable (fun z : ℤ => (z : ℝ))).aemeasurable
            (by fun_prop)]
    _ = (2 : ℝ) / 3 := by
          rw [Measure.uniformOfFinset, integral_finsetSum_measure]
          · simp [integral_smul_measure, integral_dirac]
            norm_num
          · intro z hz
            exact (integrable_dirac (f := fun x : ℤ => ((x : ℝ) ^ 4)) (by simp)).smul_measure (by simp)

private theorem coordBlockIncrement_memLp_four (a : ℕ) (j : Fin 2) :
    MemLp (coordBlockIncrement a j 0) 4 iidCodeMeasure := by
  apply MemLp.of_bound (measurable_codeWalkCoordIncrement a j 0).aestronglyMeasurable 1
  filter_upwards with ω
  dsimp [coordBlockIncrement, codeWalkCoordIncrement, codeWalkCoordIncrementInt]
  have h := codeWalk_succ_sub_coord_abs_le_one ω a
  by_cases hj : j.val = 0
  · simp only [hj, ↓reduceIte, Int.cast_sub]
    exact_mod_cast h.1
  · simp only [hj, ↓reduceIte, Int.cast_sub]
    exact_mod_cast h.2

private theorem coordBlock_partial_sum_fourth_moment_le (a : ℕ) (j : Fin 2)
    {m : ℕ} (hm : 1 ≤ m) :
    ∫ ω, (DirectedDistances.Probability.centeredPartialSum
      (codeWalkCoordIncrement a j) m ω) ^ 4 ∂iidCodeMeasure ≤ (m : ℝ) ^ 2 * 2 := by
  have hsum := DirectedDistances.Probability.centeredPartialSum_fourth_moment_le
    (hind := by
      simpa [coordBlockIncrement] using iIndepFun_codeWalkCoordIncrement a j)
    (hmeas := fun i => measurable_codeWalkCoordIncrement a j i)
    (hid := fun i => identDistrib_codeWalkCoordIncrement a j i)
    (h4 := coordBlockIncrement_memLp_four a j)
    (hc := coordBlockIncrement_mean a j) hm
  rw [coordBlockIncrement_fourth_moment, coordBlockIncrement_second_moment] at hsum
  norm_num at hsum ⊢
  nlinarith [hsum]

private theorem coordBlock_sum_eq (a m : ℕ) (j : Fin 2) (ω : ℕ → Fin 3) :
    DirectedDistances.Probability.centeredPartialSum (coordBlockIncrement a j) m ω =
      if j.val = 0 then
        (((codeWalk ω (a + m)).1 : ℝ) - (codeWalk ω a).1) else
        (((codeWalk ω (a + m)).2 : ℝ) - (codeWalk ω a).2) := by
  unfold DirectedDistances.Probability.centeredPartialSum
  simp only [Finset.sum_apply]
  change (∑ i ∈ Finset.range m, codeWalkCoordIncrement a j i ω) = _
  by_cases hj : j.val = 0
  · simp only [codeWalkCoordIncrement, codeWalkCoordIncrementInt, hj, ↓reduceIte]
    calc
      (∑ i ∈ Finset.range m,
          ((codeWalk ω (a + i + 1) - codeWalk ω (a + i)).1 : ℝ)) =
          ∑ i ∈ Finset.range m, ((lazyTwoDimensionalStep (ω (a + i + 1))).1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [codeWalk_succ_sub]
      _ = (((codeWalk ω (a + m)).1 : ℝ) - (codeWalk ω a).1) := by
            have h := congrArg Prod.fst (codeWalk_block_sub_eq_sum ω a m)
            simp only [Prod.fst_sub, Prod.fst_sum] at h
            have hR := congrArg (fun z : ℤ => (z : ℝ)) h
            push_cast at hR
            exact hR.symm
  · simp only [codeWalkCoordIncrement, codeWalkCoordIncrementInt, hj, ↓reduceIte]
    calc
      (∑ i ∈ Finset.range m,
          ((codeWalk ω (a + i + 1) - codeWalk ω (a + i)).2 : ℝ)) =
          ∑ i ∈ Finset.range m, ((lazyTwoDimensionalStep (ω (a + i + 1))).2 : ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [codeWalk_succ_sub]
      _ = (((codeWalk ω (a + m)).2 : ℝ) - (codeWalk ω a).2) := by
            have h := congrArg Prod.snd (codeWalk_block_sub_eq_sum ω a m)
            simp only [Prod.snd_sub, Prod.snd_sum] at h
            have hR := congrArg (fun z : ℤ => (z : ℝ)) h
            push_cast at hR
            exact hR.symm

private theorem codeWalk_block_coordinate_fourth_moment_le (a : ℕ) (m : ℕ)
    (j : Fin 2) :
    ∫ ω, (if j.val = 0 then
      (((codeWalk ω (a + m)).1 : ℝ) - (codeWalk ω a).1) ^ 4 else
      (((codeWalk ω (a + m)).2 : ℝ) - (codeWalk ω a).2) ^ 4)
      ∂iidCodeMeasure ≤ (m : ℝ) ^ 2 * 2 := by
  by_cases hm : m = 0
  · subst m
    simp
  · have hm' : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hsum := coordBlock_partial_sum_fourth_moment_le a j hm'
    calc
      ∫ ω, (if j.val = 0 then
        (((codeWalk ω (a + m)).1 : ℝ) - (codeWalk ω a).1) ^ 4 else
        (((codeWalk ω (a + m)).2 : ℝ) - (codeWalk ω a).2) ^ 4) ∂iidCodeMeasure =
          ∫ ω, (DirectedDistances.Probability.centeredPartialSum
            (coordBlockIncrement a j) m ω) ^ 4 ∂iidCodeMeasure := by
              apply integral_congr_ae
              filter_upwards with ω
              rw [coordBlock_sum_eq a m j ω]
              by_cases hj : j.val = 0 <;> simp [hj]
      _ ≤ (m : ℝ) ^ 2 * 2 := hsum

private theorem codeWalk_block_coordinate_integrable (a m : ℕ) (j : Fin 2) :
    Integrable (fun ω => if j.val = 0 then
      (((codeWalk ω (a + m)).1 : ℝ) - (codeWalk ω a).1) ^ 4 else
      (((codeWalk ω (a + m)).2 : ℝ) - (codeWalk ω a).2) ^ 4) iidCodeMeasure := by
  have hsumMem : MemLp (DirectedDistances.Probability.centeredPartialSum
      (coordBlockIncrement a j) m) 4 iidCodeMeasure :=
    DirectedDistances.Probability.centeredPartialSum_memLp_four
      (fun i => identDistrib_codeWalkCoordIncrement a j i)
      (coordBlockIncrement_memLp_four a j) m
  have hsumInt := hsumMem.integrable_norm_pow (by norm_num)
  have hEq : (fun ω => ‖DirectedDistances.Probability.centeredPartialSum
      (coordBlockIncrement a j) m ω‖ ^ 4) =ᵐ[iidCodeMeasure]
      (fun ω => if j.val = 0 then
        (((codeWalk ω (a + m)).1 : ℝ) - (codeWalk ω a).1) ^ 4 else
        (((codeWalk ω (a + m)).2 : ℝ) - (codeWalk ω a).2) ^ 4) := by
    filter_upwards with ω
    rw [coordBlock_sum_eq a m j ω]
    by_cases hj : j.val = 0
    · simp only [hj, ↓reduceIte, Real.norm_eq_abs]
      rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤
        (((codeWalk ω (a + m)).1 : ℝ) - (codeWalk ω a).1) ^ 4)]
    · simp only [hj, ↓reduceIte, Real.norm_eq_abs]
      rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤
        (((codeWalk ω (a + m)).2 : ℝ) - (codeWalk ω a).2) ^ 4)]
  exact hsumInt.congr hEq

/-- Helper toward Lemma 4.11: the fourth power of the sup norm of a fixed
integer-time code-walk block is integrable under the iid code law. -/
theorem iidCodeWalk_block_fourth_moment_integrable (a m : ℕ) :
    Integrable (fun ω : ℕ → Fin 3 =>
      ‖(((codeWalk ω (a + m)).1 : ℝ) - (codeWalk ω a).1,
        ((codeWalk ω (a + m)).2 : ℝ) - (codeWalk ω a).2)‖ ^ 4) iidCodeMeasure := by
  let D : (ℕ → Fin 3) → ℝ × ℝ := fun ω =>
    (((codeWalk ω (a + m)).1 : ℝ) - (codeWalk ω a).1,
      ((codeWalk ω (a + m)).2 : ℝ) - (codeWalk ω a).2)
  have hmeas : Measurable D := by
    dsimp [D]
    have hf : Measurable (fun ω => ((codeWalk ω (a + m)).1 : ℝ)) :=
      (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
        (measurable_fst.comp (measurable_codeWalk.eval (a := a + m)))
    have hf0 : Measurable (fun ω => ((codeWalk ω a).1 : ℝ)) :=
      (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
        (measurable_fst.comp (measurable_codeWalk.eval (a := a)))
    have hs : Measurable (fun ω => ((codeWalk ω (a + m)).2 : ℝ)) :=
      (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
        (measurable_snd.comp (measurable_codeWalk.eval (a := a + m)))
    have hs0 : Measurable (fun ω => ((codeWalk ω a).2 : ℝ)) :=
      (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
        (measurable_snd.comp (measurable_codeWalk.eval (a := a)))
    exact (hf.sub hf0).prodMk (hs.sub hs0)
  have hbound (ω : ℕ → Fin 3) : ‖D ω‖ ≤ (m : ℝ) := by
    have hcoord := codeWalk_block_sub_coord_abs_le_length ω a m
    have hfst : |(((codeWalk ω (a + m)).1 : ℝ) - (codeWalk ω a).1)| ≤ (m : ℝ) := by
      rw [← Int.cast_sub]
      exact_mod_cast hcoord.1
    have hsnd : |(((codeWalk ω (a + m)).2 : ℝ) - (codeWalk ω a).2)| ≤ (m : ℝ) := by
      rw [← Int.cast_sub]
      exact_mod_cast hcoord.2
    dsimp [D]
    exact max_le hfst hsnd
  have hmem : MemLp D 4 iidCodeMeasure :=
    MemLp.of_bound hmeas.aestronglyMeasurable (m : ℝ)
      (Filter.Eventually.of_forall hbound)
  change Integrable (fun ω => ‖D ω‖ ^ 4) iidCodeMeasure
  exact hmem.integrable_norm_pow (by norm_num)

private theorem max_abs_fourth_le_add (x y : ℝ) :
    (max |x| |y|) ^ 4 ≤ x ^ 4 + y ^ 4 := by
  by_cases h : |x| ≤ |y|
  · rw [max_eq_right h, ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ y ^ 4)]
    exact le_add_of_nonneg_left (by positivity)
  · have h' := le_of_not_ge h
    rw [max_eq_left h', ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ x ^ 4)]
    exact le_add_of_nonneg_right (by positivity)

private theorem integral_max_abs_fourth_le_add {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : Integrable (fun ω => f ω ^ 4) μ)
    (hg : Integrable (fun ω => g ω ^ 4) μ)
    (hm : Integrable (fun ω => (max |f ω| |g ω|) ^ 4) μ)
    (hpoint : ∀ ω, (max |f ω| |g ω|) ^ 4 ≤ f ω ^ 4 + g ω ^ 4) :
    (∫ ω, (max |f ω| |g ω|) ^ 4 ∂μ) ≤
      (∫ ω, f ω ^ 4 ∂μ) + (∫ ω, g ω ^ 4 ∂μ) := by
  calc
    _ ≤ ∫ ω, f ω ^ 4 + g ω ^ 4 ∂μ :=
      integral_mono hm (hf.add hg) hpoint
    _ = _ := integral_add hf hg

/-- Helper toward Lemma 4.11: each coordinate of a code-walk block has fourth
moment at most `2*m^2`, so their maximum-norm fourth moment is at most `4*m^2`. -/
theorem iidCodeWalk_block_fourth_moment_le (a m : ℕ) :
    (∫ ω : ℕ → Fin 3,
      ‖(((codeWalk ω (a + m)).1 : ℝ) - (codeWalk ω a).1,
        ((codeWalk ω (a + m)).2 : ℝ) - (codeWalk ω a).2)‖ ^ 4 ∂iidCodeMeasure) ≤
      4 * (m : ℝ) ^ 2 := by
  let D : (ℕ → Fin 3) → ℝ × ℝ := fun ω =>
    (((codeWalk ω (a + m)).1 : ℝ) - (codeWalk ω a).1,
      ((codeWalk ω (a + m)).2 : ℝ) - (codeWalk ω a).2)
  have hfstInt : Integrable (fun ω : ℕ → Fin 3 =>
      (((codeWalk ω (a + m)).1 : ℝ) - (codeWalk ω a).1) ^ 4) iidCodeMeasure := by
    simpa using codeWalk_block_coordinate_integrable a m (0 : Fin 2)
  have hsndInt : Integrable (fun ω : ℕ → Fin 3 =>
      (((codeWalk ω (a + m)).2 : ℝ) - (codeWalk ω a).2) ^ 4) iidCodeMeasure := by
    simpa using codeWalk_block_coordinate_integrable a m (1 : Fin 2)
  have hDint := iidCodeWalk_block_fourth_moment_integrable a m
  have hpoint (ω : ℕ → Fin 3) : ‖D ω‖ ^ 4 ≤
      (((codeWalk ω (a + m)).1 : ℝ) - (codeWalk ω a).1) ^ 4 +
      (((codeWalk ω (a + m)).2 : ℝ) - (codeWalk ω a).2) ^ 4 := by
    change (max |((codeWalk ω (a + m)).1 : ℝ) - (codeWalk ω a).1|
      |((codeWalk ω (a + m)).2 : ℝ) - (codeWalk ω a).2|) ^ 4 ≤ _
    exact max_abs_fourth_le_add _ _
  have hfstMoment := codeWalk_block_coordinate_fourth_moment_le a m (0 : Fin 2)
  have hsndMoment := codeWalk_block_coordinate_fourth_moment_le a m (1 : Fin 2)
  have hmaxInt : Integrable (fun ω : ℕ → Fin 3 =>
      (max |((codeWalk ω (a + m)).1 : ℝ) - (codeWalk ω a).1|
        |((codeWalk ω (a + m)).2 : ℝ) - (codeWalk ω a).2|) ^ 4) iidCodeMeasure := by
    apply hDint.congr
    filter_upwards with ω
    simp [Prod.norm_def, Real.norm_eq_abs]
  have hfstMoment' :
      (∫ ω, (((codeWalk ω (a + m)).1 : ℝ) - (codeWalk ω a).1) ^ 4 ∂iidCodeMeasure) ≤
        2 * (m : ℝ) ^ 2 := by simpa [mul_comm] using hfstMoment
  have hsndMoment' :
      (∫ ω, (((codeWalk ω (a + m)).2 : ℝ) - (codeWalk ω a).2) ^ 4 ∂iidCodeMeasure) ≤
        2 * (m : ℝ) ^ 2 := by simpa [mul_comm] using hsndMoment
  have hsum := integral_max_abs_fourth_le_add hfstInt hsndInt hmaxInt
    (fun ω => max_abs_fourth_le_add _ _)
  have hfinal := hsum.trans (add_le_add hfstMoment' hsndMoment')
  have hEq : (∫ ω, ‖D ω‖ ^ 4 ∂iidCodeMeasure) =
      ∫ ω, (max |((codeWalk ω (a + m)).1 : ℝ) - (codeWalk ω a).1|
        |((codeWalk ω (a + m)).2 : ℝ) - (codeWalk ω a).2|) ^ 4 ∂iidCodeMeasure := by
    apply integral_congr_ae
    filter_upwards with ω
    simp [D, Prod.norm_def, Real.norm_eq_abs]
  calc
    (∫ ω, ‖D ω‖ ^ 4 ∂iidCodeMeasure) = _ := hEq
    _ ≤ 2 * (m : ℝ) ^ 2 + 2 * (m : ℝ) ^ 2 := hfinal
    _ = 4 * (m : ℝ) ^ 2 := by ring

end DirectedDistances.RandomWalk
