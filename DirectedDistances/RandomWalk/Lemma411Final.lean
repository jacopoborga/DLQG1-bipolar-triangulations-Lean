/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.PitmanBessel3O
public import DirectedDistances.RandomWalk.ConditionedLimitAssembly
public import DirectedDistances.RandomWalk.IIDWalkFunctionalConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! Supporting lemmas for paper labels `lem-cond-walk-bm` (see CORRESPONDENCE.md). -/




public section
namespace DirectedDistances.RandomWalk.Lemma411Final

open MeasureTheory ProbabilityTheory Filter Set
open DirectedDistances.Probability
open scoped Topology NNReal ENNReal

-- The local path-space measurable structures are the canonical Borel structures.
local instance instMeasurableSpaceCPath_Lemma411Final
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    MeasurableSpace C(X, Y) := borel _
local instance instBorelCPath_Lemma411Final
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    BorelSpace C(X, Y) := ⟨rfl⟩
local instance instSecondCountableCPath_Lemma411Final
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [LocallyCompactSpace X] [SecondCountableTopology Y] :
    SecondCountableTopology C(X, Y) := continuousPath_secondCountable

private theorem minimum_succ (p : ℕ → ℤ) (n : ℕ) :
    globalLazyRunningMinimum p (n + 1) = min (globalLazyRunningMinimum p n) (p (n + 1)) := by
  have h := runningMinimum_succ (fun j : Fin (n + 1 + 1) => p j.val)
    (⟨n, by omega⟩ : Fin (n + 1))
  simpa only [runningMinimum_prefix_eq_global, Fin.val_succ, Fin.val_castSucc] using h

private theorem pitman_steps {z : ℕ → ℤ × ℤ}
    (hs : ∀ i, z (i + 1) - z i ∈
      ({(1, -1), (-1, 0), (0, 1)} : Set (ℤ × ℤ))) (n : ℕ) :
    vectorPitman z (n + 1) - vectorPitman z n ∈
      ({(1, -1), (-1, 0), (0, 1)} : Set (ℤ × ℤ)) := by
  have hm := globalLazyRunningMinimum_le (fun k => (z k).1) (i := n) le_rfl
  have h := hs n
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
  rcases h with h | h | h
  all_goals
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    simp only [Prod.fst_sub, Prod.snd_sub] at h₁ h₂
    simp only [vectorPitman, globalLazyPhi, minimum_succ]
  · left
    apply Prod.ext <;> dsimp <;> rw [min_eq_left (by omega)] <;> omega
  · by_cases hh : globalLazyRunningMinimum (fun k => (z k).1) n ≤ (z (n + 1)).1
    · right; left
      apply Prod.ext <;> dsimp <;> rw [min_eq_left hh] <;> omega
    · left
      apply Prod.ext <;> dsimp <;> rw [min_eq_right (by omega)] <;> omega
  · right; right
    apply Prod.ext <;> dsimp <;> rw [min_eq_left (by omega)] <;> omega

/-- Helper toward Lemma 4.11: the actual coupled conditioned walk has unit
coordinate increments for every code sequence. -/
theorem vectorPitman_codeWalk_real_coord_increment_abs_le (ω : ℕ → Fin 3) (k : ℕ) :
    |((vectorPitman (codeWalk ω) (k + 1)).1 : ℝ) -
      (vectorPitman (codeWalk ω) k).1| ≤ 1 ∧
    |((vectorPitman (codeWalk ω) (k + 1)).2 : ℝ) -
      (vectorPitman (codeWalk ω) k).2| ≤ 1 := by
  have hs (i : ℕ) : codeWalk ω (i + 1) - codeWalk ω i ∈
      ({(1, -1), (-1, 0), (0, 1)} : Set (ℤ × ℤ)) := by
    rw [codeWalk_succ_sub]
    generalize ω (i + 1) = c
    fin_cases c <;> norm_num [lazyTwoDimensionalStep]
  have h := pitman_steps hs k
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rw [← Int.cast_sub, ← Int.cast_sub]
  rcases h with h | h | h <;>
    have h₁ := congrArg Prod.fst h <;>
    have h₂ := congrArg Prod.snd h <;>
    simp only [Prod.fst_sub, Prod.snd_sub] at h₁ h₂ <;>
    rw [h₁, h₂] <;> norm_num

/-- Helper toward Lemma 4.11: the two continuous paths in the coupling are
within `4 / sqrt n` in compact supremum distance, uniformly in the horizon and sample. -/
theorem codeWalk_vectorPitman_compact_interpolation_dist_le
    (n : ℕ) (hn : 0 < n) (ω : ℕ → Fin 3) (T : ℝ≥0) :
    dist (compactPathRestriction T (diffusiveInterpolation n (vectorPitman (codeWalk ω))))
      (compactPathRestriction T
        (continuousVectorPitman (diffusiveInterpolation n (codeWalk ω)))) ≤
      4 / Real.sqrt n := by
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro t
  have ha := diffusiveStep_sub_interpolation_abs_le n (vectorPitman (codeWalk ω))
    (vectorPitman_codeWalk_real_coord_increment_abs_le ω) t.val
  have hb := diffusiveStep_vectorPitman_sub_abs_le n hn (codeWalk ω)
    (codeWalk_real_coord_increment_abs_le ω) t.val
  change max (|(diffusiveInterpolation n (vectorPitman (codeWalk ω)) t.val).1 -
      (continuousVectorPitman (diffusiveInterpolation n (codeWalk ω)) t.val).1|)
    (|(diffusiveInterpolation n (vectorPitman (codeWalk ω)) t.val).2 -
      (continuousVectorPitman (diffusiveInterpolation n (codeWalk ω)) t.val).2|) ≤ _
  apply max_le
  · have h := abs_sub_le
      (diffusiveInterpolation n (vectorPitman (codeWalk ω)) t.val).1
      (diffusiveStep n (vectorPitman (codeWalk ω)) t.val).1
      (continuousVectorPitman (diffusiveInterpolation n (codeWalk ω)) t.val).1
    have ha₁ := ha.1
    rw [abs_sub_comm] at ha₁
    simp only [div_eq_mul_inv, one_mul] at ha₁ hb ⊢
    linarith only [h, ha₁, hb.1]
  · have h := abs_sub_le
      (diffusiveInterpolation n (vectorPitman (codeWalk ω)) t.val).2
      (diffusiveStep n (vectorPitman (codeWalk ω)) t.val).2
      (continuousVectorPitman (diffusiveInterpolation n (codeWalk ω)) t.val).2
    have ha₂ := ha.2
    rw [abs_sub_comm] at ha₂
    have hp : 0 ≤ 1 / Real.sqrt (n : ℝ) := by positivity
    simp only [div_eq_mul_inv, one_mul] at ha₂ hb hp ⊢
    linarith only [h, ha₂, hb.2, hp]

/-- Helper toward Lemma 4.11: the compact interpolation discrepancy converges
to zero in probability, by a deterministic bound shared by all samples. -/
theorem codeWalk_vectorPitman_compact_interpolation_tendstoInMeasure (T : ℝ≥0) :
    TendstoInMeasure iidCodeMeasure
      (fun n ω => compactPathRestriction T (diffusiveInterpolation n (vectorPitman (codeWalk ω))) -
        compactPathRestriction T
          (continuousVectorPitman (diffusiveInterpolation n (codeWalk ω)))) atTop 0 := by
  apply tendstoInMeasure_iff_norm.mpr
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => 4 / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 4
  apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0)).congr'
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_gt_atTop 0] with n hn hn0
  have he : {ω : ℕ → Fin 3 | ε ≤ ‖(compactPathRestriction T
      (diffusiveInterpolation n (vectorPitman (codeWalk ω))) -
      compactPathRestriction T (continuousVectorPitman
        (diffusiveInterpolation n (codeWalk ω)))) - 0‖} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    simp only [sub_zero, ← dist_eq_norm] at hω
    exact (not_le_of_gt ((codeWalk_vectorPitman_compact_interpolation_dist_le n hn0 ω T).trans_lt hn)) hω
  change (0 : ℝ≥0∞) = iidCodeMeasure {ω : ℕ → Fin 3 | ε ≤ ‖(compactPathRestriction T
      (diffusiveInterpolation n (vectorPitman (codeWalk ω))) -
      compactPathRestriction T (continuousVectorPitman
        (diffusiveInterpolation n (codeWalk ω)))) - 0‖}
  rw [he, measure_empty]

/-- Helper toward Lemma 4.11: the interpolation of the discrete Pitman walk
has the continuous Pitman image as its functional limit, without a Brownian identification. -/
theorem codeWalk_vectorPitman_interpolation_functional_tendsto
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄) :
    TendstoInDistribution
      (fun n ω => diffusiveInterpolation n (vectorPitman (codeWalk ω))) atTop
      (fun p => continuousVectorPitman (iidBrownianPath p)) (fun _ => iidCodeMeasure) W₄ := by
  have hm (n : ℕ) : Measurable
      (fun ω => diffusiveInterpolation n (vectorPitman (codeWalk ω))) :=
    (continuous_diffusiveInterpolation n).measurable.comp
      (measurable_vectorPitmanPath.comp measurable_codeWalk)
  have hl := (codeWalk_interpolation_functional_tendsto W₄ hB hI).continuous_comp
    continuous_continuousVectorPitman
  let μ : ℕ → ProbabilityMeasure C(ℝ≥0, ℝ × ℝ) := fun n =>
    ⟨iidCodeMeasure.map (fun ω => diffusiveInterpolation n (vectorPitman (codeWalk ω))),
      (Measure.isProbabilityMeasure_map_iff (hm n).aemeasurable).mpr inferInstance⟩
  let ν : ProbabilityMeasure C(ℝ≥0, ℝ × ℝ) :=
    ⟨W₄.map (fun p => continuousVectorPitman (iidBrownianPath p)),
      (Measure.isProbabilityMeasure_map_iff
        (continuous_continuousVectorPitman.comp continuous_iidBrownianPath).measurable.aemeasurable).mpr
          inferInstance⟩
  refine ⟨fun n => (hm n).aemeasurable,
    (continuous_continuousVectorPitman.comp continuous_iidBrownianPath).measurable.aemeasurable, ?_⟩
  change Tendsto μ atTop (𝓝 ν)
  apply continuousPath_tendsto_of_compact_restrictions_inDistribution
  intro T
  have hc := tendstoInDistribution_of_tendstoInMeasure_sub
    (fun n ω => compactPathRestriction T (diffusiveInterpolation n (vectorPitman (codeWalk ω))))
    (fun p => compactPathRestriction T (continuousVectorPitman (iidBrownianPath p)))
    (hl.continuous_comp (continuous_compactPathRestriction T))
    (codeWalk_vectorPitman_compact_interpolation_tendstoInMeasure T)
    (fun n => ((continuous_compactPathRestriction T).measurable.comp (hm n)).aemeasurable)
  refine ⟨fun _ => (continuous_compactPathRestriction T).measurable.aemeasurable,
    (continuous_compactPathRestriction T).measurable.aemeasurable, ?_⟩
  have he (n : ℕ) : (μ n).map (compactPathRestriction T) =
      (⟨iidCodeMeasure.map (fun ω => compactPathRestriction T
        (diffusiveInterpolation n (vectorPitman (codeWalk ω)))),
        (Measure.isProbabilityMeasure_map_iff (hc.forall_aemeasurable n)).mpr inferInstance⟩ :
        ProbabilityMeasure C(Icc (0 : ℝ≥0) T, ℝ × ℝ)) := by
    apply ProbabilityMeasure.toMeasure_injective
    exact Measure.map_map (continuous_compactPathRestriction T).measurable (hm n)
  have he' : ν.map (compactPathRestriction T) =
      (⟨W₄.map (fun p => compactPathRestriction T
        (continuousVectorPitman (iidBrownianPath p))),
        (Measure.isProbabilityMeasure_map_iff hc.aemeasurable_limit).mpr inferInstance⟩ :
        ProbabilityMeasure C(Icc (0 : ℝ≥0) T, ℝ × ℝ)) := by
    apply ProbabilityMeasure.toMeasure_injective
    exact Measure.map_map (continuous_compactPathRestriction T).measurable
      (continuous_continuousVectorPitman.comp continuous_iidBrownianPath).measurable
  change Tendsto (fun n => (μ n).map (compactPathRestriction T)) atTop
    (𝓝 (ν.map (compactPathRestriction T)))
  simp only [he, he']
  exact hc.tendsto

/-- Helper toward Lemma 4.11: the source-conditioned interpolated walk converges
in the locally uniform topology, conditional on the whole-path Pitman identity. -/
theorem conditioned_interpolation_functional_tendsto_of_pitman_identification
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (H2 : (iidBrownianPathLaw W₄).map continuousVectorPitman =
      conditionedBrownianPathLaw W₄) :
    TendstoInDistribution (fun n z => diffusiveInterpolation n z) atTop
      conditionedBrownianPath (fun _ => conditionedVectorPathLaw 0 0) W₄ := by
  have h := codeWalk_vectorPitman_interpolation_functional_tendsto W₄ hB hI
  refine ⟨fun n => (continuous_diffusiveInterpolation n).measurable.aemeasurable,
    continuous_conditionedBrownianPath.measurable.aemeasurable, ?_⟩
  have he (n : ℕ) :
      (⟨(conditionedVectorPathLaw 0 0).map (diffusiveInterpolation n), inferInstance⟩ :
        ProbabilityMeasure C(ℝ≥0, ℝ × ℝ)) =
      ⟨iidCodeMeasure.map (fun ω => diffusiveInterpolation n (vectorPitman (codeWalk ω))),
        (Measure.isProbabilityMeasure_map_iff (h.forall_aemeasurable n)).mpr inferInstance⟩ := by
    apply ProbabilityMeasure.toMeasure_injective
    exact conditionedInterpolationPathLaw_eq_map n
  have he' :
      (⟨W₄.map conditionedBrownianPath, inferInstance⟩ : ProbabilityMeasure C(ℝ≥0, ℝ × ℝ)) =
      ⟨W₄.map (fun p => continuousVectorPitman (iidBrownianPath p)),
        (Measure.isProbabilityMeasure_map_iff h.aemeasurable_limit).mpr inferInstance⟩ := by
    apply ProbabilityMeasure.toMeasure_injective
    exact (lemma411_limit_law_rewrite W₄ hB hI H2).symm
  simp only [he, he']
  exact h.tendsto

/-- Helper toward Lemma 4.11: for every four-coordinate Brownian path law with independent
coordinates, the source-conditioned interpolated walk converges in the locally uniform topology. -/
theorem lemma411_conditioned_interpolation_functional_limit
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄) :
    TendstoInDistribution
      (fun n (z : ℕ → ℤ × ℤ) => diffusiveInterpolation n z) atTop
      conditionedBrownianPath (fun _ => conditionedVectorPathLaw 0 0) W₄ := by
  have H2 : (iidBrownianPathLaw W₄).map continuousVectorPitman =
      conditionedBrownianPathLaw W₄ :=
    DirectedDistances.Probability.iidBrownianPathLaw_map_continuousVectorPitman W₄ hB hI
  exact conditioned_interpolation_functional_tendsto_of_pitman_identification W₄ hB hI H2

end DirectedDistances.RandomWalk.Lemma411Final
