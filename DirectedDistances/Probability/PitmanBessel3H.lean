/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.PitmanBessel3E

/-! Supporting lemmas for paper labels `lem-cond-walk-bm` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.Probability
open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.RandomWalk
open scoped NNReal Topology

local instance pitman3HContinuousMapMeasurableSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    MeasurableSpace C(X, Y) := borel _
local instance pitman3HContinuousMapBorelSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    BorelSpace C(X, Y) := ⟨rfl⟩
local instance pitman3HContinuousMapSecondCountable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [LocallyCompactSpace X] [SecondCountableTopology Y] :
    SecondCountableTopology C(X, Y) := continuousPath_secondCountable

/-- Helper toward Lemma 4.11: the original endpoint and any finite collection
of transformed discrete evaluations, with the source variance removed. -/
@[expose] noncomputable def codePitmanFiniteData {k : ℕ} (t : Fin k → ℝ≥0)
    (n : ℕ) (ω : ℕ → Fin 3) : ℝ × (Fin k → ℝ) :=
  (((codeWalk ω n).1 : ℝ) / Real.sqrt n / Real.sqrt (2 / 3),
    fun i => ((vectorPitman (codeWalk ω) ⌊(n : ℝ) * t i⌋₊).1 : ℝ) /
      Real.sqrt n / Real.sqrt (2 / 3))

/-- Helper toward Lemma 4.11: measurability of the actual finite discrete data. -/
theorem measurable_codePitmanFiniteData {k : ℕ} (t : Fin k → ℝ≥0) (n : ℕ) :
    Measurable (codePitmanFiniteData t n) := by
  have hc := (measurable_pi_apply n).comp measurable_codeWalk
  have hv (j : ℕ) := (measurable_pi_apply j).comp
    (measurable_vectorPitmanPath.comp measurable_codeWalk)
  exact ((((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp hc.fst).div_const _).div_const _).prodMk
    (measurable_pi_iff.mpr fun i =>
      (((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
        (hv ⌊(n : ℝ) * t i⌋₊).fst).div_const _).div_const _)

/-- Helper toward Lemma 4.11: convergence jointly with the original endpoint,
at every finite collection of times (no ordering or distinctness required). -/
theorem codePitmanFiniteData_tendsto
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    {k : ℕ} (t : Fin k → ℝ≥0) :
    TendstoInDistribution (codePitmanFiniteData t) atTop
      (fun p => (p 1 0, fun i => scalarPitman (pathCoordinate p 0) (t i)))
      (fun _ => iidCodeMeasure) W₄ := by
  let X (n : ℕ) (ω : ℕ → Fin 3) : ℝ × (Fin k → ℝ) :=
    (standardFirstPath (diffusiveInterpolation n (codeWalk ω)) 1,
      fun i => scalarPitman (standardFirstPath (diffusiveInterpolation n (codeWalk ω))) (t i))
  have hX : TendstoInDistribution X atTop
      (fun p => (p 1 0, fun i => scalarPitman (pathCoordinate p 0) (t i)))
      (fun _ => iidCodeMeasure) W₄ :=
    TendstoInDistribution.continuous_comp
      (((continuous_eval_const (1 : ℝ≥0)).comp continuous_fst).prodMk
        (continuous_pi fun i => (continuous_eval_const (t i)).comp continuous_snd))
      (codeWalk_scalarPitman_joint_functional_tendsto W₄ hB hI)
  apply tendstoInDistribution_of_tendstoInMeasure_sub (codePitmanFiniteData t) _ hX _
    (fun n => (measurable_codePitmanFiniteData t n).aemeasurable)
  apply tendstoInMeasure_of_tendsto_ae
    (fun n => ((measurable_codePitmanFiniteData t n).aemeasurable.sub
      (hX.forall_aemeasurable n)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro ω
  have hi : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hb : Tendsto (fun n : ℕ => 3 / Real.sqrt n / Real.sqrt (2 / 3)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div, div_eq_mul_inv, zero_mul] using
      ((tendsto_const_nhds (x := (3 : ℝ))).mul hi).div_const (Real.sqrt (2 / 3))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Pi.zero_apply, sub_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hb
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hg := diffusiveInterpolation_grid n hn (codeWalk ω) n
  rw [div_self hn0] at hg
  rw [Prod.norm_def]
  apply max_le
  · change |((codeWalk ω n).1 : ℝ) / Real.sqrt n / Real.sqrt (2 / 3) -
      (diffusiveInterpolation n (codeWalk ω) 1).1 / Real.sqrt (2 / 3)| ≤ _
    rw [hg, sub_self, abs_zero]
    positivity
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have he := (diffusiveStep_vectorPitman_sub_abs_le n hn (codeWalk ω)
      (codeWalk_real_coord_increment_abs_le ω) (t i)).1
    have hp := congrArg (fun f : C(ℝ≥0, ℝ) => f (t i))
      (standardFirstPath_vectorPitman (diffusiveInterpolation n (codeWalk ω)))
    change (continuousVectorPitman (diffusiveInterpolation n (codeWalk ω)) (t i)).1 /
      Real.sqrt (2 / 3) = _ at hp
    change |((vectorPitman (codeWalk ω) ⌊(n : ℝ) * t i⌋₊).1 : ℝ) /
      Real.sqrt n / Real.sqrt (2 / 3) -
      scalarPitman (standardFirstPath (diffusiveInterpolation n (codeWalk ω))) (t i)| ≤ _
    rw [← hp, ← sub_div, abs_div,
      abs_of_pos (show 0 < Real.sqrt (2 / 3 : ℝ) by positivity)]
    exact div_le_div_of_nonneg_right he (Real.sqrt_nonneg _)

/-- Helper toward Lemma 4.11: every floor time at or before one belongs to the
actual finite source prefix, including the endpoint and scale zero. -/
theorem pitman_floor_le (n : ℕ) (t : ℝ≥0) (ht : t ≤ 1) :
    ⌊(n : ℝ) * t⌋₊ ≤ n := by
  apply Nat.floor_le_of_le
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (show (t : ℝ) ≤ 1 from ht) (Nat.cast_nonneg n)

/-- Helper toward Lemma 4.11: joint observations on the finite lazy carrier,
with every observation constrained only to lie in its time horizon. -/
@[expose] noncomputable def lazyPitmanFiniteData {k : ℕ} (t : Fin k → ℝ≥0)
    (ht : ∀ i, t i ≤ 1) (n : ℕ) (p : LazyPath n) : ℝ × (Fin k → ℝ) :=
  ((p.val (Fin.last n) : ℝ) / Real.sqrt n / Real.sqrt (2 / 3),
    fun i => ((lazyPhi p).val.val
      ⟨⌊(n : ℝ) * t i⌋₊, Nat.lt_succ_of_le (pitman_floor_le n (t i) (ht i))⟩ : ℝ) /
        Real.sqrt n / Real.sqrt (2 / 3))

private theorem sourceScalarWalk_eq (ω : ℕ → Fin 3) :
    globalIIDLazyWalk (fun i (v : ℕ → Fin 3) => v (i + 1)) ω =
      fun n => (codeWalk ω n).1 := by
  funext n
  simp only [globalIIDLazyWalk, codeWalk, Prod.fst_sum, lazyTwoDimensionalStep]

/-- Helper toward Lemma 4.11: the actual code prefix realizes all the finite
observations simultaneously; the transform is taken before observation. -/
theorem lazyPitmanFiniteData_prefix {k : ℕ} (t : Fin k → ℝ≥0)
    (ht : ∀ i, t i ≤ 1) (n : ℕ) (ω : ℕ → Fin 3) :
    lazyPitmanFiniteData t ht n
      (lazyIIDPrefix (fun i (v : ℕ → Fin 3) => v (i + 1)) n ω) =
        codePitmanFiniteData t n ω := by
  apply Prod.ext
  · simp only [lazyPitmanFiniteData, codePitmanFiniteData, lazyIIDPrefix_apply,
      sourceScalarWalk_eq, Fin.val_last]
  · funext i
    have hq := pitmanIIDPrefix_apply_global
      (fun i (v : ℕ → Fin 3) => v (i + 1)) n ω
      ⟨⌊(n : ℝ) * t i⌋₊, Nat.lt_succ_of_le (pitman_floor_le n (t i) (ht i))⟩
    rw [sourceScalarWalk_eq] at hq
    change (lazyPhi (lazyIIDPrefix (fun i (v : ℕ → Fin 3) => v (i + 1)) n ω)).val.val
      ⟨⌊(n : ℝ) * t i⌋₊, Nat.lt_succ_of_le (pitman_floor_le n (t i) (ht i))⟩ = _ at hq
    change ((lazyPhi (lazyIIDPrefix (fun i (v : ℕ → Fin 3) => v (i + 1)) n ω)).val.val _ : ℝ) /
      Real.sqrt n / Real.sqrt (2 / 3) = _
    rw [hq]
    rfl

/-- Helper toward Lemma 4.11: the original endpoint and every finite past
Pitman observation converge jointly on the exact finite uniform path spaces. -/
theorem lazyPitmanFiniteData_tendsto
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    {k : ℕ} (t : Fin k → ℝ≥0) (ht : ∀ i, t i ≤ 1) :
    TendstoInDistribution (lazyPitmanFiniteData t ht) atTop
      (fun p => (p 1 0, fun i => scalarPitman (pathCoordinate p 0) (t i)))
      (fun n => (uniformLazyPath n).toMeasure) W₄ := by
  have h := codePitmanFiniteData_tendsto W₄ hB hI t
  have hlaw (n : ℕ) : HasLaw (codePitmanFiniteData t n)
      ((uniformLazyPath n).toMeasure.map (lazyPitmanFiniteData t ht n)) iidCodeMeasure := by
    have hh := (hasLaw_map (measurable_of_countable
      (lazyPitmanFiniteData t ht n)).aemeasurable).comp (codeWalk_lazyPrefix_hasLaw n)
    simpa only [Function.comp_def, lazyPitmanFiniteData_prefix] using hh
  refine ⟨fun n => (measurable_of_countable _).aemeasurable, h.aemeasurable_limit, ?_⟩
  apply h.tendsto.congr'
  apply Filter.Eventually.of_forall
  intro n
  exact ProbabilityMeasure.toMeasure_injective (hlaw n).map_eq

end DirectedDistances.Probability
