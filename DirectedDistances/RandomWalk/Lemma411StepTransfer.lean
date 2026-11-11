/- EXACT TARGET AND INTERFACES

Common carrier U := ℝ≥0 →ᵤ[{K | IsCompact K}] (ℝ × ℝ), with borel U.
The step path is diffusiveStep, without any continuity assertion in time.

Final target (proved below):
theorem lemma411_conditioned_step_functional_limit
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄) :
    TendstoInDistribution
      (fun n z => UniformOnFun.ofFun {K | IsCompact K} (diffusiveStep n z)) atTop
      (fun p => UniformOnFun.ofFun {K | IsCompact K} (conditionedBrownianPath p))
      (fun _ => conditionedVectorPathLaw 0 0) W₄

Interfaces used below:
* ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.uniformContinuous.continuous;
* UniformOnFun.continuous_rng_iff and finitely many discrete path coordinates;
* map_vectorPitman_codeWalk, vectorPitman_codeWalk_real_coord_increment_abs_le,
  diffusiveStep_sub_interpolation_abs_le, and Real.tendsto_sqrt_atTop;
* TendstoInDistribution.continuous_comp for the interpolation limit;
* UniformOnFun.isCountablyGenerated_uniformity and a compatible pseudometric;
  ProbabilityMeasure.tendsto_of_forall_isClosed_limsup_le' for transfer.

Exact generic transfer interface, with U and its Borel measurable space as above:
theorem tendstoInDistribution_of_compact_ae_close
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ω') [IsProbabilityMeasure ν]
    (X Y : ℕ → Ω → U) (Z : Ω' → U)
    (hX : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    (hY : ∀ n, AEMeasurable (Y n) μ)
    (hclose : ∀ K : Set ℝ≥0, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, ∀ t ∈ K,
        dist (UniformOnFun.toFun {K | IsCompact K} (X n ω) t)
          (UniformOnFun.toFun {K | IsCompact K} (Y n ω) t) < ε) :
    TendstoInDistribution Y atTop Z (fun _ => μ) ν

Both target statements are proved below. This comment adds no assumptions. -/
module

public import DirectedDistances.RandomWalk.Lemma411Final
public import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Topology.Metrizable.Uniformity

/-! Helper toward Lemma 4.11: transfer from interpolation to the literal floor process. -/

public section
namespace DirectedDistances.RandomWalk.Lemma411StepTransfer

open MeasureTheory ProbabilityTheory Filter Set
open DirectedDistances.Probability
open scoped Topology NNReal ENNReal Uniformity

/-- Helper toward Lemma 4.11: the common path space carries its Borel measurable space. -/
local instance instMeasurableU_Lemma411StepTransfer :
    MeasurableSpace (UniformOnFun ℝ≥0 (ℝ × ℝ) {K | IsCompact K}) := borel _
/-- Helper toward Lemma 4.11: the common path measurable structure is Borel. -/
local instance instBorelU_Lemma411StepTransfer :
    BorelSpace (UniformOnFun ℝ≥0 (ℝ × ℝ) {K | IsCompact K}) := ⟨rfl⟩

/-- Helper toward Lemma 4.11: continuous paths embed continuously in the common
space of all paths with uniform convergence on compact sets. -/
theorem continuous_continuousPath_toUniformOnFun :
    Continuous (fun f : C(ℝ≥0, ℝ × ℝ) =>
      UniformOnFun.ofFun {K | IsCompact K} f) :=
  ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.uniformContinuous.continuous

/-- Helper toward Lemma 4.11: the literal step path depends continuously on
the discrete path in the topology of uniform convergence on compact sets. -/
theorem continuous_diffusiveStep_uniformOnFun (n : ℕ) :
    Continuous (fun z : ℕ → ℤ × ℤ =>
      UniformOnFun.ofFun {K | IsCompact K} (diffusiveStep n z)) := by
  apply UniformOnFun.continuous_rng_iff.mpr
  intro K hK
  obtain ⟨T, hT⟩ := hK.bddAbove
  let M : ℕ := ⌊(n : ℝ) * T⌋₊
  have hidx (t : K) : ⌊(n : ℝ) * t.val⌋₊ < M + 1 := by
    apply Nat.lt_succ_of_le
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hT t.property) (Nat.cast_nonneg n)
  let g : (Fin (M + 1) → ℤ × ℤ) → UniformFun K (ℝ × ℝ) := fun p =>
    UniformFun.ofFun (fun t =>
      (((p ⟨⌊(n : ℝ) * t.val⌋₊, hidx t⟩).1 : ℝ) / Real.sqrt n,
       ((p ⟨⌊(n : ℝ) * t.val⌋₊, hidx t⟩).2 : ℝ) / Real.sqrt n))
  have hg : Continuous g := continuous_of_discreteTopology
  have hr : Continuous (fun z : ℕ → ℤ × ℤ => fun i : Fin (M + 1) => z i.val) :=
    continuous_pi (fun i => continuous_apply i.val)
  exact hg.comp hr

/-- Helper toward Lemma 4.11: the step path is Borel measurable for the
product measurable space on discrete walk coordinates. -/
theorem measurable_diffusiveStep_uniformOnFun (n : ℕ) :
    Measurable (fun z : ℕ → ℤ × ℤ =>
      (UniformOnFun.ofFun {K | IsCompact K} (diffusiveStep n z) :
        UniformOnFun ℝ≥0 (ℝ × ℝ) {K | IsCompact K})) :=
  (continuous_diffusiveStep_uniformOnFun n).measurable

/-- Helper toward Lemma 4.11: under the actual conditioned law, both
coordinate increments are bounded by one, simultaneously at every integer time. -/
theorem conditionedVectorPathLaw_ae_coord_increment_abs_le :
    ∀ᵐ z ∂conditionedVectorPathLaw 0 0, ∀ k,
      |((z (k + 1)).1 : ℝ) - (z k).1| ≤ 1 ∧
      |((z (k + 1)).2 : ℝ) - (z k).2| ≤ 1 := by
  have hp : MeasurableSet {z : ℕ → ℤ × ℤ | ∀ k,
      |((z (k + 1)).1 : ℝ) - (z k).1| ≤ 1 ∧
      |((z (k + 1)).2 : ℝ) - (z k).2| ≤ 1} := by
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    have h₁ : Continuous (fun z : ℕ → ℤ × ℤ =>
        |((z (k + 1)).1 : ℝ) - (z k).1|) := by fun_prop
    have h₂ : Continuous (fun z : ℕ → ℤ × ℤ =>
        |((z (k + 1)).2 : ℝ) - (z k).2|) := by fun_prop
    exact (isClosed_le h₁ continuous_const).measurableSet.inter
      (isClosed_le h₂ continuous_const).measurableSet
  rw [← map_vectorPitman_codeWalk]
  apply (ae_map_iff
    (measurable_vectorPitmanPath.comp measurable_codeWalk).aemeasurable hp).mpr
  exact ae_of_all _ Lemma411Final.vectorPitman_codeWalk_real_coord_increment_abs_le

/-- Helper toward Lemma 4.11: the step and interpolation are eventually
uniformly close on every compact, on the same full-measure set of conditioned walks. -/
theorem conditionedVectorPathLaw_ae_step_interpolation_close :
    ∀ᵐ z ∂conditionedVectorPathLaw 0 0, ∀ K : Set ℝ≥0, IsCompact K →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ t ∈ K,
        dist (diffusiveStep n z t) (diffusiveInterpolation n z t) < ε := by
  filter_upwards [conditionedVectorPathLaw_ae_coord_increment_abs_le] with z hz
  intro K _ ε hε
  have hlim : Tendsto (fun n : ℕ => 1 / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 1
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
  intro t _
  have h := diffusiveStep_sub_interpolation_abs_le n z hz t
  change max |(diffusiveStep n z t).1 - (diffusiveInterpolation n z t).1|
    |(diffusiveStep n z t).2 - (diffusiveInterpolation n z t).2| < ε
  exact (max_le h.1 h.2).trans_lt hn

/-- Helper toward Lemma 4.11: the supremum of the step/interpolation distance
over any set of times has the same deterministic bound `1 / sqrt n`. -/
theorem diffusiveStep_interpolation_sup_dist_le (n : ℕ) (z : ℕ → ℤ × ℤ)
    (hz : ∀ k, |((z (k + 1)).1 : ℝ) - (z k).1| ≤ 1 ∧
      |((z (k + 1)).2 : ℝ) - (z k).2| ≤ 1) (K : Set ℝ≥0) :
    sSup ((fun t => dist (diffusiveStep n z t) (diffusiveInterpolation n z t)) '' K) ≤
      1 / Real.sqrt n := by
  rcases K.eq_empty_or_nonempty with rfl | hK
  · simp only [image_empty, Real.sSup_empty]
    positivity
  · apply csSup_le (hK.image _)
    rintro b ⟨t, _, rfl⟩
    have h := diffusiveStep_sub_interpolation_abs_le n z hz t
    exact max_le h.1 h.2

/-- Helper toward Lemma 4.11: almost surely the compact supremum distance
between the step and interpolation is eventually strictly smaller than any positive tolerance. -/
theorem conditionedVectorPathLaw_eventually_ae_step_interpolation_sup_lt
    (K : Set ℝ≥0) (_hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ᵐ z ∂conditionedVectorPathLaw 0 0,
      sSup ((fun t => dist (diffusiveStep n z t) (diffusiveInterpolation n z t)) '' K) < ε := by
  have hlim : Tendsto (fun n : ℕ => 1 / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 1
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
  filter_upwards [conditionedVectorPathLaw_ae_coord_increment_abs_le] with z hz
  exact (diffusiveStep_interpolation_sup_dist_le n z hz K).trans_lt hn

/-- Helper toward Lemma 4.11: the compact closeness estimate has a
deterministic eventual index, before the almost-sure quantifier. -/
theorem conditionedVectorPathLaw_eventually_ae_step_interpolation_close
    (K : Set ℝ≥0) (_hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ᵐ z ∂conditionedVectorPathLaw 0 0, ∀ t ∈ K,
      dist (diffusiveStep n z t) (diffusiveInterpolation n z t) < ε := by
  have hlim : Tendsto (fun n : ℕ => 1 / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 1
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
  filter_upwards [conditionedVectorPathLaw_ae_coord_increment_abs_le] with z hz
  intro t _
  have h := diffusiveStep_sub_interpolation_abs_le n z hz t
  change max |(diffusiveStep n z t).1 - (diffusiveInterpolation n z t).1|
    |(diffusiveStep n z t).2 - (diffusiveInterpolation n z t).2| < ε
  exact (max_le h.1 h.2).trans_lt hn

/-- Helper toward Lemma 4.11: converging together for probability laws in
a pseudometric space, using eventual almost-sure closeness and no separability premise. -/
theorem tendstoInDistribution_of_eventually_ae_dist_lt
    {E Ω Ω' : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ω') [IsProbabilityMeasure ν]
    (X Y : ℕ → Ω → E) (Z : Ω' → E)
    (hX : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    (hY : ∀ n, AEMeasurable (Y n) μ)
    (hclose : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, dist (X n ω) (Y n ω) < ε) :
    TendstoInDistribution Y atTop Z (fun _ => μ) ν := by
  refine ⟨hY, hX.aemeasurable_limit, ?_⟩
  apply tendsto_of_forall_isClosed_limsup_le'
  intro F hF
  have hb (ε : ℝ) (hε : 0 < ε) :
      limsup (fun n => (μ.map (Y n)) F) atTop ≤
        (ν.map Z) (Metric.cthickening ε F) := by
    have hmono : (fun n => (μ.map (Y n)) F) ≤ᶠ[atTop]
        (fun n => (μ.map (X n)) (Metric.cthickening ε F)) := by
      filter_upwards [hclose ε hε] with n hn
      rw [Measure.map_apply_of_aemeasurable (hY n) hF.measurableSet,
        Measure.map_apply_of_aemeasurable (hX.forall_aemeasurable n)
          Metric.isClosed_cthickening.measurableSet]
      apply measure_mono_ae
      filter_upwards [hn] with ω hω
      intro hωF
      exact Metric.mem_cthickening_of_dist_le (X n ω) (Y n ω) ε F hωF hω.le
    exact (limsup_le_limsup hmono).trans
      (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hX.tendsto
        Metric.isClosed_cthickening)
  have hlim := tendsto_measure_cthickening_of_isClosed
    (μ := ν.map Z) (s := F) ⟨1, zero_lt_one, measure_ne_top _ _⟩ hF
  change limsup (fun n => (μ.map (Y n)) F) atTop ≤ (ν.map Z) F
  apply ge_of_tendsto (hlim.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  exact eventually_nhdsWithin_of_forall (fun ε hε => hb ε hε)

/-- Helper toward Lemma 4.11: compact intervals give a countable basis for the path uniformity. -/
local instance instCountablyGeneratedU_Lemma411StepTransfer :
    IsCountablyGenerated (𝓤 (UniformOnFun ℝ≥0 (ℝ × ℝ) {K | IsCompact K})) := by
  apply UniformOnFun.isCountablyGenerated_uniformity (t := fun k : ℕ => Icc 0 (k : ℝ≥0))
  · intro k
    exact isCompact_Icc
  · intro i j hij
    exact Icc_subset_Icc_right (by exact_mod_cast hij)
  · intro K hK
    obtain ⟨T, hT⟩ := hK.bddAbove
    obtain ⟨k, hk⟩ := exists_nat_gt T
    exact ⟨k, fun t ht => ⟨zero_le, (hT ht).trans hk.le⟩⟩

/-- Helper toward Lemma 4.11: a pseudometric compatible with the original path uniformity. -/
noncomputable local instance instPseudoMetricU_Lemma411StepTransfer :
    PseudoMetricSpace (UniformOnFun ℝ≥0 (ℝ × ℝ) {K | IsCompact K}) :=
  UniformSpace.pseudoMetricSpace _

/-- Helper toward Lemma 4.11: converging together in the common path space,
with closeness tested uniformly on compact sets and no separability assumption. -/
theorem tendstoInDistribution_of_compact_ae_close
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ω') [IsProbabilityMeasure ν]
    (X Y : ℕ → Ω → UniformOnFun ℝ≥0 (ℝ × ℝ) {K | IsCompact K})
    (Z : Ω' → UniformOnFun ℝ≥0 (ℝ × ℝ) {K | IsCompact K})
    (hX : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    (hY : ∀ n, AEMeasurable (Y n) μ)
    (hclose : ∀ K : Set ℝ≥0, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, ∀ t ∈ K,
        dist (UniformOnFun.toFun {K | IsCompact K} (X n ω) t)
          (UniformOnFun.toFun {K | IsCompact K} (Y n ω) t) < ε) :
    TendstoInDistribution Y atTop Z (fun _ => μ) ν := by
  apply tendstoInDistribution_of_eventually_ae_dist_lt μ ν X Y Z hX hY
  intro ε hε
  have hV : {p : (UniformOnFun ℝ≥0 (ℝ × ℝ) {K | IsCompact K}) ×
      (UniformOnFun ℝ≥0 (ℝ × ℝ) {K | IsCompact K}) | dist p.1 p.2 < ε} ∈ 𝓤 _ :=
    Metric.dist_mem_uniformity hε
  have hB := UniformOnFun.hasBasis_uniformity_of_basis ℝ≥0 (ℝ × ℝ)
    {K | IsCompact K} ⟨∅, isCompact_empty⟩
    (fun K hK L hL => ⟨K ∪ L, hK.union hL, subset_union_left, subset_union_right⟩)
    Metric.uniformity_basis_dist
  obtain ⟨⟨K, δ⟩, ⟨hK, hδ⟩, hsub⟩ := hB.mem_iff.mp hV
  filter_upwards [hclose K hK δ hδ] with n hn
  filter_upwards [hn] with ω hω
  exact hsub (a := (X n ω, Y n ω)) hω

/-- Helper toward Lemma 4.11: continuous path spaces carry their Borel measurable spaces. -/
local instance instMeasurableC_Lemma411StepTransfer
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] :
    MeasurableSpace C(A, B) := borel _
/-- Helper toward Lemma 4.11: the continuous path measurable structures are Borel. -/
local instance instBorelC_Lemma411StepTransfer
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] :
    BorelSpace C(A, B) := ⟨rfl⟩

/-- Helper toward Lemma 4.11: the literal floor process converges in law
uniformly on compact sets to the source-conditioned Brownian process. -/
theorem lemma411_conditioned_step_functional_limit
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄) :
    TendstoInDistribution
      (fun n z => (UniformOnFun.ofFun {K | IsCompact K} (diffusiveStep n z) :
        UniformOnFun ℝ≥0 (ℝ × ℝ) {K | IsCompact K})) atTop
      (fun p => UniformOnFun.ofFun {K | IsCompact K} (conditionedBrownianPath p))
      (fun _ => conditionedVectorPathLaw 0 0) W₄ := by
  have hX := (Lemma411Final.lemma411_conditioned_interpolation_functional_limit W₄ hB hI).continuous_comp
    continuous_continuousPath_toUniformOnFun
  apply tendstoInDistribution_of_compact_ae_close (conditionedVectorPathLaw 0 0) W₄
    (fun n z => UniformOnFun.ofFun {K | IsCompact K} (diffusiveInterpolation n z))
    (fun n z => UniformOnFun.ofFun {K | IsCompact K} (diffusiveStep n z))
    (fun p => UniformOnFun.ofFun {K | IsCompact K} (conditionedBrownianPath p)) hX
    (fun n => (measurable_diffusiveStep_uniformOnFun n).aemeasurable)
  intro K hK ε hε
  filter_upwards [conditionedVectorPathLaw_eventually_ae_step_interpolation_close K hK ε hε]
    with n hn
  filter_upwards [hn] with z hz
  intro t ht
  exact (dist_comm _ _).trans_lt (hz t ht)

end DirectedDistances.RandomWalk.Lemma411StepTransfer
