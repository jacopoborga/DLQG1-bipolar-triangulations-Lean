module

public import DirectedDistances.Probability.MomentTightnessContinuous
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Helpers toward Lemma 4.11: compact containment for continuous paths.
These are supporting results for target C recorded in
`MomentTightnessContinuous.lean`, not a claim of the conditioned invariance principle. -/

@[expose] public section

namespace DirectedDistances.Probability

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal

/-- Helper toward Lemma 4.11: paths starting at zero and obeying a prescribed
sequence of closed modulus constraints on a compact time interval. -/
def zeroStartModulusSet {E : Type*} [NormedAddCommGroup E]
    (T : ℝ≥0) (δ η : ℕ → ℝ) : Set C(Icc (0 : ℝ≥0) T, E) :=
  {f | f ⟨0, bot_le, bot_le⟩ = 0 ∧
    ∀ j (s t : Icc (0 : ℝ≥0) T), dist s t ≤ δ j → dist (f s) (f t) ≤ η j}

/-- Helper toward Lemma 4.11: closed modulus constraints define a closed set
of continuous paths, including the constraint at time zero. -/
theorem isClosed_zeroStartModulusSet {E : Type*} [NormedAddCommGroup E]
    (T : ℝ≥0) (δ η : ℕ → ℝ) : IsClosed (zeroStartModulusSet (E := E) T δ η) := by
  unfold zeroStartModulusSet
  simp only [ofPred_and, ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_eq (continuous_eval_const _) continuous_const
  · exact isClosed_iInter fun j => isClosed_iInter fun s => isClosed_iInter fun t =>
      isClosed_iInter fun _ => isClosed_le
        ((continuous_eval_const s).dist (continuous_eval_const t)) continuous_const

/-- Helper toward Lemma 4.11: positive scales and moduli tending to zero
make the associated family of paths equicontinuous. -/
theorem equicontinuous_zeroStartModulusSet {E : Type*} [NormedAddCommGroup E]
    (T : ℝ≥0) (δ η : ℕ → ℝ) (hδ : ∀ j, 0 < δ j)
    (hη : Tendsto η atTop (𝓝 0)) :
    Equicontinuous (fun f : zeroStartModulusSet (E := E) T δ η =>
      (f.val : Icc (0 : ℝ≥0) T → E)) := by
  intro s
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨j, hj⟩ := (hη.eventually (gt_mem_nhds hε)).exists
  exact ⟨δ j, hδ j, fun t ht f =>
    ((f.property.2 j s t (by simpa only [dist_comm] using ht.le))).trans_lt hj⟩

/-- Helper toward Lemma 4.11: a fixed positive-scale modulus and a zero
start bound every path value by a common finite constant. -/
theorem exists_bound_zeroStartModulusSet {E : Type*} [NormedAddCommGroup E]
    (T : ℝ≥0) (δ η : ℕ → ℝ) (hδ : 0 < δ 0) :
    ∃ B : ℝ, ∀ f ∈ zeroStartModulusSet (E := E) T δ η,
      ∀ t, ‖f t‖ ≤ B := by
  obtain ⟨M, hM⟩ := exists_nat_gt ((T : ℝ) / δ 0)
  have hTM : (T : ℝ) ≤ (M : ℝ) * δ 0 :=
    ((div_lt_iff₀ hδ).mp hM).le
  refine ⟨(M : ℝ) * η 0, ?_⟩
  intro f hf t
  let p (k : ℕ) : Icc (0 : ℝ≥0) T :=
    ⟨⟨min ((k : ℝ) * δ 0) (t.val : ℝ),
      le_min (mul_nonneg (Nat.cast_nonneg _) hδ.le) t.val.property⟩, bot_le,
      (min_le_right _ _).trans (show (t.val : ℝ) ≤ T from t.property.2)⟩
  have hp0 : p 0 = ⟨0, bot_le, bot_le⟩ := by
    apply Subtype.ext
    apply NNReal.eq
    change min (((0 : ℕ) : ℝ) * δ 0) (t.val : ℝ) = 0
    rw [Nat.cast_zero, zero_mul]
    exact min_eq_left t.val.property
  have hpM : p M = t := by
    apply Subtype.ext
    apply NNReal.eq
    change min ((M : ℝ) * δ 0) (t.val : ℝ) = (t.val : ℝ)
    exact min_eq_right ((show (t.val : ℝ) ≤ (T : ℝ) from t.property.2).trans hTM)
  have hstep (k : ℕ) : dist (p k) (p (k + 1)) ≤ δ 0 := by
    change |min ((k : ℝ) * δ 0) (t.val : ℝ) -
      min (((k + 1 : ℕ) : ℝ) * δ 0) (t.val : ℝ)| ≤ δ 0
    rw [Nat.cast_add, Nat.cast_one]
    rw [abs_le]
    simp only [min_def]
    split_ifs <;> constructor <;> linarith
  have hind (k : ℕ) : dist (f (p 0)) (f (p k)) ≤ (k : ℝ) * η 0 := by
    induction k with
    | zero => simp only [dist_self, Nat.cast_zero, zero_mul, le_refl]
    | succ k ih =>
      have hh := hf.2 0 (p k) (p (k + 1)) (hstep k)
      have ht := dist_triangle (f (p 0)) (f (p k)) (f (p (k + 1)))
      push_cast
      linarith only [ih, hh, ht]
  have hh := hind M
  rw [hp0, hf.1, hpM, dist_zero_left] at hh
  exact hh

/-- Helper toward Lemma 4.11: in a finite-dimensional real normed space,
the closed family of zero-start paths with vanishing prescribed moduli is compact. -/
theorem isCompact_zeroStartModulusSet {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : ℝ≥0) (δ η : ℕ → ℝ) (hδ : ∀ j, 0 < δ j)
    (hη : Tendsto η atTop (𝓝 0)) :
    IsCompact (zeroStartModulusSet (E := E) T δ η) := by
  have heq := equicontinuous_zeroStartModulusSet (E := E) T δ η hδ hη
  obtain ⟨B, hB⟩ := exists_bound_zeroStartModulusSet (E := E) T δ η (hδ 0)
  let : T2Space (UniformOnFun (Icc (0 : ℝ≥0) T) E {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      apply eq_univ_iff_forall.mpr
      intro t
      exact mem_sUnion_of_mem (mem_singleton t) isCompact_singleton)
  have hc : IsCompact (closure (zeroStartModulusSet (E := E) T δ η)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun f : C(Icc (0 : ℝ≥0) T, E) => (f : _ → E))
      (𝔖 := {K | IsCompact K}) (fun _ => id)
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · intro K _
      exact heq.equicontinuousOn K
    · intro K _ t _
      refine ⟨Metric.closedBall (0 : E) B, isCompact_closedBall _ _, ?_⟩
      intro f hf
      simpa only [Metric.mem_closedBall, dist_zero_right] using hB f hf t
  rwa [(isClosed_zeroStartModulusSet (E := E) T δ η).closure_eq] at hc

/-- Helper toward Lemma 4.11: a continuous zero-start family in a finite-dimensional
real normed space with one common fourth-increment moment constant has tight laws
on each compact time interval (target C of `MomentTightnessContinuous.lean`). -/
theorem isTightMeasureSet_restrict_of_norm_fourth_moment
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → C(ℝ≥0, E)) (C : ℝ) (hC : 0 ≤ C) (T : ℝ≥0)
    (hzero : ∀ n ω, X n ω 0 = 0)
    (hint : ∀ n (s t : ℝ≥0), Integrable (fun ω => ‖X n ω t - X n ω s‖ ^ 4) μ)
    (hmom : ∀ n (s t : ℝ≥0), s ≤ t →
      (∫ ω, ‖X n ω t - X n ω s‖ ^ 4 ∂μ) ≤ C * ((t : ℝ) - (s : ℝ)) ^ 2) :
    letI : MeasurableSpace C(Icc (0 : ℝ≥0) T, E) := borel _
    let R : ℕ → Ω → C(Icc (0 : ℝ≥0) T, E) :=
      fun n ω => (X n ω).comp ⟨Subtype.val, continuous_subtype_val⟩
    (∀ n, Measurable (R n)) →
      IsTightMeasureSet (range (fun n => Measure.map (R n) μ)) := by
  let : MeasurableSpace C(Icc (0 : ℝ≥0) T, E) := borel _
  let : BorelSpace C(Icc (0 : ℝ≥0) T, E) := ⟨rfl⟩
  let R : ℕ → Ω → C(Icc (0 : ℝ≥0) T, E) :=
    fun n ω => (X n ω).comp ⟨Subtype.val, continuous_subtype_val⟩
  change (∀ n, Measurable (R n)) →
    IsTightMeasureSet (range (fun n => Measure.map (R n) μ))
  intro hR
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_ge (T : ℝ)
  let η : ℕ → ℝ := fun j => (1 / 2 : ℝ) ^ j
  let e : ℕ → ℝ≥0∞ := fun j => ε * (2⁻¹ : ℝ≥0∞) ^ (j + 1)
  have he (j : ℕ) : 0 < e j := by
    dsimp [e]
    exact ENNReal.mul_pos_iff.mpr ⟨hε,
      ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofNat_ne_top) _⟩
  have hηpos (j : ℕ) : 0 < η j := by dsimp [η]; positivity
  have hscale (j : ℕ) := uniform_modulus_of_norm_fourth_moment μ X N C hC
    hint hmom (η j) (hηpos j) (e j) (he j)
  choose δ hδ htail using hscale
  have hη : Tendsto η atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  let S := zeroStartModulusSet (E := E) T δ η
  have hS : IsCompact S := isCompact_zeroStartModulusSet T δ η hδ hη
  refine ⟨S, hS, ?_⟩
  rintro ν ⟨n, rfl⟩
  rw [Measure.map_apply (hR n) hS.measurableSet.compl]
  let bad (j : ℕ) : Set Ω := {ω | ∃ s t : ℝ≥0,
    (s : ℝ) ≤ N ∧ (t : ℝ) ≤ N ∧ dist s t ≤ δ j ∧
      η j ≤ ‖X n ω t - X n ω s‖}
  have hsub : R n ⁻¹' Sᶜ ⊆ ⋃ j, bad j := by
    intro ω hω
    by_contra hn
    apply hω
    refine ⟨hzero n ω, ?_⟩
    intro j s t hst
    change dist (X n ω s.val) (X n ω t.val) ≤ η j
    rw [dist_eq_norm']
    apply le_of_lt
    apply lt_of_not_ge
    intro hlarge
    apply hn
    exact mem_iUnion.mpr ⟨j, s.val, t.val,
      (show (s.val : ℝ) ≤ T from s.property.2).trans hN,
      (show (t.val : ℝ) ≤ T from t.property.2).trans hN, hst, hlarge⟩
  calc
    μ (R n ⁻¹' Sᶜ) ≤ μ (⋃ j, bad j) := measure_mono hsub
    _ ≤ ∑' j, μ (bad j) := measure_iUnion_le _
    _ ≤ ∑' j, e j := tsum_le_tsum (fun j => htail j n)
    _ = ε := by
      dsimp [e]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
      norm_num
      rw [ENNReal.inv_mul_cancel (by norm_num) ENNReal.ofNat_ne_top, mul_one]

end DirectedDistances.Probability
