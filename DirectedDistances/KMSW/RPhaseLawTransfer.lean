/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.QuadrantLaws
public import DirectedDistances.KMSW.MeasurableCutEvents
public import DirectedDistances.KMSW.MapCutVertices
public import DirectedDistances.KMSW.FiniteAvoidanceWindow
public import DirectedDistances.KMSW.CutSeparationAE
public import DirectedDistances.KMSW.DirectedContainLaw1
public import DirectedDistances.RandomWalk.SecondCoordinateUnbounded

/-! # Transfer of UIQBOT code facts to the R-phase KMSW code sequence

This file transfers measurable almost-sure code events from the Pitman-flipped
iid code realization to the KMSW image of the R-phase codes. Identifying that
image with `M̂_{τ_k,∞}` inside `M_{0,∞}` is `lem-quad-kmsw` and remains separate

`map_phaseSplit_pitmanProcesses` is a path-process law: its carrier is the
product of two path spaces `ℕ → ℤ × ℤ`, with the first coordinate the vector
Pitman process of the R-phase stream and the second the rotated R-Pitman
process of the other stream. The code-sequence law used below follows from the
stronger code-level splitter law `map_phaseSplit_iidCodeMeasure`. -/

public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk

/-- The R-phase code sequence with the fixed time-zero coordinate removed.
This is the stage-code indexing of the first component of `phaseSplit`. -/
@[expose] noncomputable def rPhaseCodeSequence (ω : ℕ → Fin 3) : ℕ → Fin 3 :=
  fun i => (phaseSplit ω).1 (i + 1)

/-- The R-phase code sequence after the Pitman flip, which is the code input -/
@[expose] noncomputable def rCodeSequence (ω : ℕ → Fin 3) : ℕ → Fin 3 :=
  pitmanCode (rPhaseCodeSequence ω)

/-- Measurability of the R-phase stage-code sequence. -/
theorem measurable_rPhaseCodeSequence : Measurable rPhaseCodeSequence := by
  apply Measurable.of_eval
  intro i
  exact (measurable_pi_apply (i + 1)).comp
    (measurable_fst.comp measurable_phaseSplit)

/-- Measurability of the Pitman-flipped R-phase code sequence. -/
theorem measurable_rCodeSequence : Measurable rCodeSequence :=
  measurable_pitmanCode.comp measurable_rPhaseCodeSequence

private def codeTail (ω : ℕ → Fin 3) : ℕ → Fin 3 := fun i => ω (i + 1)

private def firstCodeTail (ab : (ℕ → Fin 3) × (ℕ → Fin 3)) : ℕ → Fin 3 :=
  fun i => ab.1 (i + 1)

private theorem measurable_codeTail : Measurable codeTail := by
  apply Measurable.of_eval
  intro i
  exact measurable_pi_apply (i + 1)

private theorem measurable_firstCodeTail : Measurable firstCodeTail := by
  apply Measurable.of_eval
  intro i
  exact (measurable_pi_apply (i + 1)).comp measurable_fst

/-- The R-phase stage codes have the law of the iid source codes after their
fixed time-zero coordinate (`lem-quadrant-walk`, -/
theorem map_rPhaseCodeSequence :
    iidCodeMeasure.map rPhaseCodeSequence =
      iidCodeMeasure.map (fun ω => fun i => ω (i + 1)) := by
  calc
    iidCodeMeasure.map rPhaseCodeSequence =
        (iidCodeMeasure.map phaseSplit).map firstCodeTail := by
          rw [Measure.map_map measurable_firstCodeTail measurable_phaseSplit]
          rfl
    _ = (iidCodeMeasure.prod iidCodeMeasure).map firstCodeTail := by
          rw [map_phaseSplit_iidCodeMeasure]
    _ = iidCodeMeasure.map (fun ω => fun i => ω (i + 1)) := by
          calc
            (iidCodeMeasure.prod iidCodeMeasure).map firstCodeTail =
                ((iidCodeMeasure.prod iidCodeMeasure).map Prod.fst).map codeTail := by
                  rw [Measure.map_map measurable_codeTail measurable_fst]
                  rfl
            _ = iidCodeMeasure.map codeTail := by simp

/-- The Pitman-flipped R-phase code sequence has exactly the law of the
Pitman-flipped iid code sequence `pitmanCode (fun i => ω (i+1))`. -/
theorem map_rCodeSequence :
    iidCodeMeasure.map rCodeSequence =
      iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) := by
  calc
    iidCodeMeasure.map rCodeSequence =
        (iidCodeMeasure.map rPhaseCodeSequence).map pitmanCode := by
          rw [Measure.map_map measurable_pitmanCode measurable_rPhaseCodeSequence]
          rfl
    _ = (iidCodeMeasure.map codeTail).map pitmanCode :=
          congrArg (fun μ => μ.map pitmanCode) map_rPhaseCodeSequence
    _ = iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) := by
          rw [Measure.map_map measurable_pitmanCode measurable_codeTail]
          rfl

private theorem ae_mem_of_map_eq
    {F G : (ℕ → Fin 3) → (ℕ → Fin 3)}
    (hF : Measurable F) (hG : Measurable G)
    (hmap : iidCodeMeasure.map F = iidCodeMeasure.map G)
    {E : Set (ℕ → Fin 3)} (hE : MeasurableSet E)
    (hfull : iidCodeMeasure {ω | G ω ∈ E} = 1) :
    ∀ᵐ ω ∂iidCodeMeasure, F ω ∈ E := by
  have hmeasure : iidCodeMeasure {ω | F ω ∈ E} = 1 := by
    change iidCodeMeasure (F ⁻¹' E) = 1
    rw [← Measure.map_apply hF hE, hmap, Measure.map_apply hG hE]
    exact hfull
  exact (mem_ae_iff_prob_eq_one (hF hE)).2 hmeasure

private theorem measurable_L_value (n : ℕ) :
    Measurable (fun w : ℕ → Fin 3 => L w n) := by
  unfold L
  exact (Finset.range n).measurable_sum (fun i _ =>
    (measurable_of_countable (fun c : Fin 3 =>
      (lazyTwoDimensionalStep c).1)).comp (measurable_pi_apply i))

private theorem measurable_R_value (n : ℕ) :
    Measurable (fun w : ℕ → Fin 3 => R w n) := by
  unfold R
  exact (Finset.range n).measurable_sum (fun i _ =>
    (measurable_of_countable (fun c : Fin 3 =>
      (lazyTwoDimensionalStep c).2)).comp (measurable_pi_apply i))

private theorem measurableSet_cutSeparationRecord (n : ℕ) :
    MeasurableSet {w : ℕ → Fin 3 |
      (∀ j < n, R w n ≤ R w j - 1) ∧
        ∀ j, n ≤ j → L w n ≤ L w j} := by
  have hR : MeasurableSet {w : ℕ → Fin 3 | ∀ j < n, R w n ≤ R w j - 1} := by
    have hset : {w : ℕ → Fin 3 | ∀ j < n, R w n ≤ R w j - 1} =
        ⋂ j : ℕ, ⋂ (_ : j < n), {w : ℕ → Fin 3 | R w n ≤ R w j - 1} := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hset]
    exact MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ =>
      measurableSet_le (measurable_R_value n) ((measurable_R_value j).sub_const 1)))
  have hL : MeasurableSet {w : ℕ → Fin 3 | ∀ j, n ≤ j → L w n ≤ L w j} := by
    have hset : {w : ℕ → Fin 3 | ∀ j, n ≤ j → L w n ≤ L w j} =
        ⋂ j : ℕ, ⋂ (_ : n ≤ j), {w : ℕ → Fin 3 | L w n ≤ L w j} := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hset]
    exact MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ =>
      measurableSet_le (measurable_L_value n) (measurable_L_value j)))
  exact hR.inter hL

private theorem infinite_iff_forall_exists_ge (s : Set ℕ) :
    s.Infinite ↔ ∀ N, ∃ n, N ≤ n ∧ n ∈ s := by
  rw [Set.infinite_iff_exists_gt]
  constructor
  · intro h N
    obtain ⟨n, hmem, hn⟩ := h N
    exact ⟨n, Nat.le_of_lt hn, hmem⟩
  · intro h N
    obtain ⟨n, hNn, hmem⟩ := h (N + 1)
    exact ⟨n, hmem, by omega⟩

private theorem measurableSet_infinite_cutSeparationRecords :
    MeasurableSet {w : ℕ → Fin 3 |
      {n : ℕ | (∀ j < n, R w n ≤ R w j - 1) ∧
        ∀ j, n ≤ j → L w n ≤ L w j}.Infinite} := by
  have hset : {w : ℕ → Fin 3 |
      {n : ℕ | (∀ j < n, R w n ≤ R w j - 1) ∧
        ∀ j, n ≤ j → L w n ≤ L w j}.Infinite} =
      ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n),
        {w : ℕ → Fin 3 |
          (∀ j < n, R w n ≤ R w j - 1) ∧
            ∀ j, n ≤ j → L w n ≤ L w j} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, exists_prop]
    exact infinite_iff_forall_exists_ge _
  rw [hset]
  exact MeasurableSet.iInter (fun N => MeasurableSet.iUnion (fun n =>
    MeasurableSet.iUnion (fun _ => measurableSet_cutSeparationRecord n)))

/-- Almost surely every finite family of allocated vertices of the R-phase
KMSW map has infinitely many common finite-avoidance vertices. Measurability
is reduced to the countable record-barrier event and unboundedness of `R`;
the finite-family conclusion is then deterministic -/
theorem ae_rCodeSequence_infinite_common_finiteAvoidance_any_allocated :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∀ A : Finset ℕ,
        (∀ a ∈ A, ∃ N,
          a < (kmswStage (rCodeSequence ω) N).nextVertex) →
          {z : PresentVertex (rCodeSequence ω) | ∀ a ∈ A,
            FiniteAvoidance (⟨a⟩ : PresentVertex (rCodeSequence ω)) z}.Infinite := by
  let E : Set (ℕ → Fin 3) := {w |
    {n : ℕ | (∀ j < n, R w n ≤ R w j - 1) ∧
      ∀ j, n ≤ j → L w n ≤ L w j}.Infinite ∧
    ∀ a : ℤ, ∃ n, R w n ≤ a}
  have hE : MeasurableSet E := by
    change MeasurableSet
      ({w | {n : ℕ | (∀ j < n, R w n ≤ R w j - 1) ∧
        ∀ j, n ≤ j → L w n ≤ L w j}.Infinite} ∩
        {w | ∀ a : ℤ, ∃ n, R w n ≤ a})
    exact measurableSet_infinite_cutSeparationRecords.inter
      measurableSet_R_unbounded_below
  have hsource : ∀ᵐ ω ∂iidCodeMeasure,
      pitmanCode (fun i => ω (i + 1)) ∈ E := by
    filter_upwards [pitmanCodes_ae_infinite_cutSeparation_records,
      RandomWalk.pitmanCodes_ae_R_unbounded_below] with ω hrecords hR
    dsimp only at hrecords
    have hR' : ∀ a : ℤ,
        ∃ n, R (pitmanCode (fun i => ω (i + 1))) n ≤ a := by
      intro a
      obtain ⟨n, hn⟩ := hR a
      exact ⟨n, by rw [kmsw_R_eq]; exact hn⟩
    exact ⟨hrecords, hR'⟩
  have hfull : iidCodeMeasure
      {ω | pitmanCode (fun i => ω (i + 1)) ∈ E} = 1 := by
    exact (mem_ae_iff_prob_eq_one (measurableSet_preimage_pitmanCode_shift hE)).1 hsource
  have hdest := ae_mem_of_map_eq measurable_rCodeSequence measurable_pitmanCode_shift
    map_rCodeSequence hE hfull
  filter_upwards [hdest] with ω hω
  dsimp only [E, Set.mem_ofPred_eq] at hω
  intro A halloc
  exact finiteAvoidance_infinite_common_of_records hω.2 hω.1 A halloc

/-- At positive indices, `codeShift` reads the future source code with the
time convention `ω (t + i + 1)` used in `DirectedContainLaw1`. -/
theorem codeShift_succ (ω : ℕ → Fin 3) (t i : ℕ) :
    RandomWalk.codeShift t ω (i + 1) = ω (t + i + 1) := by
  simp [RandomWalk.codeShift, Nat.add_assoc]

/-- Any measurable full-measure Pitman code event transfers to the R-phase
codes of the future code sequence at the second-coordinate hit. This uses the
code-functional form of the future-code law underlying the stage-process equality in
`DirectedContainLaw1.iidCodeMeasure_map_stageProcess_future_at_rightHit` -/
theorem ae_future_rCodeSequence_mem_of_pitmanCodeShift_full_at_rightHit
    (k : ℤ) (_hk : 1 ≤ k)
    {E : Set (ℕ → Fin 3)} (hE : MeasurableSet E)
    (hfull : iidCodeMeasure
      {ω | pitmanCode (fun i => ω (i + 1)) ∈ E} = 1) :
    ∀ᵐ ω ∂iidCodeMeasure,
      rCodeSequence (RandomWalk.codeShift
        (RandomWalk.codeSndFirstHit (-k) ω).toNat ω) ∈ E := by
  let future : (ℕ → Fin 3) → (ℕ → Fin 3) := fun ω =>
    RandomWalk.codeShift (RandomWalk.codeSndFirstHit (-k) ω).toNat ω
  have hfuture : Measurable future :=
    RandomWalk.measurable_codeShift_toNat _
      (RandomWalk.measurableSet_codePast_codeSndFirstHit_eq (-k))
  have hF : Measurable (fun ω => rCodeSequence (future ω)) :=
    measurable_rCodeSequence.comp hfuture
  have hmap : iidCodeMeasure.map (fun ω => rCodeSequence (future ω)) =
      iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) := by
    calc
      iidCodeMeasure.map (fun ω => rCodeSequence (future ω)) =
          iidCodeMeasure.map rCodeSequence := by
            exact RandomWalk.map_comp_codeShift_codeSndFirstHit (-k)
              (F := rCodeSequence) measurable_rCodeSequence
      _ = iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) :=
            map_rCodeSequence
  have hresult := ae_mem_of_map_eq hF measurable_pitmanCode_shift hmap hE hfull
  simpa [future] using hresult

/-- Any measurable full-measure Pitman code event transfers to the R-phase
codes of the future code sequence at the first-coordinate hit. This uses the
code-functional form of the future-code law underlying the left-hit stage-process equality in
`DirectedContainLaw1.iidCodeMeasure_map_stageProcess_future_at_leftHit` -/
theorem ae_future_rCodeSequence_mem_of_pitmanCodeShift_full_at_leftHit
    (k : ℤ) (_hk : k ≤ -1)
    {E : Set (ℕ → Fin 3)} (hE : MeasurableSet E)
    (hfull : iidCodeMeasure
      {ω | pitmanCode (fun i => ω (i + 1)) ∈ E} = 1) :
    ∀ᵐ ω ∂iidCodeMeasure,
      rCodeSequence (RandomWalk.codeShift
        (RandomWalk.codeFstFirstHit k ω).toNat ω) ∈ E := by
  let future : (ℕ → Fin 3) → (ℕ → Fin 3) := fun ω =>
    RandomWalk.codeShift (RandomWalk.codeFstFirstHit k ω).toNat ω
  have hfuture : Measurable future :=
    RandomWalk.measurable_codeShift_toNat _
      (RandomWalk.measurableSet_codePast_codeFstFirstHit_eq k)
  have hF : Measurable (fun ω => rCodeSequence (future ω)) :=
    measurable_rCodeSequence.comp hfuture
  have hmap : iidCodeMeasure.map (fun ω => rCodeSequence (future ω)) =
      iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) := by
    calc
      iidCodeMeasure.map (fun ω => rCodeSequence (future ω)) =
          iidCodeMeasure.map rCodeSequence := by
            exact RandomWalk.map_comp_codeShift_codeFstFirstHit k
              (F := rCodeSequence) measurable_rCodeSequence
      _ = iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) :=
            map_rCodeSequence
  have hresult := ae_mem_of_map_eq hF measurable_pitmanCode_shift hmap hE hfull
  simpa [future] using hresult

private theorem ae_future_rCodeSequence_properties_and_window
    {F : (ℕ → Fin 3) → (ℕ → Fin 3)} (hF : Measurable F)
    (hmap : iidCodeMeasure.map (fun ω => rCodeSequence (F ω)) =
      iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1)))) :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∃ hfin : ∀ v, {e : ℕ | ∃ n,
        e < (kmswStage (rCodeSequence (F ω)) n).nextEdge ∧
          ((kmswStage (rCodeSequence (F ω)) n).west e = v ∨
            (kmswStage (rCodeSequence (F ω)) n).east e = v)}.Finite,
        Tendsto (L (rCodeSequence (F ω))) atTop atTop ∧
        (∀ a : ℤ, ∃ n, R (rCodeSequence (F ω)) n ≤ a) ∧
        (∀ j, 0 ≤ L (rCodeSequence (F ω)) j) ∧
        {v : ℕ | mapCutVertex (rCodeSequence (F ω)) hfin v}.Infinite ∧
        ∀ A : Finset ℕ,
          (∀ a ∈ A, ∃ N,
            a < (kmswStage (rCodeSequence (F ω)) N).nextVertex) →
          {z : PresentVertex (rCodeSequence (F ω)) | ∀ a ∈ A,
            FiniteAvoidance (⟨a⟩ : PresentVertex (rCodeSequence (F ω))) z}.Infinite := by
  let E : Set (ℕ → Fin 3) := {w |
    (∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) ∧
    Tendsto (L w) atTop atTop ∧
    (∀ a : ℤ, ∃ n, R w n ≤ a) ∧
    (∀ j, 0 ≤ L w j) ∧
    {v : ℕ | IsCutVertex w v}.Infinite ∧
    {n : ℕ | (∀ j < n, R w n ≤ R w j - 1) ∧
      ∀ j, n ≤ j → L w n ≤ L w j}.Infinite}
  have hE : MeasurableSet E := by
    change MeasurableSet
      ({w | ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite} ∩
      ({w | Tendsto (L w) atTop atTop} ∩
      ({w | ∀ a : ℤ, ∃ n, R w n ≤ a} ∩
      ({w | ∀ j, 0 ≤ L w j} ∩
      ({w | {v : ℕ | IsCutVertex w v}.Infinite} ∩
      {w | {n : ℕ | (∀ j < n, R w n ≤ R w j - 1) ∧
        ∀ j, n ≤ j → L w n ≤ L w j}.Infinite})))))
    exact measurableSet_finiteIncidence.inter
      (measurableSet_tendsto_L.inter
        (measurableSet_R_unbounded_below.inter
          (measurableSet_L_nonneg.inter
            (measurableSet_infinite_cutVertices.inter
              measurableSet_infinite_cutSeparationRecords))))
  have hsource : ∀ᵐ ω ∂iidCodeMeasure,
      pitmanCode (fun i => ω (i + 1)) ∈ E := by
    filter_upwards [pitmanCodes_ae_infinite_mapCutVertices,
      pitmanCodes_ae_infinite_cutSeparation_records] with ω hmapAE hrecords
    dsimp only at hmapAE hrecords
    obtain ⟨hfin, hT, hR, hL0, hmapInf⟩ := hmapAE
    have hset : {v : ℕ | mapCutVertex (pitmanCode (fun i => ω (i + 1))) hfin v} =
        {v : ℕ | IsCutVertex (pitmanCode (fun i => ω (i + 1))) v} := by
      ext v
      exact mapCutVertex_iff _ hfin hT hR hL0 v
    have hIs : {v : ℕ | IsCutVertex (pitmanCode (fun i => ω (i + 1))) v}.Infinite := by
      rw [← hset]
      exact hmapInf
    exact ⟨hfin, hT, hR, hL0, hIs, hrecords⟩
  have hfull : iidCodeMeasure
      {ω | pitmanCode (fun i => ω (i + 1)) ∈ E} = 1 := by
    exact (mem_ae_iff_prob_eq_one (measurableSet_preimage_pitmanCode_shift hE)).1 hsource
  have hCF : Measurable (fun ω => rCodeSequence (F ω)) :=
    measurable_rCodeSequence.comp hF
  have hdest := ae_mem_of_map_eq hCF measurable_pitmanCode_shift hmap hE hfull
  filter_upwards [hdest] with ω hω
  dsimp only [E, Set.mem_ofPred_eq] at hω
  rcases hω with ⟨hfin, hT, hR, hL0, hIs, hrecords⟩
  have hcutset : {v : ℕ | mapCutVertex (rCodeSequence (F ω)) hfin v} =
      {v : ℕ | IsCutVertex (rCodeSequence (F ω)) v} := by
    ext v
    exact mapCutVertex_iff _ hfin hT hR hL0 v
  have hmapInf :
      {v : ℕ | mapCutVertex (rCodeSequence (F ω)) hfin v}.Infinite := by
    rw [hcutset]
    exact hIs
  refine ⟨hfin, hT, hR, hL0, hmapInf, ?_⟩
  intro A halloc
  exact finiteAvoidance_infinite_common_of_records hR hrecords A halloc

/-- At every fixed right-boundary hit `R = -k`, the future R-phase KMSW map
has finite incidence, nonnegative and divergent `L`, unbounded-below `R`,
infinitely many map cut vertices, and the finite-avoidance window for every
finite allocated family. This uses the future-code law in
the code-functional form underlying
`DirectedContainLaw1.iidCodeMeasure_map_stageProcess_future_at_rightHit`;
the identification with `M̂_{τ_k,∞}` is the separate `lem-quad-kmsw` step -/
theorem ae_rCodeSequence_properties_and_window_at_rightHit
    (k : ℤ) (_hk : 1 ≤ k) :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∃ hfin : ∀ v, {e : ℕ | ∃ n,
        e < (kmswStage (rCodeSequence
          (RandomWalk.codeShift (RandomWalk.codeSndFirstHit (-k) ω).toNat ω)) n).nextEdge ∧
          ((kmswStage (rCodeSequence
            (RandomWalk.codeShift (RandomWalk.codeSndFirstHit (-k) ω).toNat ω)) n).west e = v ∨
            (kmswStage (rCodeSequence
              (RandomWalk.codeShift (RandomWalk.codeSndFirstHit (-k) ω).toNat ω)) n).east e = v)}.Finite,
        Tendsto (L (rCodeSequence
          (RandomWalk.codeShift (RandomWalk.codeSndFirstHit (-k) ω).toNat ω))) atTop atTop ∧
        (∀ a : ℤ, ∃ n, R (rCodeSequence
          (RandomWalk.codeShift (RandomWalk.codeSndFirstHit (-k) ω).toNat ω)) n ≤ a) ∧
        (∀ j, 0 ≤ L (rCodeSequence
          (RandomWalk.codeShift (RandomWalk.codeSndFirstHit (-k) ω).toNat ω)) j) ∧
        {v : ℕ | mapCutVertex (rCodeSequence
          (RandomWalk.codeShift (RandomWalk.codeSndFirstHit (-k) ω).toNat ω)) hfin v}.Infinite ∧
        ∀ A : Finset ℕ,
          (∀ a ∈ A, ∃ N, a < (kmswStage (rCodeSequence
            (RandomWalk.codeShift (RandomWalk.codeSndFirstHit (-k) ω).toNat ω)) N).nextVertex) →
          {z : PresentVertex (rCodeSequence
            (RandomWalk.codeShift (RandomWalk.codeSndFirstHit (-k) ω).toNat ω)) |
              ∀ a ∈ A, FiniteAvoidance
                (⟨a⟩ : PresentVertex (rCodeSequence
                  (RandomWalk.codeShift (RandomWalk.codeSndFirstHit (-k) ω).toNat ω))) z}.Infinite := by
  let future : (ℕ → Fin 3) → (ℕ → Fin 3) := fun ω =>
    RandomWalk.codeShift (RandomWalk.codeSndFirstHit (-k) ω).toNat ω
  have hfuture : Measurable future :=
    RandomWalk.measurable_codeShift_toNat _
      (RandomWalk.measurableSet_codePast_codeSndFirstHit_eq (-k))
  have hmap : iidCodeMeasure.map (fun ω => rCodeSequence (future ω)) =
      iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) := by
    calc
      iidCodeMeasure.map (fun ω => rCodeSequence (future ω)) =
          iidCodeMeasure.map rCodeSequence := by
            exact RandomWalk.map_comp_codeShift_codeSndFirstHit (-k)
              (F := rCodeSequence) measurable_rCodeSequence
      _ = iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) :=
            map_rCodeSequence
  have h := ae_future_rCodeSequence_properties_and_window hfuture hmap
  simpa only [future] using h

/-- The same future R-phase code properties and all-family finite-avoidance
window hold at each fixed first-coordinate hit. This is the left-hit future
law of `DirectedContainLaw1` (`lem-directed-contain`, -/
theorem ae_rCodeSequence_properties_and_window_at_leftHit
    (k : ℤ) (_hk : k ≤ -1) :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∃ hfin : ∀ v, {e : ℕ | ∃ n,
        e < (kmswStage (rCodeSequence
          (RandomWalk.codeShift (RandomWalk.codeFstFirstHit k ω).toNat ω)) n).nextEdge ∧
          ((kmswStage (rCodeSequence
            (RandomWalk.codeShift (RandomWalk.codeFstFirstHit k ω).toNat ω)) n).west e = v ∨
            (kmswStage (rCodeSequence
              (RandomWalk.codeShift (RandomWalk.codeFstFirstHit k ω).toNat ω)) n).east e = v)}.Finite,
        Tendsto (L (rCodeSequence
          (RandomWalk.codeShift (RandomWalk.codeFstFirstHit k ω).toNat ω))) atTop atTop ∧
        (∀ a : ℤ, ∃ n, R (rCodeSequence
          (RandomWalk.codeShift (RandomWalk.codeFstFirstHit k ω).toNat ω)) n ≤ a) ∧
        (∀ j, 0 ≤ L (rCodeSequence
          (RandomWalk.codeShift (RandomWalk.codeFstFirstHit k ω).toNat ω)) j) ∧
        {v : ℕ | mapCutVertex (rCodeSequence
          (RandomWalk.codeShift (RandomWalk.codeFstFirstHit k ω).toNat ω)) hfin v}.Infinite ∧
        ∀ A : Finset ℕ,
          (∀ a ∈ A, ∃ N, a < (kmswStage (rCodeSequence
            (RandomWalk.codeShift (RandomWalk.codeFstFirstHit k ω).toNat ω)) N).nextVertex) →
          {z : PresentVertex (rCodeSequence
            (RandomWalk.codeShift (RandomWalk.codeFstFirstHit k ω).toNat ω)) |
              ∀ a ∈ A, FiniteAvoidance
                (⟨a⟩ : PresentVertex (rCodeSequence
                  (RandomWalk.codeShift (RandomWalk.codeFstFirstHit k ω).toNat ω))) z}.Infinite := by
  let future : (ℕ → Fin 3) → (ℕ → Fin 3) := fun ω =>
    RandomWalk.codeShift (RandomWalk.codeFstFirstHit k ω).toNat ω
  have hfuture : Measurable future :=
    RandomWalk.measurable_codeShift_toNat _
      (RandomWalk.measurableSet_codePast_codeFstFirstHit_eq k)
  have hmap : iidCodeMeasure.map (fun ω => rCodeSequence (future ω)) =
      iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) := by
    calc
      iidCodeMeasure.map (fun ω => rCodeSequence (future ω)) =
          iidCodeMeasure.map rCodeSequence := by
            exact RandomWalk.map_comp_codeShift_codeFstFirstHit k
              (F := rCodeSequence) measurable_rCodeSequence
      _ = iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) :=
            map_rCodeSequence
  have h := ae_future_rCodeSequence_properties_and_window hfuture hmap
  simpa only [future] using h

/-- A measurable code event of full measure for the Pitman-flipped iid
realization also holds almost surely for `rCodeSequence`. This transfers
UIQBOT almost-sure facts to the KMSW image of the R-phase codes; identifying
that image with `M̂_{τ_k,∞}` inside `M_{0,∞}` is `lem-quad-kmsw` and remains -/
theorem ae_rCodeSequence_mem_of_pitmanCodeShift_full
    {E : Set (ℕ → Fin 3)} (hE : MeasurableSet E)
    (hfull : iidCodeMeasure
      {ω | pitmanCode (fun i => ω (i + 1)) ∈ E} = 1) :
    ∀ᵐ ω ∂iidCodeMeasure, rCodeSequence ω ∈ E := by
  exact ae_mem_of_map_eq measurable_rCodeSequence measurable_pitmanCode_shift
    map_rCodeSequence hE hfull

/-- Almost surely the KMSW code sequence has finite incidence, nonnegative
and divergent `L`, unbounded-below `R`, and infinitely many KMSW bookkeeping
cut vertices. Each component event is measurable by
`MeasurableCutEvents`. (`def-uiqbot`, `prop-cut-vertex`, -/
theorem ae_rCodeSequence_KMSW_properties :
    ∀ᵐ ω ∂iidCodeMeasure,
      (∀ v, {e : ℕ | ∃ n, e < (kmswStage (rCodeSequence ω) n).nextEdge ∧
        ((kmswStage (rCodeSequence ω) n).west e = v ∨
          (kmswStage (rCodeSequence ω) n).east e = v)}.Finite) ∧
      Tendsto (L (rCodeSequence ω)) atTop atTop ∧
      (∀ a : ℤ, ∃ n, R (rCodeSequence ω) n ≤ a) ∧
      (∀ j, 0 ≤ L (rCodeSequence ω) j) ∧
      {v : ℕ | IsCutVertex (rCodeSequence ω) v}.Infinite := by
  let E : Set (ℕ → Fin 3) := {w |
    (∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) ∧
    Tendsto (L w) atTop atTop ∧
    (∀ a : ℤ, ∃ n, R w n ≤ a) ∧
    (∀ j, 0 ≤ L w j) ∧
    {v : ℕ | IsCutVertex w v}.Infinite}
  have hE : MeasurableSet E := by
    change MeasurableSet
      ({w | ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite} ∩
      ({w | Tendsto (L w) atTop atTop} ∩
      ({w | ∀ a : ℤ, ∃ n, R w n ≤ a} ∩
      ({w | ∀ j, 0 ≤ L w j} ∩
      {w | {v : ℕ | IsCutVertex w v}.Infinite}))))
    exact measurableSet_finiteIncidence.inter
      (measurableSet_tendsto_L.inter
        (measurableSet_R_unbounded_below.inter
          (measurableSet_L_nonneg.inter measurableSet_infinite_cutVertices)))
  have hsource : ∀ᵐ ω ∂iidCodeMeasure,
      pitmanCode (fun i => ω (i + 1)) ∈ E := by
    filter_upwards [pitmanCodes_ae_infinite_mapCutVertices] with ω hω
    dsimp only at hω
    obtain ⟨hfin, hT, hR, hL0, hmap⟩ := hω
    have hset : {v : ℕ | mapCutVertex (pitmanCode (fun i => ω (i + 1))) hfin v} =
        {v : ℕ | IsCutVertex (pitmanCode (fun i => ω (i + 1))) v} := by
      ext v
      exact mapCutVertex_iff _ hfin hT hR hL0 v
    have hIs : {v : ℕ | IsCutVertex (pitmanCode (fun i => ω (i + 1))) v}.Infinite := by
      rw [← hset]
      exact hmap
    exact ⟨hfin, hT, hR, hL0, hIs⟩
  have hfull : iidCodeMeasure
      {ω | pitmanCode (fun i => ω (i + 1)) ∈ E} = 1 := by
    exact (mem_ae_iff_prob_eq_one (measurableSet_preimage_pitmanCode_shift hE)).1 hsource
  have hdest := ae_rCodeSequence_mem_of_pitmanCodeShift_full hE hfull
  filter_upwards [hdest] with ω hω
  simpa only [E, Set.mem_ofPred_eq] using hω

/-- Almost surely the orbit cut vertices of the KMSW map built from
`rCodeSequence` are infinite. The measurable event transferred here is the
equivalent bookkeeping event `IsCutVertex`; the boundary-orbit identification
uses the finite-incidence and walk properties above. (`prop-cut-vertex`, -/
theorem ae_rCodeSequence_infinite_mapCutVertices :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∃ hfin : ∀ v, {e : ℕ | ∃ n,
        e < (kmswStage (rCodeSequence ω) n).nextEdge ∧
          ((kmswStage (rCodeSequence ω) n).west e = v ∨
            (kmswStage (rCodeSequence ω) n).east e = v)}.Finite,
        Tendsto (L (rCodeSequence ω)) atTop atTop ∧
        (∀ a : ℤ, ∃ n, R (rCodeSequence ω) n ≤ a) ∧
        (∀ j, 0 ≤ L (rCodeSequence ω) j) ∧
        {v : ℕ | mapCutVertex (rCodeSequence ω) hfin v}.Infinite := by
  filter_upwards [ae_rCodeSequence_KMSW_properties] with ω hω
  obtain ⟨hfin, hT, hR, hL0, hIs⟩ := hω
  have hset : {v : ℕ | mapCutVertex (rCodeSequence ω) hfin v} =
      {v : ℕ | IsCutVertex (rCodeSequence ω) v} := by
    ext v
    exact mapCutVertex_iff _ hfin hT hR hL0 v
  refine ⟨hfin, hT, hR, hL0, ?_⟩
  rw [hset]
  exact hIs

end DirectedDistances.KMSW
