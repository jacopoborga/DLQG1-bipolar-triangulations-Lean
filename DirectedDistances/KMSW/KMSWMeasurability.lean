module

public import DirectedDistances.KMSW.MeasurableCutEvents
public import DirectedDistances.KMSW.StageSubgraph
public import DirectedDistances.RandomWalk.IIDCodeRelabel

/-! # Measurable finite stages, hitting times and eventual integer values

Helper infrastructure for the laws used in Section 6 (`eq:stationarity-rel`,
The source sample space is `ℕ → Fin 3` with its product measurable space. -/

public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory Quiver
open DirectedDistances.RandomWalk

/-- Shifted stage `n` is determined by the codes at precisely the indices
`1 ≤ i ≤ n`; helper for the Section 6 and Section 7 laws. -/
theorem kmswStage_shift_congr {ω ω' : ℕ → Fin 3} {n : ℕ}
    (h : ∀ i, 1 ≤ i → i ≤ n → ω i = ω' i) :
    kmswStage (fun i => ω (i + 1)) n = kmswStage (fun i => ω' (i + 1)) n := by
  exact kmswStage_congr (fun i hi => h (i + 1) (by omega) (by omega))

/-- Every function of a fixed shifted stage is measurable, with an arbitrary
measurable codomain: the stage has finite range. Helper, not a paper statement. -/
theorem measurable_kmswStage_shift_comp {β : Type*} [MeasurableSpace β]
    (n : ℕ) (F : State → β) :
    Measurable (fun ω : ℕ → Fin 3 => F (kmswStage (fun i => ω (i + 1)) n)) := by
  refine measurable_of_factors_prefix (n + 1) _ (fun ω ω' h => ?_)
  rw [kmswStage_shift_congr (fun i _ hi => h i (by omega))]



theorem measurableSet_kmswStage_shift (n : ℕ) (P : State → Prop) :
    MeasurableSet {ω : ℕ → Fin 3 | P (kmswStage (fun i => ω (i + 1)) n)} := by
  exact measurableSet_of_factors_prefix (n + 1) _ (fun ω ω' h => by
    rw [kmswStage_shift_congr (fun i _ hi => h i (by omega))])

/-- The first coordinate of `codeWalk` is exactly the shifted KMSW coordinate
`L`; indexing helper for the Section 6 and Section 7 laws. -/
theorem codeWalk_fst_eq_L_shift (ω : ℕ → Fin 3) (n : ℕ) :
    (codeWalk ω n).1 = L (fun i => ω (i + 1)) n := by
  simp only [codeWalk, L, Prod.fst_sum]

/-- The second coordinate of `codeWalk` is exactly the shifted KMSW coordinate
`R`; indexing helper for the Section 6 and Section 7 laws. -/
theorem codeWalk_snd_eq_R_shift (ω : ℕ → Fin 3) (n : ℕ) :
    (codeWalk ω n).2 = R (fun i => ω (i + 1)) n := by
  simp only [codeWalk, R, Prod.snd_sum]

/-- Full measurability of the first hit of the first walk coordinate, including
`⊤` on paths which never hit. Helper for the Section 6 and Section 7 laws. -/
theorem measurable_codeFstFirstHit (a : ℤ) : Measurable (codeFstFirstHit a) := by
  exact ENat.measurable_iff.mpr (fun k =>
    codePast_le k _ (measurableSet_codePast_codeFstFirstHit_eq a k))

/-- Full measurability of the first hit of the second walk coordinate, including
`⊤` on paths which never hit. Helper for the Section 6 and Section 7 laws. -/
theorem measurable_codeSndFirstHit (a : ℤ) : Measurable (codeSndFirstHit a) := by
  exact ENat.measurable_iff.mpr (fun k =>
    codePast_le k _ (measurableSet_codePast_codeSndFirstHit_eq a k))

private def stageCongrMap {w w' : ℕ → Fin 3} {n : ℕ}
    (h : kmswStage w n = kmswStage w' n) :
    Prefunctor (StagePresentVertex w n) (StagePresentVertex w' n) where
  obj v := ⟨v.id⟩
  map {_ _} e := ⟨e.val, by simpa only [h] using e.property⟩

private theorem stageCongrMap_length {w w' : ℕ → Fin 3} {n : ℕ}
    (h : kmswStage w n = kmswStage w' n) {a b : StagePresentVertex w n}
    (p : Path a b) : ((stageCongrMap h).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]

private theorem stage_pathLengths_congr {w w' : ℕ → Fin 3} {n : ℕ}
    (h : kmswStage w n = kmswStage w' n) (a b : ℕ) :
    pathLengths (⟨a⟩ : StagePresentVertex w n) ⟨b⟩ =
      pathLengths (⟨a⟩ : StagePresentVertex w' n) ⟨b⟩ := by
  ext k
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(stageCongrMap h).mapPath p, stageCongrMap_length h p⟩
  · rintro ⟨p, rfl⟩
    exact ⟨(stageCongrMap h.symm).mapPath p, stageCongrMap_length h.symm p⟩

/-- Reachability between fixed vertex IDs in a fixed stage is measurable.
Edges retain their allocation IDs and presence condition. Helper for Section 7 -/
theorem measurableSet_stage_reachable (n a b : ℕ) :
    MeasurableSet {ω : ℕ → Fin 3 |
      Reachable (⟨a⟩ : StagePresentVertex (fun i => ω (i + 1)) n) ⟨b⟩} := by
  refine measurableSet_of_factors_prefix (n + 1) _ (fun ω ω' h => ?_)
  have hs : kmswStage (fun i => ω (i + 1)) n =
      kmswStage (fun i => ω' (i + 1)) n :=
    kmswStage_shift_congr (fun i _ hi => h i (by omega))
  constructor
  · rintro ⟨p⟩
    exact ⟨(stageCongrMap hs).mapPath p⟩
  · rintro ⟨p⟩
    exact ⟨(stageCongrMap hs.symm).mapPath p⟩

/-- Every predicate of the attainable path-length set at a fixed stage is -/
theorem measurableSet_stage_pathLengths (n a b : ℕ) (P : Set ℕ → Prop) :
    MeasurableSet {ω : ℕ → Fin 3 |
      P (pathLengths (⟨a⟩ : StagePresentVertex (fun i => ω (i + 1)) n) ⟨b⟩)} := by
  refine measurableSet_of_factors_prefix (n + 1) _ (fun ω ω' h => ?_)
  rw [stage_pathLengths_congr
    (kmswStage_shift_congr (fun i _ hi => h i (by omega))) a b]

/-- Every function of the fixed-stage longest-path supremum is measurable.
This uses the existing `ldpSup`, with bottom for unreachable pairs; helper -/
theorem measurable_stage_ldpSup_comp {β : Type*} [MeasurableSpace β]
    (n a b : ℕ) (F : WithBot ℕ → β) :
    Measurable (fun ω : ℕ → Fin 3 =>
      F (ldpSup (⟨a⟩ : StagePresentVertex (fun i => ω (i + 1)) n) ⟨b⟩)) := by
  refine measurable_of_factors_prefix (n + 1) _ (fun ω ω' h => ?_)
  unfold ldpSup
  rw [stage_pathLengths_congr
    (kmswStage_shift_congr (fun i _ hi => h i (by omega))) a b]

/-- Every predicate of the fixed-stage longest-path supremum is measurable; -/
theorem measurableSet_stage_ldpSup (n a b : ℕ) (P : WithBot ℕ → Prop) :
    MeasurableSet {ω : ℕ → Fin 3 |
      P (ldpSup (⟨a⟩ : StagePresentVertex (fun i => ω (i + 1)) n) ⟨b⟩)} := by
  exact measurableSet_stage_pathLengths n a b
    (fun s => P (sSup ((fun k : ℕ => (k : WithBot ℕ)) '' s)))

/-- The eventual integer of a sequence, with the specified default if it is
not eventually constant. Helper for the Section 6 laws -/
@[expose] noncomputable def eventualIntValue (default : ℤ) (u : ℕ → ℤ) : ℤ := by
  classical
  exact if h : ∃ z : ℤ, ∀ᶠ j in atTop, u j = z then h.choose else default

/-- The helper `eventualIntValue` agrees with every eventual constant. -/
theorem eventualIntValue_eq (default : ℤ) {u : ℕ → ℤ} {z : ℤ}
    (hz : ∀ᶠ j in atTop, u j = z) : eventualIntValue default u = z := by
  classical
  have h : ∃ z : ℤ, ∀ᶠ j in atTop, u j = z := ⟨z, hz⟩
  rw [eventualIntValue, dite_eq_left h]
  obtain ⟨j, hj, hjz⟩ := (h.choose_spec.and hz).exists
  exact hj.symm.trans hjz

/-- If no eventual constant exists, `eventualIntValue` is the given default. -/
theorem eventualIntValue_eq_default (default : ℤ) {u : ℕ → ℤ}
    (h : ¬ ∃ z : ℤ, ∀ᶠ j in atTop, u j = z) :
    eventualIntValue default u = default := by
  classical
  exact dite_eq_right h

/-- Measurability of each fixed eventual-value event, for a sequence of
measurable integer functions. Helper for Section 6, not a paper statement. -/
theorem measurableSet_eventually_eq_int {Ω : Type*} [MeasurableSpace Ω]
    (f : ℕ → Ω → ℤ) (hf : ∀ j, Measurable (f j)) (z : ℤ) :
    MeasurableSet {ω | ∀ᶠ j in atTop, f j ω = z} := by
  have he : {ω | ∀ᶠ j in atTop, f j ω = z} =
      ⋃ N : ℕ, ⋂ j : ℕ, ⋂ (_ : N ≤ j), {ω | f j ω = z} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, eventually_atTop]
  rw [he]
  exact MeasurableSet.iUnion (fun N => MeasurableSet.iInter (fun j =>
    MeasurableSet.iInter (fun _ => measurableSet_eq_fun (hf j) measurable_const)))

/-- Eventual constancy of measurable integer functions is a measurable -/
theorem measurableSet_eventually_constant_int {Ω : Type*} [MeasurableSpace Ω]
    (f : ℕ → Ω → ℤ) (hf : ∀ j, Measurable (f j)) :
    MeasurableSet {ω | ∃ z : ℤ, ∀ᶠ j in atTop, f j ω = z} := by
  have he : {ω | ∃ z : ℤ, ∀ᶠ j in atTop, f j ω = z} =
      ⋃ z : ℤ, {ω | ∀ᶠ j in atTop, f j ω = z} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [he]
  exact MeasurableSet.iUnion (measurableSet_eventually_eq_int f hf)

/-- The eventual value with a default is measurable whenever all integer
coordinates are measurable. Applies in particular to `Ω = ℕ → Fin 3`; -/
theorem measurable_eventualIntValue {Ω : Type*} [MeasurableSpace Ω]
    (default : ℤ) (f : ℕ → Ω → ℤ) (hf : ∀ j, Measurable (f j)) :
    Measurable (fun ω => eventualIntValue default (fun j => f j ω)) := by
  classical
  refine measurable_to_countable' (fun z => ?_)
  have he : (fun ω => eventualIntValue default (fun j => f j ω)) ⁻¹' {z} =
      {ω | ∀ᶠ j in atTop, f j ω = z} ∪
        ({ω | ¬ ∃ y : ℤ, ∀ᶠ j in atTop, f j ω = y} ∩ {ω : Ω | default = z}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_inter_iff, Set.mem_ofPred_eq]
    by_cases h : ∃ y : ℤ, ∀ᶠ j in atTop, f j ω = y
    · obtain ⟨y, hy⟩ := h
      rw [eventualIntValue_eq default hy]
      constructor
      · intro hyz
        exact Or.inl (hy.mono (fun j hj => hj.trans hyz))
      · rintro (hz | ⟨hn, _⟩)
        · exact (eventualIntValue_eq default hy).symm.trans (eventualIntValue_eq default hz)
        · exact (hn ⟨y, hy⟩).elim
    · rw [eventualIntValue_eq_default default h]
      constructor
      · intro hd
        exact Or.inr ⟨h, hd⟩
      · rintro (hz | ⟨_, hd⟩)
        · exact (h ⟨z, hz⟩).elim
        · exact hd
  rw [he]
  exact (measurableSet_eventually_eq_int f hf z).union
    ((measurableSet_eventually_constant_int f hf).compl.inter
      (by by_cases h : default = z <;> simp only [h, MeasurableSet.univ,
        MeasurableSet.empty, Set.ofPred_true, Set.ofPred_false]))

end DirectedDistances.KMSW
