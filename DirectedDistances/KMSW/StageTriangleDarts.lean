module

public import DirectedDistances.KMSW.StageFacePartition
public import DirectedDistances.KMSW.StageTriangleFaces

/-! # Creation-time dart triples for finite KMSW triangles

The branch at creation, rather than the three stored edge IDs alone, determines
which geometric darts bound a triangle (`def-kmsw`,
creates its triangle between stages `j` and `j + 1`. -/

public section
namespace DirectedDistances.KMSW

/-- The times at which `def-kmsw` creates a triangle -/
abbrev TriangleCreationTime (w : ℕ → Fin 3) :=
  {j : ℕ // w j = 0 ∨ w j = 1}



@[expose] def stageTriangleTimes (w : ℕ → Fin 3) : ℕ → List (TriangleCreationTime w)
  | 0 => []
  | n + 1 =>
    if h : w n = 0 ∨ w n = 1 then
      stageTriangleTimes w n ++ [⟨n, h⟩]
    else stageTriangleTimes w n

/-- The geometric face-cycle triple at creation. `false` is the west dart
and `true` the east dart, including for missing edges. The orders are exactly
those of `StageTriangleFaces`: existing-left `(t_e,t_lambda,h_p)`, fresh-left
`(t_lambda,h_p,t_q)`, and up `(t_lambda,h_q,h_p)` (`def-kmsw`, -/
@[expose] def stageTriangleDartTriple (w : ℕ → Fin 3) (j : TriangleCreationTime w) :
    (ℕ × Bool) × (ℕ × Bool) × (ℕ × Bool) :=
  let s := kmswStage w j.val
  if w j.val = 0 then
    match s.UL.dropLast.reverse with
    | e :: _ => ((e, false), (s.active, false), (s.nextEdge, true))
    | [] => ((s.active, false), (s.nextEdge, true), (s.nextEdge + 1, false))
  else ((s.active, false), (s.nextEdge + 1, true), (s.nextEdge, true))

/-- The three darts as a list, retaining the cyclic order in the creation -/
@[expose] def stageTriangleDartList (w : ℕ → Fin 3) (j : TriangleCreationTime w) :
    List (ℕ × Bool) :=
  let t := stageTriangleDartTriple w j
  [t.1, t.2.1, t.2.2]

/-- The stored record uses old active, new active, third edge, which differs
from face-cycle order for an existing-left triangle (`def-kmsw`, -/
@[expose] def stageTriangleRecord (w : ℕ → Fin 3) (j : TriangleCreationTime w) :
    ℕ × ℕ × ℕ :=
  let s := kmswStage w j.val
  if w j.val = 0 then
    match s.UL.dropLast.reverse with
    | e :: _ => (s.active, s.nextEdge, e)
    | [] => (s.active, s.nextEdge, s.nextEdge + 1)
  else (s.active, s.nextEdge, s.nextEdge + 1)

/-- The creation-time enumeration is exactly the increasing filtered range
`j < n`. Thus stage `n` includes the triangles created by the first `n` steps -/
theorem stageTriangleTimes_val (w : ℕ → Fin 3) (n : ℕ) :
    (stageTriangleTimes w n).map Subtype.val =
      (List.range n).filter (fun j => decide (w j = 0 ∨ w j = 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : w n = 0 ∨ w n = 1 <;>
      simp [stageTriangleTimes, h, List.range_succ, ih]

/-- A time occurs in the enumeration precisely when its zero-based index is -/
theorem mem_stageTriangleTimes (w : ℕ → Fin 3) (n : ℕ)
    (j : TriangleCreationTime w) :
    j ∈ stageTriangleTimes w n ↔ j.val < n := by
  induction n with
  | zero => simp [stageTriangleTimes]
  | succ n ih =>
    by_cases h : w n = 0 ∨ w n = 1
    · simp only [stageTriangleTimes, dite_eq_left h, List.mem_append,
        List.mem_singleton, ih]
      constructor
      · rintro (hj | rfl)
        · omega
        · exact Nat.lt_succ_self n
      · intro hj
        by_cases hlt : j.val < n
        · exact Or.inl hlt
        · exact Or.inr (Subtype.ext (show j.val = n by omega))
    · rw [stageTriangleTimes, dite_eq_right h, ih]
      constructor
      · omega
      · intro hj
        have hne : j.val ≠ n := by
          intro he
          apply h
          simpa only [← he] using j.property
        omega

/-- Creation times never repeat (`def-kmsw`, -/
theorem stageTriangleTimes_nodup (w : ℕ → Fin 3) (n : ℕ) :
    (stageTriangleTimes w n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ n ih =>
    by_cases h : w n = 0 ∨ w n = 1
    · rw [stageTriangleTimes, dite_eq_left h]
      apply ih.append (by simp)
      simp only [List.disjoint_left, List.mem_singleton]
      intro j hj he
      subst j
      have hh : n < n := (mem_stageTriangleTimes w n ⟨n, h⟩).mp hj
      omega
    · rw [stageTriangleTimes, dite_eq_right h]
      exact ih

/-- The time enumeration recovers the exact recorded triangles, with the
same order and multiplicity (`def-kmsw`, -/
theorem stageTriangleTimes_records (w : ℕ → Fin 3) (n : ℕ) :
    (stageTriangleTimes w n).map (stageTriangleRecord w) =
      (kmswStage w n).triangles := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h0 : w n = 0
    · have hc : w n = 0 ∨ w n = 1 := Or.inl h0
      rw [stageTriangleTimes, dite_eq_left hc, List.map_append, ih]
      change (kmswStage w n).triangles ++ [stageTriangleRecord w ⟨n, hc⟩] = _
      simp only [kmswStage, kmswStep, kmswCodeStep, h0, ↓reduceIte]
      cases hl : (kmswStage w n).UL.dropLast.reverse <;>
        simp [kmswStepOfStep, stageTriangleRecord, h0, hl]
    · by_cases h1 : w n = 1
      · have hc : w n = 0 ∨ w n = 1 := Or.inr h1
        rw [stageTriangleTimes, dite_eq_left hc, List.map_append, ih]
        simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep,
          stageTriangleRecord]
      · have hc : ¬ (w n = 0 ∨ w n = 1) := by tauto
        rw [stageTriangleTimes, dite_eq_right hc, ih]
        simp only [kmswStage, kmswStep, kmswCodeStep, h0, h1, ↓reduceIte]
        cases hr : (kmswStage w n).UR <;> simp only [kmswStepOfStep, hr, State.addEdge]

/-- There is one creation time for each recorded triangle (`def-kmsw`, -/
theorem stageTriangleTimes_length (w : ℕ → Fin 3) (n : ℕ) :
    (stageTriangleTimes w n).length = (kmswStage w n).triangles.length := by
  have h := congrArg List.length (stageTriangleTimes_records w n)
  simpa only [List.length_map] using h

/-- The fresh-left formula agrees with the creation cycle -/
theorem stageTriangleDartTriple_left_fresh (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) (hc : w j.val = 0)
    (hl : (kmswStage w j.val).UL.dropLast.reverse = []) :
    stageTriangleDartTriple w j =
      (((kmswStage w j.val).active, false),
       ((kmswStage w j.val).nextEdge, true),
       ((kmswStage w j.val).nextEdge + 1, false)) := by
  simp only [stageTriangleDartTriple, hc, ↓reduceIte, hl]

/-- The existing-left formula agrees with the creation cycle -/
theorem stageTriangleDartTriple_left_existing (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) (hc : w j.val = 0) (e : ℕ) (es : List ℕ)
    (hl : (kmswStage w j.val).UL.dropLast.reverse = e :: es) :
    stageTriangleDartTriple w j =
      ((e, false), ((kmswStage w j.val).active, false),
       ((kmswStage w j.val).nextEdge, true)) := by
  simp only [stageTriangleDartTriple, hc, ↓reduceIte, hl]

/-- The up formula agrees with the creation cycle -/
theorem stageTriangleDartTriple_up (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) (hc : w j.val = 1) :
    stageTriangleDartTriple w j =
      (((kmswStage w j.val).active, false),
       ((kmswStage w j.val).nextEdge + 1, true),
       ((kmswStage w j.val).nextEdge, true)) := by
  have h0 : w j.val ≠ 0 := by rw [hc]; decide
  simp only [stageTriangleDartTriple, h0, ↓reduceIte]

/-- All triangle darts, in chronological order and then in face-cycle order -/
@[expose] def stageTriangleDartsVal (w : ℕ → Fin 3) (n : ℕ) : List (ℕ × Bool) :=
  (stageTriangleTimes w n).flatMap (stageTriangleDartList w)

private def boundaryWord (s : State) : List (ℕ × Bool) :=
  s.UL.map (fun e => (e, false)) ++ s.UR.map (fun e => (e, false)) ++
    s.LR.reverse.map (fun e => (e, true)) ++ s.LL.reverse.map (fun e => (e, true))

private def stepTriangleDarts (s : State) : Step → List (ℕ × Bool)
  | .down => []
  | .left => match s.UL.dropLast.reverse with
    | e :: _ => [(e, false), (s.active, false), (s.nextEdge, true)]
    | [] => [(s.active, false), (s.nextEdge, true), (s.nextEdge + 1, false)]
  | .up => [(s.active, false), (s.nextEdge + 1, true), (s.nextEdge, true)]

private def freshDarts (s : State) : Step → List (ℕ × Bool)
  | .down => if s.UR = [] then [(s.nextEdge, false), (s.nextEdge, true)] else []
  | .left => if s.UL.dropLast.reverse = [] then
      [(s.nextEdge, false), (s.nextEdge, true),
       (s.nextEdge + 1, false), (s.nextEdge + 1, true)]
    else [(s.nextEdge, false), (s.nextEdge, true)]
  | .up => [(s.nextEdge, false), (s.nextEdge, true),
       (s.nextEdge + 1, false), (s.nextEdge + 1, true)]

private theorem step_dart_balance (s : State) (c : Step)
    (xs : List ℕ) (hUL : s.UL = xs ++ [s.active]) (d : ℕ × Bool) :
    (boundaryWord (kmswStepOfStep s c)).count d + (stepTriangleDarts s c).count d =
      (boundaryWord s).count d + (freshDarts s c).count d := by
  cases c with
  | down =>
    cases hr : s.UR with
    | nil =>
      simp [boundaryWord, kmswStepOfStep, hr, State.addEdge, stepTriangleDarts,
        freshDarts, List.count_append, List.count_cons, List.reverse_append]
      ; omega
    | cons e es =>
      simp [boundaryWord, kmswStepOfStep, hr, stepTriangleDarts,
        freshDarts, List.count_append, List.count_cons]
  | left =>
    cases hr : xs.reverse with
    | nil =>
      have hx : xs = [] := List.reverse_eq_nil_iff.mp hr
      simp [boundaryWord, kmswStepOfStep, stepTriangleDarts, freshDarts,
        State.addEdge, hUL, hx, List.count_append, List.count_cons]
      ; omega
    | cons e es =>
      have hx : xs = es.reverse ++ [e] := by
        have hh := congrArg List.reverse hr
        simpa only [List.reverse_reverse, List.reverse_cons] using hh
      simp [boundaryWord, kmswStepOfStep, stepTriangleDarts, freshDarts,
        State.addEdge, hUL, hx, List.count_append, List.count_cons]
      ; omega
  | up =>
    simp [boundaryWord, kmswStepOfStep, stepTriangleDarts, freshDarts,
      State.addEdge, hUL, List.count_append, List.count_cons]
    ; omega

private theorem fresh_dart_interval (s : State) (c : Step) (d : ℕ × Bool) :
    (if d.1 < s.nextEdge then 1 else 0) + (freshDarts s c).count d =
      if d.1 < (kmswStepOfStep s c).nextEdge then 1 else 0 := by
  rcases d with ⟨e, b⟩
  cases c with
  | down =>
    cases hr : s.UR with
    | nil =>
      cases b <;>
        simp [freshDarts, kmswStepOfStep, hr, State.addEdge, List.count_cons,
          beq_iff_eq, Prod.mk.injEq] <;> split_ifs <;> omega
    | cons f fs => simp [freshDarts, kmswStepOfStep, hr]
  | left =>
    cases hl : s.UL.dropLast.reverse with
    | nil =>
      cases b <;>
        simp [freshDarts, kmswStepOfStep, hl, State.addEdge, List.count_cons,
          beq_iff_eq, Prod.mk.injEq] <;> split_ifs <;> omega
    | cons f fs =>
      cases b <;>
        simp [freshDarts, kmswStepOfStep, hl, State.addEdge, List.count_cons,
          beq_iff_eq, Prod.mk.injEq] <;> split_ifs <;> omega
  | up =>
    cases b <;>
      simp [freshDarts, kmswStepOfStep, State.addEdge, List.count_cons,
        beq_iff_eq, Prod.mk.injEq] <;> split_ifs <;> omega

private theorem stageTriangleDartsVal_succ (w : ℕ → Fin 3) (n : ℕ) :
    stageTriangleDartsVal w (n + 1) = stageTriangleDartsVal w n ++
      stepTriangleDarts (kmswStage w n) (kmswCodeStep (w n)) := by
  by_cases h0 : w n = 0
  · have hc : w n = 0 ∨ w n = 1 := Or.inl h0
    simp only [stageTriangleDartsVal, stageTriangleTimes, dite_eq_left hc,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simp [stageTriangleDartList, stageTriangleDartTriple, stepTriangleDarts,
      kmswCodeStep, h0]
    ; split <;> rfl
  · by_cases h1 : w n = 1
    · have hc : w n = 0 ∨ w n = 1 := Or.inr h1
      simp [stageTriangleDartsVal, stageTriangleTimes,
        stageTriangleDartList, stageTriangleDartTriple, stepTriangleDarts,
        kmswCodeStep, h1]
    · have hc : ¬ (w n = 0 ∨ w n = 1) := by tauto
      simp [stageTriangleDartsVal, stageTriangleTimes, stepTriangleDarts,
        kmswCodeStep, h0, h1]

/-- Every allocated geometric dart occurs exactly once in the concatenation
of the outer word and the chronological triangle triples; unallocated IDs -/
theorem stage_dart_partition_count (w : ℕ → Fin 3) (n : ℕ) (d : ℕ × Bool) :
    (stageOuterWordVal w n ++ stageTriangleDartsVal w n).count d =
      if d.1 < (kmswStage w n).nextEdge then 1 else 0 := by
  induction n with
  | zero =>
    rcases d with ⟨e, b⟩
    cases b <;>
      simp [stageOuterWordVal_eq_runs, kmswStage, kmswInit,
        stageTriangleDartsVal, stageTriangleTimes, List.count_cons,
        beq_iff_eq, Prod.mk.injEq] <;> split_ifs <;> omega
  | succ n ih =>
    obtain ⟨xs, hUL⟩ := kmswStage_UL_last w n
    have hb := step_dart_balance (kmswStage w n) (kmswCodeStep (w n)) xs hUL d
    have hf := fresh_dart_interval (kmswStage w n) (kmswCodeStep (w n)) d
    have ho : ∀ m, stageOuterWordVal w m = boundaryWord (kmswStage w m) := by
      intro m
      exact stageOuterWordVal_eq_runs w m
    rw [ho] at ih
    rw [stageTriangleDartsVal_succ, ho]
    change (boundaryWord (kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n))) ++
      (stageTriangleDartsVal w n ++
        stepTriangleDarts (kmswStage w n) (kmswCodeStep (w n)))).count d = _
    simp only [List.count_append] at ih ⊢
    change _ = if d.1 < (kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n))).nextEdge
      then 1 else 0
    omega

/-- The outer and triangle words together have no repeated dart -/
theorem stage_dart_partition_nodup (w : ℕ → Fin 3) (n : ℕ) :
    (stageOuterWordVal w n ++ stageTriangleDartsVal w n).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro d
  rw [stage_dart_partition_count]
  split_ifs <;> omega

/-- No dart belongs both to the outer word and to any triangle -/
theorem stage_outer_triangle_disjoint (w : ℕ → Fin 3) (n : ℕ) :
    List.Disjoint (stageOuterWordVal w n) (stageTriangleDartsVal w n) :=
  List.disjoint_of_nodup_append (stage_dart_partition_nodup w n)

/-- Across all chronological triangle triples, every dart is distinct -/
theorem stageTriangleDartsVal_nodup (w : ℕ → Fin 3) (n : ℕ) :
    (stageTriangleDartsVal w n).Nodup :=
  (stage_dart_partition_nodup w n).of_append_right

/-- Any two different entries of the creation-time enumeration have disjoint -/
theorem stageTriangleDartLists_pairwise (w : ℕ → Fin 3) (n : ℕ) :
    (stageTriangleTimes w n).Pairwise (fun i j =>
      List.Disjoint (stageTriangleDartList w i) (stageTriangleDartList w j)) :=
  (List.nodup_flatMap.mp (stageTriangleDartsVal_nodup w n)).2

/-- The three darts of each triangle are distinct even when considered
independently of any later stage (`def-kmsw`, -/
theorem stageTriangleDartList_nodup (w : ℕ → Fin 3) (j : TriangleCreationTime w) :
    (stageTriangleDartList w j).Nodup := by
  exact (List.nodup_flatMap.mp (stageTriangleDartsVal_nodup w (j.val + 1))).1 j
    ((mem_stageTriangleTimes w (j.val + 1) j).mpr (Nat.lt_succ_self _))

/-- Every ID in the full face enumeration is allocated at the indicated stage -/
theorem stage_face_dart_lt_nextEdge (w : ℕ → Fin 3) (n : ℕ) (d : ℕ × Bool)
    (hd : d ∈ stageOuterWordVal w n ++ stageTriangleDartsVal w n) :
    d.1 < (kmswStage w n).nextEdge := by
  have hp := List.count_pos_iff.mpr hd
  rw [stage_dart_partition_count] at hp
  split_ifs at hp with h
  · exact h
  · omega

/-- Typed enumeration of the outer and triangle darts. This uses the proved
allocation bound, including for missing edges (`def-kmsw`, -/
@[expose] def stageFaceDarts (w : ℕ → Fin 3) (n : ℕ) :
    List (StageDart (kmswStage w n).nextEdge) :=
  (stageOuterWordVal w n ++ stageTriangleDartsVal w n).attach.map fun d =>
    ((⟨d.val.1, stage_face_dart_lt_nextEdge w n d.val d.property⟩ :
      Fin (kmswStage w n).nextEdge), d.val.2)

/-- Projecting the typed enumeration preserves its exact order -/
theorem stageFaceDarts_val (w : ℕ → Fin 3) (n : ℕ) :
    (stageFaceDarts w n).map (fun d => (d.1.val, d.2)) =
      stageOuterWordVal w n ++ stageTriangleDartsVal w n := by
  simp only [stageFaceDarts, List.map_map]
  exact List.attach_map_subtype_val _

/-- The typed enumeration has no repeated geometric dart -/
theorem stageFaceDarts_nodup (w : ℕ → Fin 3) (n : ℕ) :
    (stageFaceDarts w n).Nodup := by
  apply List.Nodup.of_map (fun d => (d.1.val, d.2))
  rw [stageFaceDarts_val]
  exact stage_dart_partition_nodup w n

/-- Each recorded triangle contributes exactly three entries to the dart -/
theorem stageTriangleDartsVal_length (w : ℕ → Fin 3) (n : ℕ) :
    (stageTriangleDartsVal w n).length = 3 * (kmswStage w n).triangles.length := by
  simp [stageTriangleDartsVal, List.length_flatMap, stageTriangleDartList,
    stageTriangleTimes_length, Nat.mul_comm]

/-- The typed face enumeration has the full dart-carrier cardinality, by -/
theorem stageFaceDarts_length (w : ℕ → Fin 3) (n : ℕ) :
    (stageFaceDarts w n).length = 2 * (kmswStage w n).nextEdge := by
  have hl := congrArg List.length (stageFaceDarts_val w n)
  simp only [List.length_map, List.length_append, stageTriangleDartsVal_length] at hl
  rw [hl]
  have ho : (stageOuterWordVal w n).length = (stageOuterWord w n).length :=
    List.length_map _
  rw [ho]
  exact (kmswStage_dart_count w n).symm

/-- Finset cardinality closes the finite dart partition: the disjoint face
enumeration exhausts `Fin nextEdge × Bool` (`def-kmsw`, -/
theorem stageFaceDarts_toFinset_eq_univ (w : ℕ → Fin 3) (n : ℕ) :
    (stageFaceDarts w n).toFinset = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [List.toFinset_card_of_nodup (stageFaceDarts_nodup w n), stageFaceDarts_length]
  simp [StageDart, Nat.mul_comm]

/-- Value projection preserves outer-word membership -/
theorem stageOuterWord_mem_val (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ stageOuterWord w n ↔ (d.1.val, d.2) ∈ stageOuterWordVal w n := by
  constructor
  · intro hd
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  · intro hd
    obtain ⟨e, he, hed⟩ := List.mem_map.mp hd
    have hv : e.1.val = d.1.val := congrArg (fun x : ℕ × Bool => x.1) hed
    have hs : e.2 = d.2 := congrArg (fun x : ℕ × Bool => x.2) hed
    have heq : e = d := Prod.ext (Fin.ext hv) hs
    exact heq ▸ he

/-- The outer word consists of west darts of `UL`/`UR` and east darts of
`LR`/`LL`, including missing edges (`defn:bound-edges`, -/
theorem stageOuterWord_mem_iff (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ stageOuterWord w n ↔
      (d.2 = false ∧ (d.1.val ∈ (kmswStage w n).UL ∨
        d.1.val ∈ (kmswStage w n).UR)) ∨
      (d.2 = true ∧ (d.1.val ∈ (kmswStage w n).LR ∨
        d.1.val ∈ (kmswStage w n).LL)) := by
  rw [stageOuterWord_mem_val, stageOuterWordVal_eq_runs]
  rcases d with ⟨e, b⟩
  cases b <;> simp [Prod.mk.injEq]

/-- Distinct creation times before stage `n` have disjoint triangle darts -/
theorem stageTriangleDartLists_disjoint (w : ℕ → Fin 3) (n : ℕ)
    (i j : TriangleCreationTime w) (hi : i.val < n) (hj : j.val < n) (hij : i ≠ j) :
    List.Disjoint (stageTriangleDartList w i) (stageTriangleDartList w j) := by
  exact (stageTriangleDartLists_pairwise w n).forall
    ((mem_stageTriangleTimes w n i).mpr hi)
    ((mem_stageTriangleTimes w n j).mpr hj) hij

/-- A triangle dart cannot lie in the stage's outer word -/
theorem stageTriangleDart_not_outer (w : ℕ → Fin 3) (n : ℕ)
    (j : TriangleCreationTime w) (hj : j.val < n)
    (d : StageDart (kmswStage w n).nextEdge)
    (hd : (d.1.val, d.2) ∈ stageTriangleDartList w j) :
    d ∉ stageOuterWord w n := by
  intro ho
  have ht : (d.1.val, d.2) ∈ stageTriangleDartsVal w n :=
    List.mem_flatMap.mpr ⟨j, (mem_stageTriangleTimes w n j).mpr hj, hd⟩
  exact List.disjoint_left.mp (stage_outer_triangle_disjoint w n)
    ((stageOuterWord_mem_val w n d).mp ho) ht

/-- Every dart of `Fin nextEdge × Bool` lies in the outer word or in exactly
one chronological triangle triple. The Finset cardinality theorem supplies
coverage; disjointness supplies uniqueness (`def-kmsw`, -/
theorem stage_dart_partition (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ stageOuterWord w n ∨
      ∃! j : TriangleCreationTime w,
        j.val < n ∧ (d.1.val, d.2) ∈ stageTriangleDartList w j := by
  have hd : d ∈ stageFaceDarts w n := by
    apply List.mem_toFinset.mp
    rw [stageFaceDarts_toFinset_eq_univ]
    exact Finset.mem_univ d
  have hv : (d.1.val, d.2) ∈ stageOuterWordVal w n ++ stageTriangleDartsVal w n := by
    rw [← stageFaceDarts_val]
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  rcases List.mem_append.mp hv with ho | ht
  · exact Or.inl ((stageOuterWord_mem_val w n d).mpr ho)
  · right
    obtain ⟨j, hj, hdj⟩ := List.mem_flatMap.mp ht
    have hjn := (mem_stageTriangleTimes w n j).mp hj
    refine ⟨j, ⟨hjn, hdj⟩, ?_⟩
    intro i hi
    by_contra hij
    exact List.disjoint_left.mp (stageTriangleDartLists_disjoint w n i j hi.1 hjn hij)
      hi.2 hdj

end DirectedDistances.KMSW
