module

public import DirectedDistances.KMSW.BoundaryRecordsMissing
public import DirectedDistances.KMSW.BoundaryRecordsUL
public import DirectedDistances.KMSW.WalkRecordCounts
import DirectedDistances.KMSW.CutEquivalenceConverse

/-! # Active endpoint visits to lower boundary vertices

These helpers are not a bundled proof of the numbered paper result. -/

public section
namespace DirectedDistances.KMSW
open scoped Classical

private theorem coord_L_visit (w : ℕ → Fin 3) (n : ℕ) :
    L w (n + 1) = L w n + (RandomWalk.lazyTwoDimensionalStep (w n)).1 :=
  Finset.sum_range_succ _ _

private theorem coord_R_visit (w : ℕ → Fin 3) (n : ℕ) :
    R w (n + 1) = R w n + (RandomWalk.lazyTwoDimensionalStep (w n)).2 :=
  Finset.sum_range_succ _ _

private theorem left_record_creation (w : ℕ → Fin 3) {r : ℕ}
    (hrec : ∀ j ≤ r, L w (r + 1) < L w j) :
    w r = 0 ∧ (kmswStage w r).UL.dropLast.reverse = [] := by
  have hs := coord_L_visit w r
  have hl := hrec r le_rfl
  have hc : w r = 0 := by
    change L w (r + 1) = L w r + ((w r : ℤ) - 1) at hs
    apply Fin.ext
    have := (w r).isLt
    omega
  rw [hc, RandomWalk.lazyTwoDimensionalStep_zero] at hs
  have hmin : minL w r = L w r := by
    obtain ⟨j, hj, he⟩ := runningMin_attained (L w) r
    have hjrec := hrec j hj
    have hle := runningMin_le (L w) r r le_rfl
    change minL w r = L w j at he
    change minL w r ≤ L w r at hle
    dsimp at hs
    omega
  have hlen := kmswStage_UL_length w r
  have hlen' : (kmswStage w r).UL.length = 1 := by omega
  have hempty : (kmswStage w r).UL.dropLast = [] := by
    apply List.length_eq_zero_iff.mp
    rw [List.length_dropLast, hlen']
  exact ⟨hc, by rw [hempty]; rfl⟩

/-- the west endpoint of a newly created LL edge is the new active initial vertex. -/
theorem kmswLLCreatedEdge_west_eq_act (w : ℕ → Fin 3) {t : ℕ}
    (ht : 0 < t) (hrec : ∀ j < t, L w t < L w j) :
    (kmswStage w t).west (kmswLLCreatedEdge w t) =
      (kmswStage w t).west (act w t) := by
  cases t with
  | zero => omega
  | succ r =>
    obtain ⟨hc, hu⟩ := left_record_creation w (fun j hj => hrec j (by omega))
    simp [kmswStage, kmswLLCreatedEdge, act, kmswStep, kmswCodeStep,
      hc, kmswStepOfStep, hu, State.addEdge]

/-- no earlier active edge has the west vertex of a new LL record edge. -/
theorem kmswLLCreatedEdge_west_not_visited_before (w : ℕ → Fin 3) {t m : ℕ}
    (ht : 0 < t) (hrec : ∀ j < t, L w t < L w j) (hm : m < t) :
    (kmswStage w m).west (act w m) ≠
      (kmswStage w t).west (kmswLLCreatedEdge w t) := by
  cases t with
  | zero => omega
  | succ r =>
    obtain ⟨hc, hu⟩ := left_record_creation w (fun j hj => hrec j (by omega))
    have hv : (kmswStage w (r + 1)).west (kmswLLCreatedEdge w (r + 1)) =
        (kmswStage w r).nextVertex := by
      simp [kmswStage, kmswLLCreatedEdge, kmswStep, kmswCodeStep,
        hc, kmswStepOfStep, hu, State.addEdge]
    rw [hv]
    exact Nat.ne_of_lt (((CutConverse.endpoint_bound w m) _
      (act_lt_nextEdge w le_rfl)).1.trans_le
        (CutConverse.nextVertex_mono w (by omega : m ≤ r)))

/-- a return to the LL creation level before descending below it revisits its west vertex. -/
theorem kmswLLCreatedEdge_west_visit_of_level (w : ℕ → Fin 3) {t m : ℕ}
    (ht : 0 < t) (hrec : ∀ j < t, L w t < L w j)
    (htm : t ≤ m) (hlev : L w m = L w t)
    (habove : ∀ j ≤ m, L w t ≤ L w j) :
    (kmswStage w m).west (act w m) =
      (kmswStage w t).west (kmswLLCreatedEdge w t) := by
  have heq := kmsw_west_act_eq_of_level w htm hlev.symm
    (fun j _ hjm => habove j hjm)
  have hstable := (kmswStage_endpoints_stable w htm (act_lt_nextEdge w le_rfl)).1
  exact heq.symm.trans (hstable.trans (kmswLLCreatedEdge_west_eq_act w ht hrec).symm)

private theorem ul_allocated (w : ℕ → Fin 3) {n e : ℕ}
    (he : e ∈ (kmswStage w n).UL) : e < (kmswStage w n).nextEdge := by
  rw [kmswStage_UL_eq] at he
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp he
  have hmn := List.mem_range.mp (List.mem_filter.mp hm).1
  exact act_lt_nextEdge w (by omega)

private theorem reverse_dropLast (xs : List ℕ) :
    xs.dropLast.reverse = xs.reverse.tail := by
  simpa only [List.reverse_reverse] using
    congrArg List.reverse (List.dropLast_reverse (l := xs.reverse))

private theorem step_UL_reverse (s : State) (c : Fin 3) :
    (kmswStep s c).UL.reverse = (kmswStep s c).active ::
      (if c = 0 then s.UL.reverse.tail.tail
        else if c = 1 then s.UL.reverse.tail else s.UL.reverse) := by
  fin_cases c
  · change (kmswStepOfStep s .left).UL.reverse =
      (kmswStepOfStep s .left).active :: s.UL.reverse.tail.tail
    cases hs : s.UL.dropLast.reverse <;>
      simp only [kmswStepOfStep, List.reverse_append, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.singleton_append, List.reverse_reverse,
        ← reverse_dropLast, hs, List.tail_cons, List.tail_nil]
  · change (kmswStepOfStep s .up).UL.reverse =
      (kmswStepOfStep s .up).active :: s.UL.reverse.tail
    simp only [kmswStepOfStep, List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.singleton_append, reverse_dropLast]
  · change (kmswStepOfStep s .down).UL.reverse =
      (kmswStepOfStep s .down).active :: s.UL.reverse
    cases hs : s.UR <;> simp [kmswStepOfStep, hs]

private theorem visitWestStack_old_map (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).UL.reverse.map (kmswStage w (n + 1)).west = CutConverse.westStack w n := by
  apply List.map_congr_left
  intro e he
  exact (kmswStage_endpoints_stable w (Nat.le_succ n)
    (ul_allocated w (List.mem_reverse.mp he))).1

private theorem visitWestStack_down (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2) :
    (CutConverse.westStack w (n + 1)).tail = CutConverse.westStack w n := by
  have hs := step_UL_reverse (kmswStage w n) (w n)
  change (kmswStage w (n + 1)).UL.reverse = act w (n + 1) :: _ at hs
  have h0 : (2 : Fin 3) ≠ 0 := by decide
  have h1 : (2 : Fin 3) ≠ 1 := by decide
  simp only [hc, h0, h1, ↓reduceIte] at hs
  change ((kmswStage w (n + 1)).UL.reverse.map
    (kmswStage w (n + 1)).west).tail = _
  rw [hs]
  simp only [List.map_cons, List.tail_cons]
  exact visitWestStack_old_map w n

private theorem visitWestStack_up (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1) :
    CutConverse.westStack w (n + 1) = CutConverse.westStack w n := by
  have hs := step_UL_reverse (kmswStage w n) (w n)
  change (kmswStage w (n + 1)).UL.reverse = act w (n + 1) :: _ at hs
  have h0 : (1 : Fin 3) ≠ 0 := by decide
  simp only [hc, h0, ↓reduceIte] at hs
  have ht := congrArg List.tail (visitWestStack_old_map w n)
  simp only [← List.map_tail] at ht
  have hw : (kmswStage w (n + 1)).west (act w (n + 1)) =
      (kmswStage w n).west (act w n) := by
    simp [act, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, State.addEdge]
  unfold CutConverse.westStack
  rw [hs, List.map_cons]
  change (kmswStage w (n + 1)).west (act w (n + 1)) :: _ = _
  rw [ht, hw]
  obtain ⟨es, hes⟩ := kmswStage_UL_last w n
  simp [CutConverse.westStack, hes, act]

private theorem visitWestStack_left (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0)
    (hlen : 2 ≤ (kmswStage w n).UL.length) :
    CutConverse.westStack w (n + 1) = (CutConverse.westStack w n).tail := by
  obtain ⟨es, hes⟩ := kmswStage_UL_last w n
  have hnon : es.reverse ≠ [] := by
    intro he
    have hlen' := congrArg List.length he
    rw [hes] at hlen
    simp only [List.length_reverse, List.length_nil] at hlen'
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    omega
  cases he : es.reverse with
  | nil => exact (hnon he).elim
  | cons e rest =>
    have hrev : (kmswStage w n).UL.reverse = act w n :: e :: rest := by
      simp only [hes, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.singleton_append, he, act]
    have hdrop : (kmswStage w n).UL.dropLast.reverse = e :: rest := by
      rw [reverse_dropLast, hrev, List.tail_cons]
    have hs := step_UL_reverse (kmswStage w n) (w n)
    change (kmswStage w (n + 1)).UL.reverse = act w (n + 1) :: _ at hs
    simp only [hc, ↓reduceIte, hrev, List.tail_cons] at hs
    have ht := congrArg (fun xs : List ℕ => xs.tail.tail) (visitWestStack_old_map w n)
    simp only [← List.map_tail, hrev, List.tail_cons] at ht
    have hw : (kmswStage w (n + 1)).west (act w (n + 1)) =
        (kmswStage w n).west e := by
      simp [act, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep,
        hdrop, State.addEdge]
    unfold CutConverse.westStack
    rw [hs, List.map_cons]
    change (kmswStage w (n + 1)).west (act w (n + 1)) :: _ = _
    rw [hw, ht]
    simp [CutConverse.westStack, hrev]

private theorem coord_L_succ (w : ℕ → Fin 3) (n : ℕ) :
    L w (n + 1) = L w n + (RandomWalk.lazyTwoDimensionalStep (w n)).1 :=
  Finset.sum_range_succ _ _

private theorem visitWestStack_excursion (w : ℕ → Fin 3) {a n : ℕ} (han : a ≤ n)
    (habove : ∀ j, a ≤ j → j ≤ n → L w a ≤ L w j) :
    (CutConverse.westStack w n).drop (L w n - L w a).toNat = CutConverse.westStack w a := by
  induction n, han using Nat.le_induction with
  | base => simp
  | succ n han ih =>
    have hprior : ∀ j, a ≤ j → j ≤ n → L w a ≤ L w j :=
      fun j haj hjn => habove j haj (by omega)
    have hi := ih hprior
    have hn := habove n han (by omega)
    have hnext := habove (n + 1) (by omega) (le_refl _)
    have hc := coord_L_succ w n
    by_cases h0 : w n = 0
    · rw [h0, RandomWalk.lazyTwoDimensionalStep_zero] at hc
      change L w (n + 1) = L w n - 1 at hc
      have hlen := kmswStage_UL_length w n
      have hmin := runningMin_le (L w) n a han
      change minL w n ≤ L w a at hmin
      have hlen2 : 2 ≤ (kmswStage w n).UL.length := by omega
      rw [visitWestStack_left w n h0 hlen2]
      have hidx : (L w n - L w a).toNat = (L w (n + 1) - L w a).toNat + 1 := by
        omega
      rw [hidx] at hi
      simpa only [List.drop_tail] using hi
    · by_cases h1 : w n = 1
      · rw [h1, RandomWalk.lazyTwoDimensionalStep_one] at hc
        dsimp at hc
        rw [add_zero] at hc
        rw [visitWestStack_up w n h1, hc]
        exact hi
      · have h2 : w n = 2 := by
          apply Fin.ext
          have := (w n).isLt
          have hn0 : (w n).val ≠ 0 := fun h => h0 (Fin.ext h)
          have hn1 : (w n).val ≠ 1 := fun h => h1 (Fin.ext h)
          omega
        rw [h2, RandomWalk.lazyTwoDimensionalStep_two] at hc
        dsimp at hc
        have hidx : (L w (n + 1) - L w a).toNat = (L w n - L w a).toNat + 1 := by
          omega
        rw [hidx, ← List.drop_tail, visitWestStack_down w n h2]
        exact hi



private theorem visitWestStack_head (w : ℕ → Fin 3) (n : ℕ) :
    CutConverse.westStack w n = activeInitial w n :: (CutConverse.westStack w n).tail := by
  obtain ⟨es, hes⟩ := kmswStage_UL_last w n
  rw [CutConverse.activeInitial_eq]
  simp [CutConverse.westStack, hes, act]


private theorem nodup_drop_head_zero {xs : List ℕ} (hn : xs.Nodup)
    (hne : xs ≠ []) {d : ℕ} (he : (xs.drop d).head? = xs.head?) : d = 0 := by
  cases d with
  | zero => rfl
  | succ d =>
    cases xs with
    | nil => exact (hne rfl).elim
    | cons a rest =>
      have hnot := (List.nodup_cons.mp hn).1
      have hmem : a ∈ rest.drop d := by
        cases hd : rest.drop d with
        | nil => simp [hd] at he
        | cons b bs =>
          have hab : b = a := by simpa [hd] using he
          simp [hab]
      exact (hnot (List.mem_of_mem_drop hmem)).elim

/-- all active-initial visits to the west vertex of an LL record edge, including
exclusion after a deeper minimum. This is not the numbered paper result. -/
theorem kmswLLCreatedEdge_west_visit_iff (w : ℕ → Fin 3) {t : ℕ}
    (ht : 0 < t) (hrec : ∀ j < t, L w t < L w j) (m : ℕ) :
    (kmswStage w m).west (act w m) =
        (kmswStage w t).west (kmswLLCreatedEdge w t) ↔
      L w m = L w t ∧ ∀ j ≤ m, L w t ≤ L w j := by
  constructor
  · intro hv
    have htm : t ≤ m := by
      by_contra h
      exact kmswLLCreatedEdge_west_not_visited_before w ht hrec (by omega) hv
    have heq : activeInitial w m = activeInitial w t := by
      rw [CutConverse.activeInitial_eq, CutConverse.activeInitial_eq, hv,
        kmswLLCreatedEdge_west_eq_act w ht hrec]
    have hmem : activeInitial w t ∈ CutConverse.westStack w m := by
      rw [visitWestStack_head w m, ← heq]
      exact List.mem_cons_self
    have habove := CutConverse.barrier_of_westStack_mem w htm hmem
    have hdrop := visitWestStack_excursion w htm habove
    have hhead : ((CutConverse.westStack w m).drop (L w m - L w t).toNat).head? =
        (CutConverse.westStack w m).head? := by
      rw [hdrop, visitWestStack_head w t, visitWestStack_head w m]
      simp only [List.head?_cons, heq]
    have hzero := nodup_drop_head_zero (CutConverse.westStack_nodup w m)
      (by rw [visitWestStack_head w m]; simp) hhead
    have hle := habove m htm le_rfl
    refine ⟨by omega, ?_⟩
    intro j hjm
    by_cases hjt : j < t
    · exact (hrec j hjt).le
    · exact habove j (by omega) hjm
  · rintro ⟨hlev, habove⟩
    have htm : t ≤ m := by
      by_contra h
      have := hrec m (by omega)
      omega
    exact kmswLLCreatedEdge_west_visit_of_level w ht hrec htm hlev habove

private theorem ur_allocated (w : ℕ → Fin 3) (n : ℕ) :
    ∀ e ∈ (kmswStage w n).UR, e < (kmswStage w n).nextEdge := by
  induction n with
  | zero => simp [kmswStage, kmswInit]
  | succ n ih =>
    have hmono := kmswStage_nextEdge_mono w (Nat.le_succ n)
    change ∀ e ∈ (kmswStep (kmswStage w n) (w n)).UR,
      e < (kmswStep (kmswStage w n) (w n)).nextEdge
    unfold kmswStep
    cases kmswCodeStep (w n) with
    | down =>
      cases hs : (kmswStage w n).UR with
      | nil => simp [kmswStepOfStep, hs, State.addEdge]
      | cons e es =>
        intro f hf
        simp only [kmswStepOfStep, hs] at hf ⊢
        exact ih f (by simp only [hs, List.mem_cons]; exact Or.inr hf)
    | left =>
      cases hs : (kmswStage w n).UL.dropLast.reverse <;>
        simp only [kmswStepOfStep, hs, State.addEdge] at *
      all_goals
        intro e he
        have := ih e he
        omega
    | up =>
      intro e he
      simp only [kmswStepOfStep, State.addEdge, List.mem_cons] at he ⊢
      rcases he with rfl | he
      · omega
      · have := ih e he
        omega

private theorem right_record_creation (w : ℕ → Fin 3) {r : ℕ}
    (hrec : ∀ j ≤ r, R w (r + 1) < R w j) :
    w r = 2 ∧ (kmswStage w r).UR = [] := by
  have hs := coord_R_visit w r
  have hl := hrec r le_rfl
  have hc : w r = 2 := by
    by_cases h0 : w r = 0
    · rw [h0, RandomWalk.lazyTwoDimensionalStep_zero] at hs
      dsimp at hs
      omega
    · by_cases h1 : w r = 1
      · rw [h1, RandomWalk.lazyTwoDimensionalStep_one] at hs
        dsimp at hs
        omega
      · apply Fin.ext
        have := (w r).isLt
        have hn0 : (w r).val ≠ 0 := fun h => h0 (Fin.ext h)
        have hn1 : (w r).val ≠ 1 := fun h => h1 (Fin.ext h)
        omega
  have hmin : minR w r = R w r := by
    obtain ⟨j, hj, he⟩ := runningMin_attained (R w) r
    have hjrec := hrec j hj
    have hle := runningMin_le (R w) r r le_rfl
    change minR w r = R w j at he
    change minR w r ≤ R w r at hle
    rw [hc, RandomWalk.lazyTwoDimensionalStep_two] at hs
    dsimp at hs
    omega
  have hlen := kmswStage_UR_length w r
  have hlen' : (kmswStage w r).UR.length = 0 := by omega
  exact ⟨hc, List.length_eq_zero_iff.mp hlen'⟩

private theorem right_record_data (w : ℕ → Fin 3) {t : ℕ}
    (ht : 0 < t) (hrec : ∀ j < t, R w t < R w j) :
    (kmswStage w t).UR = [] ∧ act w t ∈ (kmswStage w t).LR ∧
      minR w t = R w t := by
  have hmin : minR w t = R w t := by
    obtain ⟨j, hj, he⟩ := runningMin_attained (R w) t
    have hle := runningMin_le (R w) t t le_rfl
    change minR w t = R w j at he
    change minR w t ≤ R w t at hle
    by_cases hjt : j < t
    · have := hrec j hjt
      omega
    · have : j = t := by omega
      simpa [this] using he
  cases t with
  | zero => omega
  | succ r =>
    obtain ⟨hc, hu⟩ := right_record_creation w (fun j hj => hrec j (by omega))
    refine ⟨?_, ?_, hmin⟩
    · simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hu, State.addEdge]
    · simp [act, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hu, State.addEdge]

/-- the terminal endpoint at a positive right record has not been visited earlier. -/
theorem kmswLR_record_east_not_visited_before (w : ℕ → Fin 3) {t m : ℕ}
    (ht : 0 < t) (hrec : ∀ j < t, R w t < R w j) (hm : m < t) :
    (kmswStage w m).east (act w m) ≠ (kmswStage w t).east (act w t) := by
  cases t with
  | zero => omega
  | succ r =>
    obtain ⟨hc, hu⟩ := right_record_creation w (fun j hj => hrec j (by omega))
    have hv : (kmswStage w (r + 1)).east (act w (r + 1)) =
        (kmswStage w r).nextVertex := by
      simp [act, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hu, State.addEdge]
    rw [hv]
    exact Nat.ne_of_lt (((CutConverse.endpoint_bound w m) _
      (act_lt_nextEdge w le_rfl)).2.trans_le
        (CutConverse.nextVertex_mono w (by omega : m ≤ r)))
private theorem pending_ne_nil (s : State) : CutConverse.pendingVertices s ≠ [] := by
  simp [CutConverse.pendingVertices]

private theorem nonrecord_tip (w : ℕ → Fin 3) (n : ℕ)
    (hreset : ¬ (w n = 2 ∧ (kmswStage w n).UR = [])) :
    (kmswStage w (n + 1)).LR = (kmswStage w n).LR ∧
      (CutConverse.pendingVertices (kmswStage w (n + 1))).getLast? =
        (CutConverse.pendingVertices (kmswStage w n)).getLast? := by
  let s := kmswStage w n
  let t := kmswStage w (n + 1)
  have hmaps : s.UR.map t.east = s.UR.map s.east := by
    apply List.map_congr_left
    intro e he
    exact (kmswStage_endpoints_stable w (Nat.le_succ n) (ur_allocated w n e he)).2
  change t.LR = s.LR ∧ _
  generalize hw : w n = c
  fin_cases c
  · have hp : CutConverse.pendingVertices t = CutConverse.pendingVertices s := by
      have hUR : t.UR = s.UR := by
        change (kmswStep s (w n)).UR = _
        rw [hw]
        cases hs : s.UL.dropLast.reverse <;>
          simp [kmswStep, kmswCodeStep, kmswStepOfStep, hs, State.addEdge]
      have hEast : t.east t.active = s.east s.active := by
        change (kmswStep s (w n)).east (kmswStep s (w n)).active = _
        rw [hw]
        cases hs : s.UL.dropLast.reverse <;>
          simp [kmswStep, kmswCodeStep, kmswStepOfStep, hs, State.addEdge]
      simp only [CutConverse.pendingVertices, hUR, hEast, hmaps]
    refine ⟨?_, congrArg List.getLast? hp⟩
    change (kmswStep s (w n)).LR = _
    rw [hw]
    cases hs : s.UL.dropLast.reverse <;>
      simp [kmswStep, kmswCodeStep, kmswStepOfStep, hs, State.addEdge]
  · have hUR : t.UR = (s.nextEdge + 1) :: s.UR := by
      change (kmswStep s (w n)).UR = _
      simp [hw, kmswStep, kmswCodeStep, kmswStepOfStep]
    have hnew : t.east (s.nextEdge + 1) = s.east s.active ∧
        t.east t.active = s.nextVertex := by
      change (kmswStep s (w n)).east _ = _ ∧
        (kmswStep s (w n)).east (kmswStep s (w n)).active = _
      simp [hw, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
    have hp : CutConverse.pendingVertices t = s.nextVertex :: CutConverse.pendingVertices s := by
      unfold CutConverse.pendingVertices
      rw [hUR, List.map_cons, hnew.1, hnew.2, hmaps]
    refine ⟨?_, ?_⟩
    · change (kmswStep s (w n)).LR = _
      rw [hw]; rfl
    · rw [hp, List.getLast?_cons_of_ne_nil (pending_ne_nil s)]
  · have hu : s.UR ≠ [] := fun hu => hreset ⟨hw, hu⟩
    cases hs : s.UR with
    | nil => exact (hu hs).elim
    | cons e es =>
      change (kmswStep s (w n)).LR = s.LR ∧
        (CutConverse.pendingVertices (kmswStep s (w n))).getLast? = _
      change (kmswStep s (w n)).LR = s.LR ∧
        (CutConverse.pendingVertices (kmswStep s (w n))).getLast? = (CutConverse.pendingVertices s).getLast?
      rw [hw]
      simp [CutConverse.pendingVertices, kmswStep, kmswCodeStep, kmswStepOfStep, hs]



private theorem right_terminal_min_iff (w : ℕ → Fin 3) {t : ℕ}
    (ht : 0 < t) (hrec : ∀ j < t, R w t < R w j) {m : ℕ} (htm : t ≤ m) :
    (CutConverse.pendingVertices (kmswStage w m)).getLast? =
        some ((kmswStage w t).east (act w t)) ↔ minR w m = R w t := by
  induction m, htm using Nat.le_induction with
  | base =>
    obtain ⟨hu, _, hmin⟩ := right_record_data w ht hrec
    simp [CutConverse.pendingVertices, hu, act, hmin]
  | succ m htm ih =>
    by_cases hreset : w m = 2 ∧ (kmswStage w m).UR = []
    · obtain ⟨hc, hu⟩ := hreset
      have htip : (CutConverse.pendingVertices (kmswStage w (m + 1))).getLast? =
          some (kmswStage w m).nextVertex := by
        simp [CutConverse.pendingVertices, kmswStage, kmswStep, kmswCodeStep,
          hc, kmswStepOfStep, hu, State.addEdge]
      have hbound : (kmswStage w t).east (act w t) < (kmswStage w m).nextVertex :=
        ((CutConverse.endpoint_bound w t) _ (act_lt_nextEdge w le_rfl)).2.trans_le
          (CutConverse.nextVertex_mono w htm)
      have hmin := runningMin_le (R w) m t htm
      change minR w m ≤ R w t at hmin
      have hlen := kmswStage_UR_length w m
      rw [hu] at hlen
      simp only [List.length_nil, Nat.cast_zero] at hlen
      have hs := coord_R_visit w m
      rw [hc, RandomWalk.lazyTwoDimensionalStep_two] at hs
      dsimp at hs
      have hnext : minR w (m + 1) = min (minR w m) (R w (m + 1)) := rfl
      have hlow : minR w (m + 1) < R w t := by
        have := min_le_right (minR w m) (R w (m + 1))
        rw [← hnext] at this
        omega
      rw [htip]
      constructor
      · intro he
        have := Option.some.inj he
        omega
      · intro he
        omega
    · obtain ⟨hLR, htip⟩ := nonrecord_tip w m hreset
      have hprev := kmswStage_LR_length w m
      have hnext := kmswStage_LR_length w (m + 1)
      rw [hLR] at hnext
      have hmin : minR w (m + 1) = minR w m := by omega
      rw [htip, hmin]
      exact ih

/-- all visits to a positive LR record's terminal endpoint are exactly the
returns to its level before a deeper minimum. Not the numbered paper result. -/
theorem kmswLR_record_east_visit_iff (w : ℕ → Fin 3) {t : ℕ}
    (ht : 0 < t) (hrec : ∀ j < t, R w t < R w j) (m : ℕ) :
    (kmswStage w m).east (act w m) = (kmswStage w t).east (act w t) ↔
      R w m = R w t ∧ ∀ j ≤ m, R w t ≤ R w j := by
  obtain ⟨_, hLRt, _⟩ := right_record_data w ht hrec
  have hstable : edgeEast w (act w t) = (kmswStage w t).east (act w t) :=
    (edge_endpoints_eq w (act_lt_nextEdge w (le_refl t))).2.symm
  constructor
  · intro hv
    have htm : t ≤ m := by
      by_contra h
      exact kmswLR_record_east_not_visited_before w ht hrec (by omega) hv
    have hu : (kmswStage w m).UR = [] := by
      cases he : (kmswStage w m).UR with
      | nil => rfl
      | cons e es =>
        have hmem : (kmswStage w t).east (act w t) ∈
            (CutConverse.pendingVertices (kmswStage w m)).dropLast := by
          rw [← hv]
          simp only [CutConverse.pendingVertices, he, List.map_cons,
            List.dropLast_cons_cons, act]
          exact List.mem_cons_self
        have hne := (CutConverse.pending_interior_ne_LR_endpoints w m t hmem hLRt).2
        exact (hne hstable.symm).elim
    have htip : (CutConverse.pendingVertices (kmswStage w m)).getLast? =
        some ((kmswStage w t).east (act w t)) := by
      simpa [CutConverse.pendingVertices, hu, act] using congrArg some hv
    have hmin := (right_terminal_min_iff w ht hrec htm).1 htip
    have hlen := kmswStage_UR_length w m
    rw [hu] at hlen
    simp only [List.length_nil, Nat.cast_zero] at hlen
    refine ⟨by omega, ?_⟩
    intro j hj
    have := runningMin_le (R w) m j hj
    change minR w m ≤ R w j at this
    omega
  · rintro ⟨hlev, habove⟩
    have htm : t ≤ m := by
      by_contra h
      have := hrec m (by omega)
      omega
    have hmin : minR w m = R w t := by
      obtain ⟨j, hj, he⟩ := runningMin_attained (R w) m
      have hl := habove j hj
      have hu := runningMin_le (R w) m m le_rfl
      change minR w m = R w j at he
      change minR w m ≤ R w m at hu
      omega
    have hlen := kmswStage_UR_length w m
    have hu : (kmswStage w m).UR = [] := by
      apply List.length_eq_zero_iff.mp
      omega
    have htip := (right_terminal_min_iff w ht hrec htm).2 hmin
    simpa [CutConverse.pendingVertices, hu, act] using htip


private theorem first_negative_hit_record (p : ℕ → ℤ) (hp0 : p 0 = 0)
    (hstep : ∀ i, |p (i + 1) - p i| ≤ 1) (k : ℕ) (hk : 1 ≤ k)
    (hhit : ∃ t, p t = -(k : ℤ)) :
    0 < Nat.find hhit ∧ ∀ j < Nat.find hhit, p (Nat.find hhit) < p j := by
  have h := (strict_running_minimum_iff_first_hit p hp0 hstep
    (Nat.find hhit) (Nat.find hhit) (-(k : ℤ)) (by omega) hhit).2
      ⟨le_rfl, Nat.find_spec hhit, rfl⟩
  have hmem := Finset.mem_filter.mp h.1
  exact ⟨(Finset.mem_Icc.mp hmem.1).1, hmem.2⟩

private theorem L_visit_step_bound (w : ℕ → Fin 3) (i : ℕ) :
    |L w (i + 1) - L w i| ≤ 1 := by
  rw [coord_L_visit]
  generalize hw : w i = c
  fin_cases c <;> simp [RandomWalk.lazyTwoDimensionalStep]

private theorem R_visit_step_bound (w : ℕ → Fin 3) (i : ℕ) :
    |R w (i + 1) - R w i| ≤ 1 := by
  rw [coord_R_visit]
  generalize hw : w i = c
  fin_cases c <;> simp [RandomWalk.lazyTwoDimensionalStep]

/-- At the first hit of `-k`, the new missing LL edge's west endpoint first
becomes an active initial vertex; its complete visit set is the stated
level-and-prefix-barrier condition. Applies to every finite prefix containing
the hit. This helper does not count as the numbered paper result. -/
theorem kmswLL_first_hit_vertex_visits (w : ℕ → Fin 3) (k : ℕ) (hk : 1 ≤ k)
    (hhit : ∃ t, L w t = -(k : ℤ)) :
    let t := Nat.find hhit
    let v := (kmswStage w t).west (kmswLLCreatedEdge w t)
    (kmswStage w t).west (act w t) = v ∧
      (∀ m, (kmswStage w m).west (act w m) = v ↔
        L w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ L w j) ∧
      IsLeast {m | (kmswStage w m).west (act w m) = v} t := by
  dsimp only
  obtain ⟨ht, hrec⟩ := first_negative_hit_record (L w) (by simp [L])
    (L_visit_step_bound w) k hk hhit
  have hlevel := Nat.find_spec hhit
  have heq := (kmswLLCreatedEdge_west_eq_act w ht hrec).symm
  have hvisits (m : ℕ) :
      (kmswStage w m).west (act w m) =
          (kmswStage w (Nat.find hhit)).west (kmswLLCreatedEdge w (Nat.find hhit)) ↔
        L w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ L w j := by
    simpa only [hlevel] using kmswLLCreatedEdge_west_visit_iff w ht hrec m
  refine ⟨heq, hvisits, heq, ?_⟩
  intro m hm
  exact Nat.find_min' hhit ((hvisits m).1 hm).1

/-- The terminal endpoint at the first hit of `-k` first becomes an active
terminal vertex at that time, with exactly the stated subsequent visits.
Applies to every finite prefix containing the hit. This helper does not
count as the numbered paper result. -/
theorem kmswLR_first_hit_vertex_visits (w : ℕ → Fin 3) (k : ℕ) (hk : 1 ≤ k)
    (hhit : ∃ t, R w t = -(k : ℤ)) :
    let t := Nat.find hhit
    let u := (kmswStage w t).east (act w t)
    (kmswStage w t).east (act w t) = u ∧
      (∀ m, (kmswStage w m).east (act w m) = u ↔
        R w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ R w j) ∧
      IsLeast {m | (kmswStage w m).east (act w m) = u} t := by
  dsimp only
  obtain ⟨ht, hrec⟩ := first_negative_hit_record (R w) (by simp [R])
    (R_visit_step_bound w) k hk hhit
  have hlevel := Nat.find_spec hhit
  have hvisits (m : ℕ) :
      (kmswStage w m).east (act w m) = (kmswStage w (Nat.find hhit)).east (act w (Nat.find hhit)) ↔
        R w m = -(k : ℤ) ∧ ∀ j ≤ m, -(k : ℤ) ≤ R w j := by
    simpa only [hlevel] using kmswLR_record_east_visit_iff w ht hrec m
  refine ⟨rfl, hvisits, rfl, ?_⟩
  intro m hm
  exact Nat.find_min' hhit ((hvisits m).1 hm).1

end DirectedDistances.KMSW
