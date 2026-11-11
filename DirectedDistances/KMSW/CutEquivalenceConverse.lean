module

public import DirectedDistances.KMSW.CutEquivalence
import DirectedDistances.KMSW.WalkRecordCounts
import DirectedDistances.KMSW.StageIncidence
import Mathlib.Order.Interval.Set.Infinite

/-! # Converse boundary bookkeeping -/

public section
namespace DirectedDistances.KMSW
open scoped Classical
namespace CutConverse

 
theorem allocation_count (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).nextEdge = n + (kmswStage w n).UR.length +
      (kmswStage w n).LL.length + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (kmswStep (kmswStage w n) (w n)).nextEdge =
      n + 1 + (kmswStep (kmswStage w n) (w n)).UR.length +
        (kmswStep (kmswStage w n) (w n)).LL.length + 1
    unfold kmswStep
    cases kmswCodeStep (w n) with
    | down =>
      cases hs : (kmswStage w n).UR <;>
        simp only [kmswStepOfStep, hs, State.addEdge, List.length_cons,
          List.length_nil] at * <;> omega
    | left =>
      cases hs : (kmswStage w n).UL.dropLast.reverse <;>
        simp only [kmswStepOfStep, hs, State.addEdge, List.length_cons] <;> omega
    | up =>
      simp only [kmswStepOfStep, State.addEdge, List.length_cons]
      omega

/-- Stable and stage active initial endpoints agree (`def-kmsw`, -/
theorem activeInitial_eq (w : ℕ → Fin 3) (n : ℕ) :
    activeInitial w n = (kmswStage w n).west (act w n) :=
  (edge_endpoints_eq w (act_lt_nextEdge w (le_refl n))).1.symm

private theorem ul_allocated (w : ℕ → Fin 3) {n e : ℕ}
    (he : e ∈ (kmswStage w n).UL) : e < (kmswStage w n).nextEdge := by
  rw [kmswStage_UL_eq] at he
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp he
  have hmn := List.mem_range.mp (List.mem_filter.mp hm).1
  exact act_lt_nextEdge w (by omega)

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

/-- Every allocated endpoint lies below the vertex counter (`def-kmsw`, -/
@[expose] def EndpointBound (s : State) (V : ℕ) : Prop :=
  ∀ e < s.nextEdge, s.west e < V ∧ s.east e < V

private theorem EndpointBound.addEdge {s : State} {V : ℕ}
    (h : EndpointBound s V) {a b : ℕ} (ha : a < V) (hb : b < V) (p : Bool) :
    EndpointBound (s.addEdge a b p) V := by
  intro e he
  by_cases heq : e = s.nextEdge
  · subst e
    simpa only [State.addEdge, ↓reduceIte] using And.intro ha hb
  · have he' : e < s.nextEdge := by change e < s.nextEdge + 1 at he; omega
    simpa only [State.addEdge, heq, ↓reduceIte] using h e he'

private theorem EndpointBound.mono {s : State} {V W : ℕ}
    (h : EndpointBound s V) (hVW : V ≤ W) : EndpointBound s W := by
  intro e he
  exact ⟨(h e he).1.trans_le hVW, (h e he).2.trans_le hVW⟩

/-- Endpoint bounds at every stage of `def-kmsw`, -/
theorem endpoint_bound (w : ℕ → Fin 3) (n : ℕ) :
    EndpointBound (kmswStage w n) (kmswStage w n).nextVertex := by
  induction n with
  | zero => intro e he; exact ⟨by change 0 < 2; omega, by change 1 < 2; omega⟩
  | succ n ih =>
    have ha := ih _ (act_lt_nextEdge w (le_refl n))
    change EndpointBound (kmswStep (kmswStage w n) (w n))
      (kmswStep (kmswStage w n) (w n)).nextVertex
    unfold kmswStep
    cases kmswCodeStep (w n) with
    | down =>
      cases hs : (kmswStage w n).UR with
      | cons e es => simpa only [EndpointBound, kmswStepOfStep, hs] using ih
      | nil =>
        simpa only [EndpointBound, kmswStepOfStep, hs, State.addEdge, act,
          Nat.succ_eq_add_one] using
          (ih.mono (Nat.le_succ _)).addEdge (ha.2.trans_le (Nat.le_succ _))
            (Nat.lt_succ_self _) true
    | left =>
      cases hs : (kmswStage w n).UL.dropLast.reverse with
      | cons e es =>
        have he : e ∈ (kmswStage w n).UL :=
          List.dropLast_subset _ (List.mem_reverse.mp (by rw [hs]; simp))
        simpa only [EndpointBound, kmswStepOfStep, hs, State.addEdge, act,
          Nat.succ_eq_add_one] using
          ih.addEdge (ih e (ul_allocated w he)).1 ha.2 true
      | nil =>
        have hV := Nat.le_succ (kmswStage w n).nextVertex
        have h1 := (ih.mono hV).addEdge (Nat.lt_succ_self _) (ha.2.trans_le hV) true
        simpa [EndpointBound, kmswStepOfStep, hs, State.addEdge, act] using
          h1.addEdge (Nat.lt_succ_self _) (ha.1.trans_le hV) false
    | up =>
      have hV := Nat.le_succ (kmswStage w n).nextVertex
      have h1 := (ih.mono hV).addEdge (ha.1.trans_le hV) (Nat.lt_succ_self _) true
      exact h1.addEdge (Nat.lt_succ_self _) (ha.2.trans_le hV) false

/-- Ordered vertices from the active terminal endpoint along UR (`def-kmsw`, -/
@[expose] def pendingVertices (s : State) : List ℕ :=
  s.east s.active :: s.UR.map s.east



@[expose] def FrontierCoherent (s : State) : Prop :=
  s.UR.map s.west = (pendingVertices s).dropLast

private inductive FrontierMove (s t : State) : Prop
  | same (hp : pendingVertices t = pendingVertices s)
      (ht : t.west t.active = s.nextVertex ∨
        ∃ e ∈ s.UL, t.west t.active = s.west e)
  | push (hp : pendingVertices t = s.nextVertex :: pendingVertices s)
      (ht : t.west t.active = s.west s.active)
  | pop (hp : pendingVertices s = t.west t.active :: pendingVertices t)
  | reset (hp : pendingVertices t = [s.nextVertex])
      (ht : t.west t.active = s.east s.active)

private theorem frontier_step (w : ℕ → Fin 3) (n : ℕ)
    (hcoh : FrontierCoherent (kmswStage w n)) :
    FrontierCoherent (kmswStage w (n + 1)) ∧
      FrontierMove (kmswStage w n) (kmswStage w (n + 1)) := by
  let s := kmswStage w n
  let t := kmswStage w (n + 1)
  have hmaps : s.UR.map t.west = s.UR.map s.west ∧
      s.UR.map t.east = s.UR.map s.east := by
    constructor <;> apply List.map_congr_left <;> intro e he
    · exact (kmswStage_endpoints_stable w (Nat.le_succ n) (ur_allocated w n e he)).1
    · exact (kmswStage_endpoints_stable w (Nat.le_succ n) (ur_allocated w n e he)).2
  change FrontierCoherent t ∧ FrontierMove s t
  change s.UR.map s.west = (pendingVertices s).dropLast at hcoh
  by_cases h0 : w n = 0
  · have hUR : t.UR = s.UR := by
      change (kmswStep s (w n)).UR = _
      rw [h0]
      cases hs : s.UL.dropLast.reverse <;>
        simp [kmswStep, kmswCodeStep, kmswStepOfStep, hs, State.addEdge]
    have hEast : t.east t.active = s.east s.active := by
      change (kmswStep s (w n)).east (kmswStep s (w n)).active = _
      rw [h0]
      cases hs : s.UL.dropLast.reverse <;>
        simp [kmswStep, kmswCodeStep, kmswStepOfStep, hs, State.addEdge]
    have hp : pendingVertices t = pendingVertices s := by
      unfold pendingVertices
      rw [hUR, hEast, hmaps.2]
    refine ⟨?_, FrontierMove.same hp ?_⟩
    · change t.UR.map t.west = _
      rw [hUR, hmaps.1, hp]
      exact hcoh
    · change (kmswStep s (w n)).west (kmswStep s (w n)).active = s.nextVertex ∨ _
      rw [h0]
      cases hs : s.UL.dropLast.reverse with
      | nil =>
        exact Or.inl (by simp [kmswStep, kmswCodeStep, kmswStepOfStep, hs, State.addEdge])
      | cons e es =>
        refine Or.inr ⟨e, ?_, ?_⟩
        · exact List.dropLast_subset _ (List.mem_reverse.mp (by rw [hs]; simp))
        · change (kmswStep s (w n)).west (kmswStep s (w n)).active = s.west e
          simp [h0, kmswStep, kmswCodeStep, kmswStepOfStep, hs, State.addEdge]
  · by_cases h1 : w n = 1
    · have hUR : t.UR = (s.nextEdge + 1) :: s.UR := by
        change (kmswStep s (w n)).UR = _
        simp [h1, kmswStep, kmswCodeStep, kmswStepOfStep]
      have hnew : t.west (s.nextEdge + 1) = s.nextVertex ∧
          t.east (s.nextEdge + 1) = s.east s.active ∧
          t.east t.active = s.nextVertex ∧ t.west t.active = s.west s.active := by
        change (kmswStep s (w n)).west _ = _ ∧
          (kmswStep s (w n)).east _ = _ ∧
          (kmswStep s (w n)).east (kmswStep s (w n)).active = _ ∧
          (kmswStep s (w n)).west (kmswStep s (w n)).active = _
        simp [h1, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
      have hp : pendingVertices t = s.nextVertex :: pendingVertices s := by
        unfold pendingVertices
        rw [hUR, List.map_cons, hnew.2.2.1, hnew.2.1, hmaps.2]
      refine ⟨?_, FrontierMove.push hp hnew.2.2.2⟩
      change t.UR.map t.west = _
      rw [hUR, List.map_cons, hnew.1, hmaps.1, hp]
      simpa only [pendingVertices, List.dropLast_cons_cons] using congrArg (List.cons s.nextVertex) hcoh
    · have h2 : w n = 2 := by
        apply Fin.ext
        have := (w n).isLt
        have hn0 : (w n).val ≠ 0 := fun he => h0 (Fin.ext he)
        have hn1 : (w n).val ≠ 1 := fun he => h1 (Fin.ext he)
        omega
      cases hs : s.UR with
      | nil =>
        have hUR : t.UR = [] := by
          change (kmswStep s (w n)).UR = _
          simp [h2, kmswStep, kmswCodeStep, kmswStepOfStep, hs, State.addEdge]
        have hnew : t.east t.active = s.nextVertex ∧
            t.west t.active = s.east s.active := by
          change (kmswStep s (w n)).east (kmswStep s (w n)).active = _ ∧
            (kmswStep s (w n)).west (kmswStep s (w n)).active = _
          simp [h2, kmswStep, kmswCodeStep, kmswStepOfStep, hs, State.addEdge]
        have hp : pendingVertices t = [s.nextVertex] := by simp [pendingVertices, hUR, hnew.1]
        exact ⟨by simp [FrontierCoherent, hUR, hp], FrontierMove.reset hp hnew.2⟩
      | cons e es =>
        have hold : s.west e = s.east s.active ∧
            es.map s.west = (s.east e :: es.map s.east).dropLast := by
          simpa only [pendingVertices, hs, List.map_cons, List.dropLast_cons_cons,
            List.cons.injEq] using hcoh
        have ht : t.UR = es ∧ t.west = s.west ∧ t.east = s.east ∧ t.active = e := by
          change (kmswStep s (w n)).UR = _ ∧ (kmswStep s (w n)).west = _ ∧
            (kmswStep s (w n)).east = _ ∧ (kmswStep s (w n)).active = _
          simp [h2, kmswStep, kmswCodeStep, kmswStepOfStep, hs]
        refine ⟨?_, FrontierMove.pop ?_⟩
        · simpa only [FrontierCoherent, pendingVertices, ht.1, ht.2.1,
            ht.2.2.1, ht.2.2.2] using hold.2
        · simp only [pendingVertices, hs, List.map_cons, ht.1, ht.2.1,
            ht.2.2.1, ht.2.2.2, hold.1]

private theorem initial_lt_nextVertex (w : ℕ → Fin 3) {m n : ℕ} (hmn : m ≤ n) :
    activeInitial w m < (kmswStage w n).nextVertex := by
  have he := act_lt_nextEdge w hmn
  have hb := (endpoint_bound w n) _ he
  rw [(edge_endpoints_eq w he).1] at hb
  exact hb.1

private theorem pending_lt_nextVertex (w : ℕ → Fin 3) (n : ℕ)
    {v : ℕ} (hv : v ∈ pendingVertices (kmswStage w n)) :
    v < (kmswStage w n).nextVertex := by
  simp only [pendingVertices, List.mem_cons, List.mem_map] at hv
  rcases hv with rfl | ⟨e, he, rfl⟩
  · exact (endpoint_bound w n) _ (act_lt_nextEdge w (le_refl n)) |>.2
  · exact (endpoint_bound w n) e (ur_allocated w n e he) |>.2

private theorem ul_west_visited (w : ℕ → Fin 3) {n e : ℕ}
    (he : e ∈ (kmswStage w n).UL) :
    ∃ m ≤ n, (kmswStage w n).west e = activeInitial w m := by
  rw [kmswStage_UL_eq] at he
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp he
  have hmn : m ≤ n := by have := List.mem_range.mp (List.mem_filter.mp hm).1; omega
  exact ⟨m, hmn, (edge_endpoints_eq w (act_lt_nextEdge w hmn)).1⟩

/-- UR incidence, vertex distinctness, and exclusion of all previously -/
theorem frontier_history (w : ℕ → Fin 3) (n : ℕ) :
    FrontierCoherent (kmswStage w n) ∧
      (pendingVertices (kmswStage w n)).Nodup ∧
      ∀ m ≤ n, activeInitial w m ∉ pendingVertices (kmswStage w n) := by
  induction n with
  | zero =>
    refine ⟨rfl, by simp [pendingVertices, kmswStage, kmswInit], ?_⟩
    intro m hm
    have : m = 0 := by omega
    subst m
    simp [pendingVertices, activeInitial, edgeWest, act, kmswStage, kmswInit]
  | succ n ih =>
    obtain ⟨hc, hmoves⟩ := frontier_step w n ih.1
    refine ⟨hc, ?_⟩
    let s := kmswStage w n
    let t := kmswStage w (n + 1)
    have hn : activeInitial w (n + 1) = t.west t.active := activeInitial_eq w (n + 1)
    have hist : ∀ m ≤ n, activeInitial w m ∉ pendingVertices s := ih.2.2
    have hdup : (pendingVertices s).Nodup := ih.2.1
    change (pendingVertices t).Nodup ∧ ∀ m ≤ n + 1, activeInitial w m ∉ pendingVertices t
    cases hmoves with
    | same hp ht =>
      constructor
      · rw [hp]; exact hdup
      · intro m hm hv
        rw [hp] at hv
        by_cases hmn : m ≤ n
        · exact hist m hmn hv
        · have hm : m = n + 1 := by omega
          subst m
          rcases ht with ht | ⟨e, he, ht⟩
          · have hb := pending_lt_nextVertex w n hv
            rw [hn, ht] at hb
            exact Nat.lt_irrefl _ hb
          · obtain ⟨k, hkn, hk⟩ := ul_west_visited w he
            have heq : activeInitial w (n + 1) = activeInitial w k := hn.trans (ht.trans hk)
            rw [heq] at hv
            exact hist k hkn hv
    | push hp ht =>
      have hfresh : s.nextVertex ∉ pendingVertices s := by
        intro hv
        exact Nat.lt_irrefl _ (pending_lt_nextVertex w n hv)
      have hnew : activeInitial w (n + 1) = activeInitial w n :=
        hn.trans (ht.trans (activeInitial_eq w n).symm)
      constructor
      · rw [hp]; exact List.nodup_cons.mpr ⟨hfresh, hdup⟩
      · intro m hm hv
        rw [hp] at hv
        have hb : activeInitial w m < s.nextVertex := by
          by_cases hmn : m ≤ n
          · exact initial_lt_nextVertex w hmn
          · have hm : m = n + 1 := by omega
            subst m
            rw [hnew]
            exact initial_lt_nextVertex w (le_refl n)
        rcases List.mem_cons.mp hv with hv | hv
        · exact (Nat.ne_of_lt hb) hv
        · by_cases hmn : m ≤ n
          · exact hist m hmn hv
          · have hm : m = n + 1 := by omega
            subst m
            rw [hnew] at hv
            exact hist n (le_refl n) hv
    | pop hp =>
      rw [hp] at hdup
      obtain ⟨hfresh, hdup⟩ := List.nodup_cons.mp hdup
      refine ⟨hdup, ?_⟩
      intro m hm hv
      by_cases hmn : m ≤ n
      · apply hist m hmn
        rw [hp]
        exact List.mem_cons_of_mem _ hv
      · have hm : m = n + 1 := by omega
        subst m
        rw [hn] at hv
        exact hfresh hv
    | reset hp ht =>
      constructor
      · rw [hp]; exact List.nodup_singleton _
      · intro m hm hv
        rw [hp, List.mem_singleton] at hv
        by_cases hmn : m ≤ n
        · have hb := initial_lt_nextVertex w hmn
          exact (Nat.ne_of_lt hb) hv
        · have hm : m = n + 1 := by omega
          subst m
          have hb := (endpoint_bound w n) _ (act_lt_nextEdge w (le_refl n)) |>.2
          have he : activeInitial w (n + 1) = (kmswStage w n).east (act w n) :=
            hn.trans ht
          rw [he] at hv
          exact (Nat.ne_of_lt hb) hv




theorem nextEdge_ge_time_add_UR (w : ℕ → Fin 3) (n : ℕ) :
    n + 1 + (kmswStage w n).UR.length ≤ (kmswStage w n).nextEdge := by
  have := allocation_count w n
  omega

private theorem lr_allocated (w : ℕ → Fin 3) {n e : ℕ}
    (he : e ∈ (kmswStage w n).LR) : e < (kmswStage w n).nextEdge := by
  rw [kmswStage_LR_eq] at he
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp he
  have hmn := List.mem_range.mp (List.mem_filter.mp hm).1
  exact act_lt_nextEdge w (by omega)

private theorem record_of_down_empty (w : ℕ → Fin 3) (n : ℕ)
    (hw : w n = 2) (hu : (kmswStage w n).UR = []) :
    ∀ j < n + 1, R w (n + 1) ≤ R w j - 1 := by
  have hc : R w (n + 1) = R w n +
      (RandomWalk.lazyTwoDimensionalStep (w n)).2 := Finset.sum_range_succ _ _
  have hlen := kmswStage_UR_length w n
  rw [hu] at hlen
  rw [hw, RandomWalk.lazyTwoDimensionalStep_two] at hc
  simp only [List.length_nil, Nat.cast_zero] at hlen
  intro j hj
  have hmin := runningMin_le (R w) n j (by omega)
  change minR w n ≤ R w j at hmin
  dsimp at hc
  omega

private theorem pending_ne_nil (s : State) : pendingVertices s ≠ [] := by
  simp [pendingVertices]

private theorem nonrecord_tip (w : ℕ → Fin 3) (n : ℕ)
    (hreset : ¬ (w n = 2 ∧ (kmswStage w n).UR = [])) :
    (kmswStage w (n + 1)).LR = (kmswStage w n).LR ∧
      (pendingVertices (kmswStage w (n + 1))).getLast? =
        (pendingVertices (kmswStage w n)).getLast? := by
  let s := kmswStage w n
  let t := kmswStage w (n + 1)
  have hmaps : s.UR.map t.east = s.UR.map s.east := by
    apply List.map_congr_left
    intro e he
    exact (kmswStage_endpoints_stable w (Nat.le_succ n) (ur_allocated w n e he)).2
  change t.LR = s.LR ∧ _
  generalize hw : w n = c
  fin_cases c
  · have hp : pendingVertices t = pendingVertices s := by
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
      simp only [pendingVertices, hUR, hEast, hmaps]
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
    have hp : pendingVertices t = s.nextVertex :: pendingVertices s := by
      unfold pendingVertices
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
        (pendingVertices (kmswStep s (w n))).getLast? = _
      change (kmswStep s (w n)).LR = s.LR ∧
        (pendingVertices (kmswStep s (w n))).getLast? = (pendingVertices s).getLast?
      rw [hw]
      simp [pendingVertices, kmswStep, kmswCodeStep, kmswStepOfStep, hs]

/-- A lower-right terminal endpoint is a past right-record initial vertex -/
theorem lr_east_history (w : ℕ → Fin 3) (n : ℕ) :
    ∀ e ∈ (kmswStage w n).LR,
      (∃ k ≤ n, (∀ i < k, R w k ≤ R w i - 1) ∧
        (kmswStage w n).east e = activeInitial w k) ∨
      (pendingVertices (kmswStage w n)).getLast? = some ((kmswStage w n).east e) := by
  induction n with
  | zero =>
    intro e he
    have he : e = 0 := by simpa [kmswStage, kmswInit] using he
    subst e
    exact Or.inr rfl
  | succ n ih =>
    let s := kmswStage w n
    let t := kmswStage w (n + 1)
    have hstable (e : ℕ) (he : e ∈ s.LR) : t.east e = s.east e :=
      (kmswStage_endpoints_stable w (Nat.le_succ n) (lr_allocated w he)).2
    change ∀ e ∈ t.LR, _
    by_cases hreset : w n = 2 ∧ s.UR = []
    · obtain ⟨hw, hu⟩ := hreset
      have hLR : t.LR = s.LR ++ [s.nextEdge] := by
        change (kmswStep s (w n)).LR = _
        simp [hw, kmswStep, kmswCodeStep, kmswStepOfStep, hu, State.addEdge]
      have hnew : t.east s.nextEdge = s.nextVertex ∧
          activeInitial w (n + 1) = s.east s.active ∧
          pendingVertices t = [s.nextVertex] := by
        rw [activeInitial_eq]
        change t.east s.nextEdge = _ ∧ t.west t.active = _ ∧ _
        have ht : t = kmswStep s (w n) := rfl
        rw [ht, hw]
        simp [pendingVertices, kmswStep, kmswCodeStep,
          kmswStepOfStep, hu, State.addEdge]
      intro e he
      rw [hLR, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · rcases ih e he with ⟨k, hk, hr, hv⟩ | hv
        · exact Or.inl ⟨k, by omega, hr, (hstable e he).trans hv⟩
        · have heast : s.east e = s.east s.active := by
            change (s.east s.active :: s.UR.map s.east).getLast? = some (s.east e) at hv
            rw [hu] at hv
            exact (Option.some.inj hv).symm
          exact Or.inl ⟨n + 1, le_refl _, record_of_down_empty w n hw hu,
            (hstable e he).trans (heast.trans hnew.2.1.symm)⟩
      · exact Or.inr (by rw [hnew.2.2, hnew.1]; rfl)
    · obtain ⟨hLR, htip⟩ := nonrecord_tip w n hreset
      intro e he
      rw [hLR] at he
      rcases ih e he with ⟨k, hk, hr, hv⟩ | hv
      · exact Or.inl ⟨k, by omega, hr, (hstable e he).trans hv⟩
      · exact Or.inr (by rw [htip, hstable e he]; exact hv)

private theorem record_time_eq (w : ℕ → Fin 3) {n k : ℕ}
    (hk : ∀ i < k, R w k ≤ R w i - 1)
    (hfirst : ∀ j < n, activeInitial w j ≠ activeInitial w n)
    (heq : activeInitial w k = activeInitial w n) : k = n := by
  rcases lt_trichotomy k n with h | h | h
  · exact (hfirst k h heq).elim
  · exact h
  · exact (activeInitial_ne_of_right_record w k hk n h heq.symm).elim


private theorem act_present (w : ℕ → Fin 3) {m n : ℕ} (hmn : m ≤ n) :
    (kmswStage w n).present (act w m) = true := by
  induction n, hmn using Nat.le_induction with
  | base =>
    obtain ⟨es, hes⟩ := kmswStage_UL_last w m
    apply (kmswStage_status w m).2.1
    rw [hes]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  | succ n hmn ih =>
    change (kmswStep (kmswStage w n) (w n)).present (act w m) = true
    rw [kmswStep_present_existing _ _ (act_lt_nextEdge w hmn)]
    split
    · rfl
    · exact ih

private theorem act_ne_next (w : ℕ → Fin 3) {m n : ℕ} (hmn : m ≤ n) :
    act w m ≠ act w (n + 1) := by
  have hold := act_lt_nextEdge w hmn
  have hp := act_present w hmn
  change act w m ≠ (kmswStep (kmswStage w n) (w n)).active
  unfold kmswStep
  cases kmswCodeStep (w n) with
  | down =>
    cases hs : (kmswStage w n).UR with
    | nil => simp only [kmswStepOfStep, hs]; omega
    | cons e es =>
      simp only [kmswStepOfStep, hs]
      intro he
      have hmissing := (kmswStage_status w n).1 _ hold
      have hf := hmissing.mpr (Or.inl (by rw [hs]; simp [he]))
      rw [hp] at hf
      contradiction
  | left => cases hs : (kmswStage w n).UL.dropLast.reverse <;>
      simp only [kmswStepOfStep, hs] <;> omega
  | up => simp only [kmswStepOfStep]; omega

/-- Active edge IDs are never reused (`def-kmsw`, -/
theorem act_injective (w : ℕ → Fin 3) : Function.Injective (act w) := by
  intro m n he
  rcases lt_trichotomy m n with h | h | h
  · cases n with
    | zero => omega
    | succ n => exact (act_ne_next w (by omega) he).elim
  · exact h
  · cases m with
    | zero => omega
    | succ m => exact (act_ne_next w (by omega) he.symm).elim



theorem pending_terminal_eq_LR (w : ℕ → Fin 3) (n : ℕ) :
    (pendingVertices (kmswStage w n)).getLast? =
      ((kmswStage w n).LR.map (kmswStage w n).east).getLast? := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let s := kmswStage w n
    let t := kmswStage w (n + 1)
    have hmaps : s.LR.map t.east = s.LR.map s.east := by
      apply List.map_congr_left
      intro e he
      exact (kmswStage_endpoints_stable w (Nat.le_succ n) (lr_allocated w he)).2
    change (pendingVertices t).getLast? = (t.LR.map t.east).getLast?
    by_cases hreset : w n = 2 ∧ s.UR = []
    · obtain ⟨hw, hu⟩ := hreset
      have ht : t = kmswStep s (w n) := rfl
      rw [ht, hw]
      simp [pendingVertices, kmswStep, kmswCodeStep, kmswStepOfStep, hu,
        State.addEdge, List.map_append]
    · obtain ⟨hLR, htip⟩ := nonrecord_tip w n hreset
      rw [htip, hLR, hmaps]
      exact ih



theorem east_active_eq_LR_terminal_of_UR_nil (w : ℕ → Fin 3) (n : ℕ)
    (hUR : (kmswStage w n).UR = []) :
    some ((kmswStage w n).east (act w n)) =
      ((kmswStage w n).LR.getLast?).map (kmswStage w n).east := by
  simpa only [pendingVertices, hUR, List.map_nil, List.getLast?_singleton,
    List.getLast?_map, act] using pending_terminal_eq_LR w n
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

/-- West vertices of UL, ordered from the active edge toward the source -/
@[expose] def westStack (w : ℕ → Fin 3) (n : ℕ) : List ℕ :=
  (kmswStage w n).UL.reverse.map (kmswStage w n).west

private theorem westStack_old_map (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).UL.reverse.map (kmswStage w (n + 1)).west = westStack w n := by
  apply List.map_congr_left
  intro e he
  exact (kmswStage_endpoints_stable w (Nat.le_succ n)
    (ul_allocated w (List.mem_reverse.mp he))).1

private theorem westStack_down (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2) :
    (westStack w (n + 1)).tail = westStack w n := by
  have hs := step_UL_reverse (kmswStage w n) (w n)
  change (kmswStage w (n + 1)).UL.reverse = act w (n + 1) :: _ at hs
  have h0 : (2 : Fin 3) ≠ 0 := by decide
  have h1 : (2 : Fin 3) ≠ 1 := by decide
  simp only [hc, h0, h1, ↓reduceIte] at hs
  change ((kmswStage w (n + 1)).UL.reverse.map
    (kmswStage w (n + 1)).west).tail = _
  rw [hs]
  simp only [List.map_cons, List.tail_cons]
  exact westStack_old_map w n

private theorem westStack_up (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1) :
    westStack w (n + 1) = westStack w n := by
  have hs := step_UL_reverse (kmswStage w n) (w n)
  change (kmswStage w (n + 1)).UL.reverse = act w (n + 1) :: _ at hs
  have h0 : (1 : Fin 3) ≠ 0 := by decide
  simp only [hc, h0, ↓reduceIte] at hs
  have ht := congrArg List.tail (westStack_old_map w n)
  simp only [← List.map_tail] at ht
  have hw : (kmswStage w (n + 1)).west (act w (n + 1)) =
      (kmswStage w n).west (act w n) := by
    simp [act, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, State.addEdge]
  unfold westStack
  rw [hs, List.map_cons]
  change (kmswStage w (n + 1)).west (act w (n + 1)) :: _ = _
  rw [ht, hw]
  obtain ⟨es, hes⟩ := kmswStage_UL_last w n
  simp [westStack, hes, act]

private theorem westStack_left (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0)
    (hlen : 2 ≤ (kmswStage w n).UL.length) :
    westStack w (n + 1) = (westStack w n).tail := by
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
    have ht := congrArg (fun xs : List ℕ => xs.tail.tail) (westStack_old_map w n)
    simp only [← List.map_tail, hrev, List.tail_cons] at ht
    have hw : (kmswStage w (n + 1)).west (act w (n + 1)) =
        (kmswStage w n).west e := by
      simp [act, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep,
        hdrop, State.addEdge]
    unfold westStack
    rw [hs, List.map_cons]
    change (kmswStage w (n + 1)).west (act w (n + 1)) :: _ = _
    rw [hw, ht]
    simp [westStack, hrev]

private theorem coord_L_succ (w : ℕ → Fin 3) (n : ℕ) :
    L w (n + 1) = L w n + (RandomWalk.lazyTwoDimensionalStep (w n)).1 :=
  Finset.sum_range_succ _ _

private theorem westStack_excursion (w : ℕ → Fin 3) {a n : ℕ} (han : a ≤ n)
    (habove : ∀ j, a ≤ j → j ≤ n → L w a ≤ L w j) :
    (westStack w n).drop (L w n - L w a).toNat = westStack w a := by
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
      rw [westStack_left w n h0 hlen2]
      have hidx : (L w n - L w a).toNat = (L w (n + 1) - L w a).toNat + 1 := by
        omega
      rw [hidx] at hi
      simpa only [List.drop_tail] using hi
    · by_cases h1 : w n = 1
      · rw [h1, RandomWalk.lazyTwoDimensionalStep_one] at hc
        dsimp at hc
        rw [add_zero] at hc
        rw [westStack_up w n h1, hc]
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
        rw [hidx, ← List.drop_tail, westStack_down w n h2]
        exact hi



private theorem westStack_head (w : ℕ → Fin 3) (n : ℕ) :
    westStack w n = activeInitial w n :: (westStack w n).tail := by
  obtain ⟨es, hes⟩ := kmswStage_UL_last w n
  rw [activeInitial_eq]
  simp [westStack, hes, act]

private theorem westStack_visited (w : ℕ → Fin 3) {n v : ℕ}
    (hv : v ∈ westStack w n) : ∃ m ≤ n, v = activeInitial w m := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
  exact ul_west_visited w (List.mem_reverse.mp he)

private theorem down_initial (w : ℕ → Fin 3) (n : ℕ) (hw : w n = 2) :
    activeInitial w (n + 1) = (kmswStage w n).east (act w n) := by
  rw [activeInitial_eq]
  cases hu : (kmswStage w n).UR with
  | nil => simp [act, kmswStage, kmswStep, kmswCodeStep, hw, kmswStepOfStep,
      hu, State.addEdge]
  | cons e es =>
    have hc := (frontier_history w n).1
    have he : (kmswStage w n).west e = (kmswStage w n).east (act w n) := by
      have hh := congrArg List.head? hc
      simpa [FrontierCoherent, pendingVertices, hu, act] using hh
    simpa [act, kmswStage, kmswStep, kmswCodeStep, hw, kmswStepOfStep, hu] using he

private theorem westStack_down_eq (w : ℕ → Fin 3) (n : ℕ) (hw : w n = 2) :
    westStack w (n + 1) = activeInitial w (n + 1) :: westStack w n := by
  rw [westStack_head w (n + 1), westStack_down w n hw]

private theorem westStack_left_short (w : ℕ → Fin 3) (n : ℕ) (hw : w n = 0)
    (hlen : (kmswStage w n).UL.length < 2) :
    westStack w (n + 1) = [(kmswStage w n).nextVertex] := by
  have hd : (kmswStage w n).UL.dropLast.reverse = [] := by
    apply List.length_eq_zero_iff.mp
    simp only [List.length_reverse, List.length_dropLast]
    omega
  simp [westStack, kmswStage, kmswStep, kmswCodeStep, hw, kmswStepOfStep,
    hd, State.addEdge]

/-- West vertices of the UL path are pairwise distinct (`def-kmsw`, -/
theorem westStack_nodup (w : ℕ → Fin 3) (n : ℕ) : (westStack w n).Nodup := by
  induction n with
  | zero => simp [westStack, kmswStage, kmswInit]
  | succ n ih =>
    by_cases h0 : w n = 0
    · by_cases hl : 2 ≤ (kmswStage w n).UL.length
      · rw [westStack_left w n h0 hl]
        exact ih.tail
      · rw [westStack_left_short w n h0 (by omega)]
        exact List.nodup_singleton _
    · by_cases h1 : w n = 1
      · rw [westStack_up w n h1]; exact ih
      · have h2 : w n = 2 := by
          apply Fin.ext
          have := (w n).isLt
          have hn0 : (w n).val ≠ 0 := fun he => h0 (Fin.ext he)
          have hn1 : (w n).val ≠ 1 := fun he => h1 (Fin.ext he)
          omega
        rw [westStack_down_eq w n h2]
        apply List.nodup_cons.mpr
        refine ⟨?_, ih⟩
        intro hv
        obtain ⟨m, hm, he⟩ := westStack_visited w hv
        rw [down_initial w n h2] at he
        exact activeEast_ne_activeInitial w hm he

/-- A previously visited initial vertex that leaves UL never returns -/
theorem westStack_absent_persists (w : ℕ → Fin 3) {a m n : ℕ}
    (ham : a ≤ m) (hmn : m ≤ n) (habs : activeInitial w a ∉ westStack w m) :
    activeInitial w a ∉ westStack w n := by
  induction n, hmn using Nat.le_induction with
  | base => exact habs
  | succ n hmn ih =>
    by_cases h0 : w n = 0
    · by_cases hl : 2 ≤ (kmswStage w n).UL.length
      · rw [westStack_left w n h0 hl]
        exact fun hv => ih (List.mem_of_mem_tail hv)
      · rw [westStack_left_short w n h0 (by omega)]
        intro hv
        have he := List.mem_singleton.mp hv
        exact (Nat.ne_of_lt (initial_lt_nextVertex w (ham.trans hmn))) he
    · by_cases h1 : w n = 1
      · rw [westStack_up w n h1]; exact ih
      · have h2 : w n = 2 := by
          apply Fin.ext
          have := (w n).isLt
          have hn0 : (w n).val ≠ 0 := fun he => h0 (Fin.ext he)
          have hn1 : (w n).val ≠ 1 := fun he => h1 (Fin.ext he)
          omega
        rw [westStack_down_eq w n h2]
        intro hv
        rcases List.mem_cons.mp hv with he | hv
        · rw [down_initial w n h2] at he
          exact activeEast_ne_activeInitial w (ham.trans hmn) he.symm
        · exact ih hv


/-- Reverse-list form of the UL path incidence relation (`def-kmsw`, -/
@[expose] def ULCoherent (s : State) : Prop :=
  s.UL.reverse.map s.east = s.east s.active :: (s.UL.reverse.map s.west).dropLast

/-- The UL edges join consecutively (`def-kmsw`, -/
theorem ul_coherent (w : ℕ → Fin 3) (n : ℕ) : ULCoherent (kmswStage w n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let s := kmswStage w n
    let t := kmswStage w (n + 1)
    obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
    have hrev : s.UL.reverse = s.active :: xs.reverse := by
      simp [s, hxs]
    have hE : s.UL.reverse.map t.east = s.UL.reverse.map s.east := by
      apply List.map_congr_left
      intro e he
      exact (kmswStage_endpoints_stable w (Nat.le_succ n)
        (ul_allocated w (List.mem_reverse.mp he))).2
    have hW : s.UL.reverse.map t.west = s.UL.reverse.map s.west :=
      westStack_old_map w n
    have hEt := congrArg List.tail hE
    have hWt := congrArg List.tail hW
    simp only [hrev, List.map_cons, List.tail_cons] at hEt hWt
    change ULCoherent s at ih
    have hi : xs.reverse.map s.east =
        (s.west s.active :: xs.reverse.map s.west).dropLast := by
      have hh := congrArg List.tail ih
      simpa only [ULCoherent, hrev, List.map_cons, List.tail_cons] using hh
    have hs := step_UL_reverse s (w n)
    change t.UL.reverse = t.active :: _ at hs
    change ULCoherent t
    by_cases h0 : w n = 0
    · simp only [h0, ↓reduceIte, hrev, List.tail_cons] at hs
      have hd : s.UL.dropLast.reverse = xs.reverse := by
        rw [reverse_dropLast, hrev, List.tail_cons]
      cases hx : xs.reverse with
      | nil =>
        simp only [hx, List.tail_nil] at hs
        simp [ULCoherent, hs]
      | cons e es =>
        have hw : t.west t.active = s.west e := by
          change (kmswStep s (w n)).west (kmswStep s (w n)).active = _
          simp [h0, kmswStep, kmswCodeStep, kmswStepOfStep, hd, hx, State.addEdge]
        rw [hx] at hEt hWt hi hs
        have hEtt := congrArg List.tail hEt
        have hWtt := congrArg List.tail hWt
        simp only [List.map_cons, List.tail_cons] at hEtt hWtt
        have hit := congrArg List.tail hi
        simp only [List.map_cons, List.dropLast_cons_cons, List.tail_cons] at hit
        simp only [ULCoherent, hs, List.tail_cons, List.map_cons, hEtt, hWtt, hw]
        exact congrArg (List.cons (t.east t.active)) hit
    · by_cases h1 : w n = 1
      · simp only [h1, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, hrev, List.tail_cons] at hs
        have hw : t.west t.active = s.west s.active := by
          change (kmswStep s (w n)).west (kmswStep s (w n)).active = _
          simp [h1, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
        simp only [ULCoherent, hs, List.map_cons, hEt, hWt, hw]
        exact congrArg (List.cons (t.east t.active)) hi
      · have h2 : w n = 2 := by
          apply Fin.ext
          have := (w n).isLt
          have hn0 : (w n).val ≠ 0 := fun he => h0 (Fin.ext he)
          have hn1 : (w n).val ≠ 1 := fun he => h1 (Fin.ext he)
          omega
        simp only [h0, h1, ↓reduceIte] at hs
        have hw : t.west t.active = s.east s.active := by
          have hh := down_initial w n h2
          rw [activeInitial_eq] at hh
          exact hh
        simp only [ULCoherent, hs, List.map_cons, hE, hW, hw]
        rw [hrev]
        simp only [List.map_cons, List.dropLast_cons_cons]
        simp only [ULCoherent, hrev, List.map_cons] at ih
        exact congrArg (List.cons (t.east t.active)) ih


/-- A surviving UL west vertex has never crossed below its initial level -/
theorem barrier_of_westStack_mem (w : ℕ → Fin 3) {a m : ℕ} (_ham : a ≤ m)
    (hv : activeInitial w a ∈ westStack w m) :
    ∀ j, a ≤ j → j ≤ m → L w a ≤ L w j := by
  intro j haj hjm
  by_contra hbad
  have hex : ∃ d, a ≤ d ∧ d ≤ m ∧ L w d < L w a :=
    ⟨j, haj, hjm, by omega⟩
  let d := Nat.find hex
  have hd : a ≤ d ∧ d ≤ m ∧ L w d < L w a := Nat.find_spec hex
  have had : a < d := by
    by_contra hh
    have : d = a := by omega
    rw [this] at hd
    omega
  have hdpos : 0 < d := by omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdpos)
  have hak : a ≤ k := by omega
  have habove : ∀ i, a ≤ i → i ≤ k → L w a ≤ L w i := by
    intro i hai hik
    by_contra hi
    have hf : Nat.find hex ≤ i := Nat.find_min' hex ⟨hai, by omega, by omega⟩
    change d ≤ i at hf
    omega
  have hc := coord_L_succ w k
  have hprev := habove k hak (le_refl _)
  have h0 : w k = 0 := by
    by_contra h0
    by_cases h1 : w k = 1
    · rw [h1, RandomWalk.lazyTwoDimensionalStep_one] at hc
      have hdk : L w d = L w (k + 1) := congrArg (L w) hk
      dsimp at hc
      omega
    · have h2 : w k = 2 := by
        apply Fin.ext
        have := (w k).isLt
        have hn0 : (w k).val ≠ 0 := fun he => h0 (Fin.ext he)
        have hn1 : (w k).val ≠ 1 := fun he => h1 (Fin.ext he)
        omega
      rw [h2, RandomWalk.lazyTwoDimensionalStep_two] at hc
      have hdk : L w d = L w (k + 1) := congrArg (L w) hk
      dsimp at hc
      omega
  rw [h0, RandomWalk.lazyTwoDimensionalStep_zero] at hc
  have hlev : L w k = L w a := by
    have hdk : L w d = L w (k + 1) := congrArg (L w) hk
    dsimp at hc
    omega
  have hstack : westStack w k = westStack w a := by
    have hh := westStack_excursion w hak habove
    simpa only [hlev, sub_self, Int.toNat_zero, List.drop_zero] using hh
  have habs : activeInitial w a ∉ westStack w (k + 1) := by
    by_cases hl : 2 ≤ (kmswStage w k).UL.length
    · rw [westStack_left w k h0 hl, hstack]
      have hn := westStack_nodup w a
      rw [westStack_head w a] at hn
      exact (List.nodup_cons.mp hn).1
    · rw [westStack_left_short w k h0 (by omega)]
      intro hh
      exact (Nat.ne_of_lt (initial_lt_nextVertex w hak)) (List.mem_singleton.mp hh)
  exact westStack_absent_persists w (by omega : a ≤ k + 1) (by omega : k + 1 ≤ m)
    habs hv

/-- For a visited initial vertex, either endpoint of a UL edge is represented -/
theorem westStack_mem_of_UL_incidence (w : ℕ → Fin 3) {a J e : ℕ} (haJ : a ≤ J)
    (he : e ∈ (kmswStage w J).UL)
    (hv : edgeWest w e = activeInitial w a ∨ edgeEast w e = activeInitial w a) :
    activeInitial w a ∈ westStack w J := by
  have he' := List.mem_reverse.mpr he
  have halloc := ul_allocated w he
  rcases hv with hv | hv
  · exact List.mem_map.mpr ⟨e, he', ((edge_endpoints_eq w halloc).1.trans hv)⟩
  · have hmem : activeInitial w a ∈
        (kmswStage w J).UL.reverse.map (kmswStage w J).east := by
      exact List.mem_map.mpr ⟨e, he', ((edge_endpoints_eq w halloc).2.trans hv)⟩
    rw [ul_coherent w J] at hmem
    rcases List.mem_cons.mp hmem with hh | hh
    · exact (activeEast_ne_activeInitial w haJ hh.symm).elim
    · exact List.dropLast_subset _ hh


/-- All UL path vertices, including its terminal vertex, are distinct -/
theorem ul_path_vertices_nodup (w : ℕ → Fin 3) (n : ℕ) :
    ((kmswStage w n).east (act w n) :: westStack w n).Nodup := by
  apply List.nodup_cons.mpr
  refine ⟨?_, westStack_nodup w n⟩
  intro hv
  obtain ⟨m, hm, he⟩ := westStack_visited w hv
  exact activeEast_ne_activeInitial w hm he



theorem ur_up_origin (w : ℕ → Fin 3) (n : ℕ) :
    ∀ e ∈ (kmswStage w n).UR, ∃ k < n, w k = 1 ∧
      e = (kmswStage w k).nextEdge + 1 ∧ edgeWest w e = (kmswStage w k).nextVertex := by
  induction n with
  | zero => simp [kmswStage, kmswInit]
  | succ n ih =>
    let s := kmswStage w n
    let t := kmswStage w (n + 1)
    have hold (e : ℕ) (he : e ∈ s.UR) : ∃ k < n + 1, w k = 1 ∧
        e = (kmswStage w k).nextEdge + 1 ∧ edgeWest w e = (kmswStage w k).nextVertex := by
      obtain ⟨k, hk, hw, heq, hv⟩ := ih e he
      exact ⟨k, by omega, hw, heq, hv⟩
    change ∀ e ∈ t.UR, _
    generalize hw : w n = c
    fin_cases c
    · have hUR : t.UR = s.UR := by
        change (kmswStep s (w n)).UR = _
        rw [hw]
        cases hs : s.UL.dropLast.reverse <;>
          simp [kmswStep, kmswCodeStep, kmswStepOfStep, hs, State.addEdge]
      rw [hUR]
      exact hold
    · have hUR : t.UR = (s.nextEdge + 1) :: s.UR := by
        change (kmswStep s (w n)).UR = _
        simp [hw, kmswStep, kmswCodeStep, kmswStepOfStep]
      intro e he
      rw [hUR, List.mem_cons] at he
      rcases he with rfl | he
      · refine ⟨n, Nat.lt_succ_self n, hw, rfl, ?_⟩
        have halloc := ur_allocated w (n + 1) (s.nextEdge + 1) (by rw [hUR]; simp)
        rw [← (edge_endpoints_eq w halloc).1]
        change (kmswStep s (w n)).west (s.nextEdge + 1) = s.nextVertex
        simp [hw, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
      · exact hold e he
    · cases hs : s.UR with
      | nil =>
        have hUR : t.UR = [] := by
          change (kmswStep s (w n)).UR = _
          simp [hw, kmswStep, kmswCodeStep, kmswStepOfStep, hs, State.addEdge]
        simp [hUR]
      | cons e es =>
        have hUR : t.UR = es := by
          change (kmswStep s (w n)).UR = _
          simp [hw, kmswStep, kmswCodeStep, kmswStepOfStep, hs]
        intro f hf
        apply hold f
        rw [hs]
        exact List.mem_cons_of_mem _ (hUR ▸ hf)



theorem pending_interior_up_origin (w : ℕ → Fin 3) (n : ℕ) {v : ℕ}
    (hv : v ∈ (pendingVertices (kmswStage w n)).dropLast) :
    ∃ k < n, w k = 1 ∧ v = (kmswStage w k).nextVertex := by
  have hc := (frontier_history w n).1
  rw [← hc] at hv
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
  obtain ⟨k, hk, hw, _, hv⟩ := ur_up_origin w n e he
  exact ⟨k, hk, hw, ((edge_endpoints_eq w (ur_allocated w n e he)).1).trans hv⟩

private theorem nextVertex_step_mono (s : State) (c : Fin 3) :
    s.nextVertex ≤ (kmswStep s c).nextVertex := by
  unfold kmswStep
  cases kmswCodeStep c with
  | down => cases hs : s.UR <;> simp [kmswStepOfStep, hs, State.addEdge]
  | left => cases hs : s.UL.dropLast.reverse <;> simp [kmswStepOfStep, hs, State.addEdge]
  | up => simp [kmswStepOfStep, State.addEdge]

/-- Vertex allocation is monotone (`def-kmsw`, -/
theorem nextVertex_mono (w : ℕ → Fin 3) {m n : ℕ} (hmn : m ≤ n) :
    (kmswStage w m).nextVertex ≤ (kmswStage w n).nextVertex := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_refl _
  | succ n _ ih => exact ih.trans (nextVertex_step_mono _ _)

private theorem nextVertex_up (w : ℕ → Fin 3) (n : ℕ) (hw : w n = 1) :
    (kmswStage w (n + 1)).nextVertex = (kmswStage w n).nextVertex + 1 := by
  simp [kmswStage, kmswStep, kmswCodeStep, hw, kmswStepOfStep, State.addEdge]

private theorem nextVertex_down_empty (w : ℕ → Fin 3) (n : ℕ)
    (hw : w n = 2) (hu : (kmswStage w n).UR = []) :
    (kmswStage w (n + 1)).nextVertex = (kmswStage w n).nextVertex + 1 := by
  simp [kmswStage, kmswStep, kmswCodeStep, hw, kmswStepOfStep, hu, State.addEdge]

/-- LR vertices are the two root endpoints or fresh vertices created by -/
theorem lr_endpoint_origin (w : ℕ → Fin 3) (n : ℕ) :
    ∀ e ∈ (kmswStage w n).LR, ∀ v,
      (edgeWest w e = v ∨ edgeEast w e = v) →
      v = 0 ∨ v = 1 ∨ ∃ k < n, w k = 2 ∧ (kmswStage w k).UR = [] ∧
        v = (kmswStage w k).nextVertex := by
  induction n with
  | zero =>
    intro e he v hv
    have he : e = 0 := by simpa [kmswStage, kmswInit] using he
    subst e
    rcases hv with hv | hv
    · exact Or.inl hv.symm
    · exact Or.inr (Or.inl hv.symm)
  | succ n ih =>
    let s := kmswStage w n
    let t := kmswStage w (n + 1)
    have hold (e : ℕ) (he : e ∈ s.LR) (v : ℕ)
        (hv : edgeWest w e = v ∨ edgeEast w e = v) :
        v = 0 ∨ v = 1 ∨ ∃ k < n + 1, w k = 2 ∧ (kmswStage w k).UR = [] ∧
          v = (kmswStage w k).nextVertex := by
      rcases ih e he v hv with hh | hh | ⟨k, hk, hw, hu, hv⟩
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr ⟨k, by omega, hw, hu, hv⟩)
    by_cases hreset : w n = 2 ∧ s.UR = []
    · obtain ⟨hw, hu⟩ := hreset
      have hLR : t.LR = s.LR ++ [s.nextEdge] := by
        change (kmswStep s (w n)).LR = _
        simp [hw, kmswStep, kmswCodeStep, kmswStepOfStep, hu, State.addEdge]
      intro e he v hv
      change e ∈ t.LR at he
      rw [hLR, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact hold e he v hv
      · have halloc : s.nextEdge < t.nextEdge := by
          change s.nextEdge < (kmswStep s (w n)).nextEdge
          simp [hw, kmswStep, kmswCodeStep, kmswStepOfStep, hu, State.addEdge]
        have hnew : edgeWest w s.nextEdge = s.east s.active ∧
            edgeEast w s.nextEdge = s.nextVertex := by
          have hh := edge_endpoints_eq w halloc
          have ht : t = kmswStep s (w n) := rfl
          change t.west s.nextEdge = _ ∧ t.east s.nextEdge = _ at hh
          rw [ht, hw] at hh
          constructor
          · simpa [kmswStep, kmswCodeStep, kmswStepOfStep, hu, State.addEdge] using hh.1.symm
          · simpa [kmswStep, kmswCodeStep, kmswStepOfStep, hu, State.addEdge] using hh.2.symm
        rcases hv with hv | hv
        · let e0 := s.LR.getLast (kmswStage_LR_nonempty w n)
          have hlast : s.LR.getLast? = some e0 := List.getLast?_eq_some_getLast _
          have hmem : e0 ∈ s.LR := List.getLast_mem _
          have htip := east_active_eq_LR_terminal_of_UR_nil w n hu
          change some (s.east s.active) = s.LR.getLast?.map s.east at htip
          rw [hlast] at htip
          have ht : s.east s.active = s.east e0 := Option.some.inj htip
          apply hold e0 hmem v
          apply Or.inr
          exact (edge_endpoints_eq w (lr_allocated w hmem)).2.symm.trans
            (ht.symm.trans (hnew.1.symm.trans hv))
        · exact Or.inr (Or.inr ⟨n, Nat.lt_succ_self n, hw, hu,
            (hnew.2.symm.trans hv).symm⟩)
    · intro e he v hv
      have hLR := (nonrecord_tip w n hreset).1
      rw [hLR] at he
      exact hold e he v hv

/-- A fresh up-created vertex never belongs to any LR path, including -/
theorem up_vertex_ne_LR_endpoints (w : ℕ → Fin 3) {k : ℕ} (hk : w k = 1)
    (J e : ℕ) (he : e ∈ (kmswStage w J).LR) :
    (kmswStage w k).nextVertex ≠ edgeWest w e ∧
      (kmswStage w k).nextVertex ≠ edgeEast w e := by
  have hroot : 2 ≤ (kmswStage w k).nextVertex := nextVertex_mono w (Nat.zero_le k)
  have hexclude (v : ℕ) (hv : edgeWest w e = v ∨ edgeEast w e = v) :
      (kmswStage w k).nextVertex ≠ v := by
    rcases lr_endpoint_origin w J e he v hv with rfl | rfl | ⟨i, _, hi, hu, rfl⟩
    · omega
    · omega
    · rcases lt_trichotomy k i with h | h | h
      · have hh := nextVertex_mono w (Nat.succ_le_of_lt h)
        rw [nextVertex_up w k hk] at hh
        omega
      · subst i
        rw [hk] at hi
        contradiction
      · have hh := nextVertex_mono w (Nat.succ_le_of_lt h)
        rw [nextVertex_down_empty w i hi hu] at hh
        omega
  exact ⟨hexclude _ (Or.inl rfl), hexclude _ (Or.inr rfl)⟩



theorem pending_interior_ne_LR_endpoints (w : ℕ → Fin 3) (n J : ℕ) {v e : ℕ}
    (hv : v ∈ (pendingVertices (kmswStage w n)).dropLast)
    (he : e ∈ (kmswStage w J).LR) : v ≠ edgeWest w e ∧ v ≠ edgeEast w e := by
  obtain ⟨k, _, hk, rfl⟩ := pending_interior_up_origin w n hv
  exact up_vertex_ne_LR_endpoints w hk J e he


/-- UR joins the active east endpoint to the terminal endpoint of LR -/
theorem ur_chain_to_LR (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).UR.map (kmswStage w n).west =
      ((kmswStage w n).east (act w n) ::
        (kmswStage w n).UR.map (kmswStage w n).east).dropLast ∧
    ((kmswStage w n).east (act w n) ::
      (kmswStage w n).UR.map (kmswStage w n).east).getLast? =
      ((kmswStage w n).LR.getLast?).map (kmswStage w n).east := by
  refine ⟨(frontier_history w n).1, ?_⟩
  simpa only [pendingVertices, act, List.getLast?_map] using pending_terminal_eq_LR w n

end CutConverse

/-- Left boundary incidence under a strict past right minimum is the future -/
theorem leftBoundary_iff_of_rightMin (w : ℕ → Fin 3)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop) (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1) :
    OnLeftBoundary w (activeInitial w n) ↔ ∀ j, n ≤ j → L w n ≤ L w j := by
  constructor
  · rintro ⟨e, he, hv⟩ j hnj
    obtain ⟨J, hJ, hJj⟩ := he.exists_notMem_finset (Finset.range j)
    change e ∈ (kmswStage w J).UL at hJ
    have hjJ : j ≤ J := by simpa only [Finset.mem_range, not_lt] using hJj
    have hmem := CutConverse.westStack_mem_of_UL_incidence w (hnj.trans hjJ) hJ hv
    exact CutConverse.barrier_of_westStack_mem w (hnj.trans hjJ) hmem j hnj hjJ
  · exact onLeftBoundary_activeInitial_of_barrier w htrans n


/-- Right boundary incidence with first visit is the strict vertical record -/
theorem rightBoundary_firstVisit_iff (w : ℕ → Fin 3) (n : ℕ) :
    (OnRightBoundary w (activeInitial w n) ∧
      ∀ j < n, activeInitial w j ≠ activeInitial w n) ↔
      ∀ j < n, R w n ≤ R w j - 1 := by
  constructor
  · rintro ⟨⟨e, he, hv⟩, hfirst⟩
    obtain ⟨J, hJ, hJn⟩ := he.exists_notMem_finset (Finset.range n)
    change e ∈ (kmswStage w J).LR at hJ
    have hnJ : n ≤ J := by simpa only [Finset.mem_range, not_lt] using hJn
    have halloc := CutConverse.lr_allocated w hJ
    rcases hv with hv | hv
    · rw [kmswStage_LR_eq] at hJ
      obtain ⟨k, hk, hek⟩ := List.mem_map.mp hJ
      have hr : ∀ i < k, R w k ≤ R w i - 1 := by
        have hh := of_decide_eq_true (List.mem_filter.mp hk).2
        intro i hi
        have := hh i hi
        omega
      have heq : activeInitial w k = activeInitial w n := by
        change edgeWest w (act w k) = _
        rw [hek]
        exact hv
      have hkn := CutConverse.record_time_eq w hr hfirst heq
      simpa only [hkn] using hr
    · have hv' : (kmswStage w J).east e = activeInitial w n :=
        (edge_endpoints_eq w halloc).2.trans hv
      rcases CutConverse.lr_east_history w J e hJ with ⟨k, _, hr, heq⟩ | htip
      · have hkn := CutConverse.record_time_eq w hr hfirst (heq.symm.trans hv')
        simpa only [hkn] using hr
      · have hmem := List.mem_of_getLast? htip
        rw [hv'] at hmem
        exact ((CutConverse.frontier_history w J).2.2 n hnJ hmem).elim
  · intro hr
    exact ⟨onRightBoundary_activeInitial_of_record w n hr,
      activeInitial_ne_of_right_record w n hr⟩


/-- The converse cut criterion (`lem-cut-equiv`, -/
theorem records_of_cut_and_first_visit (w : ℕ → Fin 3)
    (hL0 : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop) (n : ℕ)
    (hcut : IsCutVertex w (activeInitial w n))
    (hfirst : ∀ j < n, activeInitial w j ≠ activeInitial w n) :
    (∀ j < n, R w n ≤ R w j - 1) ∧ (∀ j, n ≤ j → L w n ≤ L w j) := by
  have hA := (rightBoundary_firstVisit_iff w n).mp ⟨hcut.2, hfirst⟩
  exact ⟨hA, (leftBoundary_iff_of_rightMin w htrans n hA).mp hcut.1⟩

/-- Lemma 4.8, deterministic form, in the UIQBOT setting: L ≥ 0 and L → ∞ -/
theorem cut_equiv_of_nonneg_of_tendsto (w : ℕ → Fin 3)
    (hL0 : ∀ j, 0 ≤ L w j) (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop) (n : ℕ) :
    (IsCutVertex w (activeInitial w n) ∧ ∀ j < n, activeInitial w j ≠ activeInitial w n) ↔
      ((∀ j < n, R w n ≤ R w j - 1) ∧ (∀ j, n ≤ j → L w n ≤ L w j)) := by
  constructor
  · rintro ⟨hcut, hfirst⟩
    exact records_of_cut_and_first_visit w hL0 htrans n hcut hfirst
  · rintro ⟨hR, hL⟩
    exact cut_and_first_visit_of_records w htrans n hR hL

end DirectedDistances.KMSW
