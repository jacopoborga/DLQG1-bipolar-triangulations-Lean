module

public import DirectedDistances.KMSW.BoundaryRecordsUL
import DirectedDistances.KMSW.WalkRecordCounts
import DirectedDistances.RandomWalk.ConditionedTransience
import Mathlib.Order.Interval.Set.Infinite

/-! # Infinite-boundary endpoint bookkeeping

Stable endpoints and boundary predicates for `lem-cut-equiv`, -/

public section
namespace DirectedDistances.KMSW
open scoped Classical

private theorem allocation_count (w : ℕ → Fin 3) (n : ℕ) :
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

/-- Every edge ID `e` is allocated by stage `e` of `def-kmsw`, -/
private theorem edge_lt_nextEdge_at_self (w : ℕ → Fin 3) (e : ℕ) :
    e < (kmswStage w e).nextEdge := by
  have := allocation_count w e
  omega

/-- Stable geometric west endpoint (`def-kmsw`, -/
@[expose] def edgeWest (w : ℕ → Fin 3) (e : ℕ) : ℕ := (kmswStage w e).west e

/-- Stable geometric east endpoint (`def-kmsw`, -/
@[expose] def edgeEast (w : ℕ → Fin 3) (e : ℕ) : ℕ := (kmswStage w e).east e

/-- Both endpoints at any stage where an edge exists equal its stable endpoints -/
theorem edge_endpoints_eq (w : ℕ → Fin 3) {j e : ℕ}
    (he : e < (kmswStage w j).nextEdge) :
    (kmswStage w j).west e = edgeWest w e ∧
      (kmswStage w j).east e = edgeEast w e := by
  rcases le_total e j with hej | hje
  · exact kmswStage_endpoints_stable w hej (edge_lt_nextEdge_at_self w e)
  · have h := kmswStage_endpoints_stable w hje he
    exact ⟨h.1.symm, h.2.symm⟩

/-- Infinite upper-left membership (`remark-kmsw-infinite`, -/
@[expose] def IsLeftBoundaryEdge (w : ℕ → Fin 3) (e : ℕ) : Prop :=
  {j | e ∈ (kmswStage w j).UL}.Infinite

/-- Infinite lower-right membership (`remark-kmsw-infinite`, -/
@[expose] def IsRightBoundaryEdge (w : ℕ → Fin 3) (e : ℕ) : Prop :=
  {j | e ∈ (kmswStage w j).LR}.Infinite

/-- Endpoint incidence on the left boundary (`def-cut-vertex`, -/
@[expose] def OnLeftBoundary (w : ℕ → Fin 3) (v : ℕ) : Prop :=
  ∃ e, IsLeftBoundaryEdge w e ∧ (edgeWest w e = v ∨ edgeEast w e = v)

/-- Endpoint incidence on the right boundary (`def-cut-vertex`, -/
@[expose] def OnRightBoundary (w : ℕ → Fin 3) (v : ℕ) : Prop :=
  ∃ e, IsRightBoundaryEdge w e ∧ (edgeWest w e = v ∨ edgeEast w e = v)

/-- The boundary definition of a cut vertex (`def-cut-vertex`, -/
@[expose] def IsCutVertex (w : ℕ → Fin 3) (v : ℕ) : Prop :=
  OnLeftBoundary w v ∧ OnRightBoundary w v

/-- Initial vertex of the active edge (`lem-cut-equiv`, -/
@[expose] def activeInitial (w : ℕ → Fin 3) (n : ℕ) : ℕ := edgeWest w (act w n)

/-- Stage and stable active initial vertices agree (`def-kmsw`, -/
private theorem activeInitial_eq (w : ℕ → Fin 3) (n : ℕ) :
    activeInitial w n = (kmswStage w n).west (act w n) :=
  (edge_endpoints_eq w (act_lt_nextEdge w (le_refl n))).1.symm

private theorem mem_UL_of_record (w : ℕ → Fin 3) {m j : ℕ} (hmj : m ≤ j)
    (hrec : ∀ k, m < k → k ≤ j → L w m + 1 ≤ L w k) :
    act w m ∈ (kmswStage w j).UL := by
  rw [kmswStage_UL_eq]
  exact List.mem_map.mpr ⟨m, List.mem_filter.mpr
    ⟨List.mem_range.mpr (by omega), decide_eq_true hrec⟩, rfl⟩

private theorem mem_LR_of_record (w : ℕ → Fin 3) {m j : ℕ} (hmj : m ≤ j)
    (hrec : ∀ k < m, R w m ≤ R w k - 1) :
    act w m ∈ (kmswStage w j).LR := by
  rw [kmswStage_LR_eq]
  refine List.mem_map.mpr ⟨m, List.mem_filter.mpr
    ⟨List.mem_range.mpr (by omega), ?_⟩, rfl⟩
  apply decide_eq_true
  intro k hk
  have := hrec k hk
  omega

/-- A strict all-future horizontal record gives an infinite upper-left edge -/
private theorem isLeftBoundaryEdge_act_of_strict_record (w : ℕ → Fin 3) (m : ℕ)
    (hrec : ∀ k, m < k → L w m + 1 ≤ L w k) :
    IsLeftBoundaryEdge w (act w m) := by
  apply Set.Infinite.mono (s := Set.Ici m) ?_ (Set.Ici_infinite m)
  intro j hj
  exact mem_UL_of_record w hj (fun k hk _ => hrec k hk)

/-- A strict past vertical record gives an infinite lower-right edge -/
private theorem isRightBoundaryEdge_act_of_record (w : ℕ → Fin 3) (m : ℕ)
    (hrec : ∀ k < m, R w m ≤ R w k - 1) :
    IsRightBoundaryEdge w (act w m) := by
  apply Set.Infinite.mono (s := Set.Ici m) ?_ (Set.Ici_infinite m)
  intro j hj
  exact mem_LR_of_record w hj hrec

/-- The initial vertex persists along a returning weak horizontal excursion -/
private theorem activeInitial_eq_of_level (w : ℕ → Fin 3) {n m : ℕ}
    (hnm : n ≤ m) (hlev : L w n = L w m)
    (habove : ∀ j, n ≤ j → j ≤ m → L w n ≤ L w j) :
    activeInitial w n = activeInitial w m := by
  have h := kmsw_west_act_eq_of_level w hnm hlev habove
  rw [(edge_endpoints_eq w (act_lt_nextEdge w hnm)).1,
    (edge_endpoints_eq w (act_lt_nextEdge w (le_refl m))).1] at h
  exact h

/-- Transience upgrades a weak all-future horizontal barrier to endpoint
incidence on an infinite upper-left edge (`lem-cut-equiv`, -/
theorem onLeftBoundary_activeInitial_of_barrier (w : ℕ → Fin 3)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop) (n : ℕ)
    (hbarrier : ∀ j, n ≤ j → L w n ≤ L w j) :
    OnLeftBoundary w (activeInitial w n) := by
  obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp htrans (L w n + 1)
  let M := max N n
  let m := Nat.findGreatest (fun i => L w i = L w n) M
  have hnm : n ≤ m := Nat.le_findGreatest (le_max_right N n) rfl
  have hmM : m ≤ M := Nat.findGreatest_le M
  have hm : L w m = L w n :=
    Nat.findGreatest_spec (P := fun i => L w i = L w n) (le_max_right N n) rfl
  have hrec : ∀ j, m < j → L w m + 1 ≤ L w j := by
    intro j hmj
    rw [hm]
    by_cases hMj : M < j
    · exact hN j (by dsimp [M] at hMj; omega)
    · have hjM : j ≤ M := by omega
      have hne : L w j ≠ L w n := by
        intro he
        have hjm : j ≤ m := Nat.le_findGreatest hjM he
        omega
      have hj := hbarrier j (by omega)
      omega
  refine ⟨act w m, isLeftBoundaryEdge_act_of_strict_record w m hrec, Or.inl ?_⟩
  exact (activeInitial_eq_of_level w hnm hm.symm
    (fun j hnj _ => hbarrier j hnj)).symm

/-- A strict past vertical record places the active initial vertex on the -/
theorem onRightBoundary_activeInitial_of_record (w : ℕ → Fin 3) (n : ℕ)
    (hrec : ∀ j < n, R w n ≤ R w j - 1) :
    OnRightBoundary w (activeInitial w n) :=
  ⟨act w n, isRightBoundaryEdge_act_of_record w n hrec, Or.inl rfl⟩

/-- The two walk barriers imply the boundary-incidence part of the cut -/
private theorem isCutVertex_activeInitial_of_records (w : ℕ → Fin 3)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop) (n : ℕ)
    (hR : ∀ j < n, R w n ≤ R w j - 1)
    (hL : ∀ j, n ≤ j → L w n ≤ L w j) :
    IsCutVertex w (activeInitial w n) :=
  ⟨onLeftBoundary_activeInitial_of_barrier w htrans n hL,
    onRightBoundary_activeInitial_of_record w n hR⟩

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

private def EndpointBound (s : State) (V : ℕ) : Prop :=
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

private theorem endpoint_bound (w : ℕ → Fin 3) (n : ℕ) :
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

private def pendingVertices (s : State) : List ℕ :=
  s.east s.active :: s.UR.map s.east

private def FrontierCoherent (s : State) : Prop :=
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

private theorem frontier_history (w : ℕ → Fin 3) (n : ℕ) :
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

/-- The terminal vertex of the active edge has never been an active initial -/
theorem activeEast_ne_activeInitial (w : ℕ → Fin 3) {j n : ℕ} (hj : j ≤ n) :
    (kmswStage w n).east (act w n) ≠ activeInitial w j := by
  intro he
  apply (frontier_history w n).2.2 j hj
  exact List.mem_cons.mpr (Or.inl he.symm)

private theorem right_record_step (w : ℕ → Fin 3) (n : ℕ)
    (hrec : ∀ j < n + 1, R w (n + 1) ≤ R w j - 1) :
    w n = 2 ∧ (kmswStage w n).UR = [] := by
  have hc : R w (n + 1) = R w n +
      (RandomWalk.lazyTwoDimensionalStep (w n)).2 := Finset.sum_range_succ _ _
  have hn := hrec n (Nat.lt_succ_self n)
  have h2 : w n = 2 := by
    by_cases h0 : w n = 0
    · rw [h0, RandomWalk.lazyTwoDimensionalStep_zero] at hc
      dsimp at hc
      omega
    by_cases h1 : w n = 1
    · rw [h1, RandomWalk.lazyTwoDimensionalStep_one] at hc
      dsimp at hc
      omega
    apply Fin.ext
    have := (w n).isLt
    have hn0 : (w n).val ≠ 0 := fun he => h0 (Fin.ext he)
    have hn1 : (w n).val ≠ 1 := fun he => h1 (Fin.ext he)
    omega
  refine ⟨h2, ?_⟩
  obtain ⟨i, hi, he⟩ := runningMin_attained (R w) n
  have hh := hrec i (by omega)
  have hlen := kmswStage_UR_length w n
  rw [h2, RandomWalk.lazyTwoDimensionalStep_two] at hc
  change minR w n = R w i at he
  have hz : (kmswStage w n).UR.length = 0 := by dsimp at hc; omega
  exact List.length_eq_zero_iff.mp hz

/-- At a strict vertical record, the active initial vertex is visited for the -/
theorem activeInitial_ne_of_right_record (w : ℕ → Fin 3) (n : ℕ)
    (hrec : ∀ j < n, R w n ≤ R w j - 1) :
    ∀ j < n, activeInitial w j ≠ activeInitial w n := by
  cases n with
  | zero => intro j hj; omega
  | succ n =>
    obtain ⟨h2, hUR⟩ := right_record_step w n hrec
    have hnew : activeInitial w (n + 1) = (kmswStage w n).east (act w n) := by
      rw [activeInitial_eq]
      simp [act, kmswStage, kmswStep, kmswCodeStep, h2, kmswStepOfStep,
        hUR, State.addEdge]
    intro j hj he
    have hh := activeEast_ne_activeInitial w (j := j) (n := n) (by omega)
    exact hh (hnew.symm.trans he.symm)

/-- The forward walk-to-cut direction, including first-visit uniqueness, of -/
theorem cut_and_first_visit_of_records (w : ℕ → Fin 3)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop) (n : ℕ)
    (hR : ∀ j < n, R w n ≤ R w j - 1)
    (hL : ∀ j, n ≤ j → L w n ≤ L w j) :
    IsCutVertex w (activeInitial w n) ∧
      ∀ j < n, activeInitial w j ≠ activeInitial w n :=
  ⟨isCutVertex_activeInitial_of_records w htrans n hR hL,
    activeInitial_ne_of_right_record w n hR⟩

end DirectedDistances.KMSW
