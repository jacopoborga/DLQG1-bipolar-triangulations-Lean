module

public import DirectedDistances.KMSW.BoundaryDynamics
public import DirectedDistances.KMSW.BoundaryRecordsUL
public import Mathlib.Data.List.Chain
public import Mathlib.Data.Rat.Lemmas

/-! # Incidence facts for the finite KMSW stages

Stage-level combinatorial bookkeeping for `def-kmsw`, -/

public section
namespace DirectedDistances.KMSW

/-- Consecutive edges in an ordered KMSW boundary meet east-to-west -/
@[expose] def WestEastChain (s : State) : List ℕ → Prop
  := List.IsChain (fun e f => s.east e = s.west f)

/-- Initial vertex represented by the first edge of an ordered KMSW boundary -/
@[expose] def boundaryStart (s : State) (es : List ℕ) : Option ℕ :=
  es.head?.map s.west

/-- Terminal vertex represented by the last edge of an ordered KMSW boundary -/
@[expose] def boundaryEnd (s : State) (es : List ℕ) : Option ℕ :=
  es.getLast?.map s.east

/-- Rational vertex ranks for the successive `def-kmsw` stages
Fresh vertices are placed above the active endpoint on a down step, below the
active initial endpoint on a fresh left step, and between the active endpoints
on an up step. -/
@[expose] def kmswStageRank (w : ℕ → Fin 3) : ℕ → ℕ → ℚ
  | 0, v => if v = 0 then 0 else if v = 1 then 1 else 0
  | n + 1, v =>
      let s := kmswStage w n
      let r := kmswStageRank w n
      if v = s.nextVertex then
        if w n = 0 then
          if s.UL.dropLast.reverse = [] then r (s.west s.active) - 1
          else r v
        else if w n = 1 then
          (r (s.west s.active) + r (s.east s.active)) / 2
        else if s.UR = [] then r (s.east s.active) + 1
        else r v
      else r v

private theorem step_edge_ids (s : State) (c : Fin 3)
    (hb : ∀ e ∈ s.UL ++ s.UR ++ s.LL ++ s.LR, e < s.nextEdge) :
    (kmswStep s c).active < (kmswStep s c).nextEdge ∧
      (∀ e ∈ (kmswStep s c).UL ++ (kmswStep s c).UR ++
          (kmswStep s c).LL ++ (kmswStep s c).LR,
        e < (kmswStep s c).nextEdge) ∧
      s.nextEdge ≤ (kmswStep s c).nextEdge := by
  have hu : ∀ e ∈ s.UL, e < s.nextEdge := by
    intro e he
    apply hb e
    simp only [List.mem_append]
    tauto
  have hr : ∀ e ∈ s.UR, e < s.nextEdge := by
    intro e he
    apply hb e
    simp only [List.mem_append]
    tauto
  have hl : ∀ e ∈ s.LL, e < s.nextEdge := by
    intro e he
    apply hb e
    simp only [List.mem_append]
    tauto
  have hd : ∀ e ∈ s.LR, e < s.nextEdge := by
    intro e he
    apply hb e
    simp only [List.mem_append]
    tauto
  have hpre : ∀ e ∈ s.UL.dropLast, e < s.nextEdge := by
    intro e he
    exact hu e (List.dropLast_subset _ he)
  unfold kmswStep
  cases kmswCodeStep c with
  | down =>
      dsimp only [kmswStepOfStep]
      split <;> simp_all [State.addEdge, List.mem_append, List.mem_cons] <;> grind
  | left =>
      dsimp only [kmswStepOfStep]
      split
      · simp_all [State.addEdge, List.mem_append, List.mem_cons] <;> grind
      · simp_all [State.addEdge, List.mem_append, List.mem_cons] <;> grind
  | up =>
      simp_all [kmswStepOfStep, State.addEdge, List.mem_append, List.mem_cons] <;> grind

private theorem stage_edge_ids (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).active < (kmswStage w n).nextEdge ∧
      (∀ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR ++
          (kmswStage w n).LL ++ (kmswStage w n).LR,
        e < (kmswStage w n).nextEdge) := by
  induction n with
  | zero => simp [kmswStage, kmswInit]
  | succ n ih =>
      have hs := step_edge_ids (kmswStage w n) (w n) ih.2
      exact ⟨hs.1, hs.2.1⟩

/-- Every edge ID on any of the four KMSW boundary lists and the active ID -/
theorem kmswStage_boundary_ids_lt_nextEdge (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).active < (kmswStage w n).nextEdge ∧
      (∀ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR ++
          (kmswStage w n).LL ++ (kmswStage w n).LR,
        e < (kmswStage w n).nextEdge) :=
  stage_edge_ids w n

private theorem addEdge_endpoint_bound (s : State) (V a b : ℕ)
    (hold : ∀ e < s.nextEdge, s.west e < V ∧ s.east e < V)
    (ha : a < V) (hb : b < V) :
    ∀ e < s.nextEdge + 1,
      (s.addEdge a b true).west e < V ∧ (s.addEdge a b true).east e < V := by
  intro e he
  by_cases h : e = s.nextEdge
  · subst e
    simp only [State.addEdge]
    simp
    exact ⟨ha, hb⟩
  · have heold : e < s.nextEdge := by omega
    simpa [State.addEdge, h] using hold e heold

private theorem step_endpoint_bound (s : State) (c : Fin 3)
    (ha : s.active < s.nextEdge)
    (hids : ∀ e ∈ s.UL ++ s.UR ++ s.LL ++ s.LR, e < s.nextEdge)
    (hvert : ∀ e < s.nextEdge, s.west e < s.nextVertex ∧ s.east e < s.nextVertex) :
    ∀ e < (kmswStep s c).nextEdge,
      (kmswStep s c).west e < (kmswStep s c).nextVertex ∧
      (kmswStep s c).east e < (kmswStep s c).nextVertex := by
  have hact := hvert s.active ha
  have hupper : ∀ e ∈ s.UL, e < s.nextEdge := by
    intro e he
    exact hids e (by simp only [List.mem_append]; tauto)
  unfold kmswStep
  cases kmswCodeStep c with
  | down =>
      dsimp only [kmswStepOfStep]
      split
      · intro e he
        exact hvert e (by simpa using he)
      · have hold : ∀ e < s.nextEdge,
            s.west e < s.nextVertex + 1 ∧ s.east e < s.nextVertex + 1 := by
          intro e he
          have h := hvert e he
          omega
        have hnew := addEdge_endpoint_bound s (s.nextVertex + 1)
          (s.east s.active) s.nextVertex hold (by omega) (by omega)
        intro e he
        simpa [State.addEdge] using hnew e (by simpa [State.addEdge] using he)
  | left =>
      dsimp only [kmswStepOfStep]
      split
      · rename_i e es hs
        have heUL : e ∈ s.UL := by
          have hdrop : e ∈ s.UL.dropLast := by
            apply List.mem_reverse.mp
            rw [hs]
            exact List.mem_cons_self
          exact List.dropLast_subset _ hdrop
        have hebound := hids e (by simp only [List.mem_append]; tauto)
        have heend := hvert e hebound
        have hold : ∀ f < s.nextEdge,
              s.west f < s.nextVertex ∧ s.east f < s.nextVertex := hvert
        have hnew := addEdge_endpoint_bound s s.nextVertex (s.west e)
          (s.east s.active) hold heend.1 hact.2
        intro f hf
        simpa [State.addEdge] using hnew f (by simpa [State.addEdge] using hf)
      · have holdOld : ∀ e < s.nextEdge,
              s.west e < s.nextVertex + 1 ∧ s.east e < s.nextVertex + 1 := by
          intro e he
          have h := hvert e he
          omega
        have ht := addEdge_endpoint_bound s (s.nextVertex + 1)
          s.nextVertex (s.east s.active) holdOld (by omega) (by omega)
        have hboundT : ∀ e < (s.addEdge s.nextVertex (s.east s.active) true).nextEdge,
              (s.addEdge s.nextVertex (s.east s.active) true).west e < s.nextVertex + 1 ∧
              (s.addEdge s.nextVertex (s.east s.active) true).east e < s.nextVertex + 1 := by
          intro e he
          simpa [State.addEdge] using ht e (by simpa [State.addEdge] using he)
        have hnew := addEdge_endpoint_bound (s.addEdge s.nextVertex (s.east s.active) true)
          (s.nextVertex + 1) s.nextVertex (s.west s.active) hboundT
          (by omega) (by omega)
        intro e he
        simpa [State.addEdge] using hnew e (by simpa [State.addEdge] using he)
  | up =>
      have holdOld : ∀ e < s.nextEdge,
            s.west e < s.nextVertex + 1 ∧ s.east e < s.nextVertex + 1 := by
        intro e he
        have h := hvert e he
        omega
      have ht := addEdge_endpoint_bound s (s.nextVertex + 1)
        (s.west s.active) s.nextVertex holdOld (by omega) (by omega)
      have hboundT : ∀ e < (s.addEdge (s.west s.active) s.nextVertex true).nextEdge,
            (s.addEdge (s.west s.active) s.nextVertex true).west e < s.nextVertex + 1 ∧
            (s.addEdge (s.west s.active) s.nextVertex true).east e < s.nextVertex + 1 := by
        intro e he
        simpa [State.addEdge] using ht e (by simpa [State.addEdge] using he)
      have hnewVertex : s.nextVertex < s.nextVertex + 1 := by omega
      have htu := addEdge_endpoint_bound (s.addEdge (s.west s.active) s.nextVertex true)
        (s.nextVertex + 1) s.nextVertex (s.east s.active) hboundT hnewVertex (by omega)
      intro e he
      have he' : e < (s.addEdge (s.west s.active) s.nextVertex true).nextEdge + 1 := by
        simpa [kmswStepOfStep, State.addEdge] using he
      simpa [kmswStepOfStep, State.addEdge] using htu e he'

private theorem stage_endpoint_bounds (w : ℕ → Fin 3) (n : ℕ) :
    ∀ e < (kmswStage w n).nextEdge,
      (kmswStage w n).west e < (kmswStage w n).nextVertex ∧
      (kmswStage w n).east e < (kmswStage w n).nextVertex := by
  induction n with
  | zero => intro e he; simp [kmswStage, kmswInit] at *
  | succ n ih =>
      exact step_endpoint_bound (kmswStage w n) (w n)
        (stage_edge_ids w n).1 (stage_edge_ids w n).2 ih

/-- Every endpoint of every allocated geometric edge is a vertex ID of the
stage; this includes missing edges (`def-kmsw`, -/
theorem kmswStage_endpoints_lt_nextVertex (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    (kmswStage w n).west e < (kmswStage w n).nextVertex ∧
      (kmswStage w n).east e < (kmswStage w n).nextVertex :=
  stage_endpoint_bounds w n e he

private theorem step_status (s : State) (c : Fin 3)
    (hids : ∀ e ∈ s.UL ++ s.UR ++ s.LL ++ s.LR, e < s.nextEdge)
    (hstatus : ∀ e < s.nextEdge,
      (s.present e = false ↔ e ∈ s.UR ∨ e ∈ s.LL))
    (hUL : ∀ e ∈ s.UL, s.present e = true)
    (hLR : ∀ e ∈ s.LR, s.present e = true)
    (hURnd : s.UR.Nodup) (hLLnd : s.LL.Nodup)
    (hdisj : ∀ e, e ∈ s.UR → e ∈ s.LL → False) :
    (∀ e < (kmswStep s c).nextEdge,
      ((kmswStep s c).present e = false ↔
        e ∈ (kmswStep s c).UR ∨ e ∈ (kmswStep s c).LL)) ∧
    (∀ e ∈ (kmswStep s c).UL, (kmswStep s c).present e = true) ∧
    (∀ e ∈ (kmswStep s c).LR, (kmswStep s c).present e = true) ∧
    (kmswStep s c).UR.Nodup ∧ (kmswStep s c).LL.Nodup ∧
    (∀ e, e ∈ (kmswStep s c).UR → e ∈ (kmswStep s c).LL → False) := by
  have hboundUL : ∀ e ∈ s.UL, e < s.nextEdge := by
    intro e he
    exact hids e (by simp only [List.mem_append]; tauto)
  have hboundULdrop : ∀ e ∈ s.UL.dropLast, e < s.nextEdge := by
    intro e he
    exact hboundUL e (List.dropLast_subset _ he)
  have hpresentULdrop : ∀ e ∈ s.UL.dropLast, s.present e = true := by
    intro e he
    exact hUL e (List.dropLast_subset _ he)
  have hboundUR : ∀ e ∈ s.UR, e < s.nextEdge := by
    intro e he
    exact hids e (by simp only [List.mem_append]; tauto)
  have hboundLL : ∀ e ∈ s.LL, e < s.nextEdge := by
    intro e he
    exact hids e (by simp only [List.mem_append]; tauto)
  have hboundLR : ∀ e ∈ s.LR, e < s.nextEdge := by
    intro e he
    exact hids e (by simp only [List.mem_append]; tauto)
  unfold kmswStep
  cases kmswCodeStep c with
  | down =>
      dsimp only [kmswStepOfStep]
      split <;> simp_all [State.addEdge, List.mem_append, List.mem_cons] <;> grind
  | left =>
      dsimp only [kmswStepOfStep]
      split
      · rename_i e es hs
        have hrev : s.UL.dropLast.reverse = e :: es := by
          rw [hs]
        have hrest : ∀ f ∈ es, f ∈ s.UL := by
          intro f hf
          have hmem : f ∈ s.UL.dropLast.reverse := by
            rw [hrev]
            exact List.mem_cons_of_mem _ hf
          exact List.dropLast_subset _ (List.mem_reverse.mp hmem)
        simp_all [State.addEdge, List.mem_append, List.mem_cons] <;> grind
      · simp_all [State.addEdge, List.mem_append, List.mem_cons] <;> grind
  | up =>
      simp_all [kmswStepOfStep, State.addEdge, List.mem_append, List.mem_cons] <;> grind

private theorem stage_status (w : ℕ → Fin 3) (n : ℕ) :
    (∀ e < (kmswStage w n).nextEdge,
      ((kmswStage w n).present e = false ↔
        e ∈ (kmswStage w n).UR ∨ e ∈ (kmswStage w n).LL)) ∧
    (∀ e ∈ (kmswStage w n).UL, (kmswStage w n).present e = true) ∧
    (∀ e ∈ (kmswStage w n).LR, (kmswStage w n).present e = true) ∧
    (kmswStage w n).UR.Nodup ∧ (kmswStage w n).LL.Nodup ∧
    (∀ e, e ∈ (kmswStage w n).UR → e ∈ (kmswStage w n).LL → False) := by
  induction n with
  | zero => simp [kmswStage, kmswInit]
  | succ n ih =>
      have hs := step_status (kmswStage w n) (w n) (stage_edge_ids w n).2
        ih.1 ih.2.1 ih.2.2.1 ih.2.2.2.1 ih.2.2.2.2.1 ih.2.2.2.2.2
      exact hs

/-- Exact missing-edge status and boundary disjointness in each finite stage:
the missing IDs are `UR ∪ LL`, while `UL` and `LR` are present -/
theorem kmswStage_status (w : ℕ → Fin 3) (n : ℕ) :
    (∀ e < (kmswStage w n).nextEdge,
      ((kmswStage w n).present e = false ↔
        e ∈ (kmswStage w n).UR ∨ e ∈ (kmswStage w n).LL)) ∧
    (∀ e ∈ (kmswStage w n).UL, (kmswStage w n).present e = true) ∧
    (∀ e ∈ (kmswStage w n).LR, (kmswStage w n).present e = true) ∧
    (kmswStage w n).UR.Nodup ∧ (kmswStage w n).LL.Nodup ∧
    (∀ e, e ∈ (kmswStage w n).UR → e ∈ (kmswStage w n).LL → False) :=
  stage_status w n

/-- The upper-left boundary is nonempty and ends at the active edge -/
theorem kmswStage_UL_nonempty_active_last (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).UL ≠ [] ∧
      (kmswStage w n).UL.getLast? = some (kmswStage w n).active := by
  obtain ⟨es, he⟩ := kmswStage_UL_last w n
  constructor
  · intro h
    rw [he] at h
    simp at h
  · rw [he]
    simp

private theorem kmswStage_LR_nonempty_aux (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).LR ≠ [] := by
  intro hLR
  have hlen := kmswStage_LR_length w n
  rw [hLR] at hlen
  simp only [List.length_nil, Nat.cast_zero] at hlen
  have hmin := runningMin_le (R w) n 0 (Nat.zero_le _)
  change minR w n ≤ R w 0 at hmin
  have hzero : R w 0 = 0 := by simp [R]
  rw [hzero] at hmin
  omega

/-- The lower-right boundary remains nonempty, including stage zero -/
theorem kmswStage_LR_nonempty (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).LR ≠ [] :=
  kmswStage_LR_nonempty_aux w n



end DirectedDistances.KMSW
