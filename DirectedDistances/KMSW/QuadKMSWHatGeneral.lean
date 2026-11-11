/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.QuadKMSWHatPhases
public import DirectedDistances.KMSW.FlowLineLPhase
public import DirectedDistances.KMSW.FlowLineEntryFrontier

/-! # Reachable-edge bookkeeping across flow-line phases

The finite reachable part is tracked through alternating phases -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk
open Quiver

/-- A transition whose destination remains in an L-phase adds no reachable
present edge (`lem-flow-line-times`, -/
theorem lPhase_reachablePresentEdges_succ_eq (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k n : ℕ)
    (hle : walkNL w h k ≤ n)
    (hlt : n + 1 < walkNR w h (k + 1)) :
    stageReachablePresentEdges w (n + 1) = stageReachablePresentEdges w n := by
  rw [stageReachablePresentEdges_succ]
  have hnot := lPhase_activeWest_unreachable w h k (n + 1) (by omega) hlt
  have hempty : {e | e = act w (n + 1) ∧
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w (n + 1)).west (act w (n + 1))⟩} = ∅ := by
    ext e
    simp [hnot]
  rw [hempty, Set.union_empty]

/-- The reachable present-edge set is constant throughout the L-phase, up to
but excluding the re-entry time (`lem-flow-line-times`, -/
theorem lPhase_reachablePresentEdges_eq (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k n : ℕ)
    (hle : walkNL w h k ≤ n)
    (hlt : n < walkNR w h (k + 1)) :
    stageReachablePresentEdges w n =
      stageReachablePresentEdges w (walkNL w h k) := by
  induction n, hle using Nat.le_induction with
  | base => rfl
  | succ n hle ih =>
      calc
        stageReachablePresentEdges w (n + 1) =
            stageReachablePresentEdges w n :=
              lPhase_reachablePresentEdges_succ_eq w h k n hle (by omega)
        _ = stageReachablePresentEdges w (walkNL w h k) := ih (by omega)

/-- A transition whose destination remains in an R-phase unions in the new
active edge, since its west endpoint is reachable (`lem-flow-line-times`, -/
theorem rPhase_reachablePresentEdges_succ_eq (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k n : ℕ)
    (hle : walkNR w h k ≤ n)
    (hlt : n + 1 < walkNL w h k) :
    stageReachablePresentEdges w (n + 1) =
      stageReachablePresentEdges w n ∪ {act w (n + 1)} := by
  rw [stageReachablePresentEdges_succ]
  have hreach := flowLine_phase_reachable w h k (n + 1) (by omega) hlt
  have hnew : {e | e = act w (n + 1) ∧
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w (n + 1)).west (act w (n + 1))⟩} =
      {act w (n + 1)} := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl, _⟩
      rfl
    · intro he
      subst e
      exact ⟨rfl, hreach⟩
  rw [hnew]

/-- The transition into the L-phase at `walkNL` adds no reachable present
edge: its new active west endpoint is unreachable. This is the gluing boundary
case at every R-phase exit (`lem-flow-line-times`, -/
theorem rPhase_exit_reachablePresentEdges (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    stageReachablePresentEdges w (walkNL w h k) =
      stageReachablePresentEdges w (walkNL w h k - 1) := by
  let N := walkNL w h k
  have hNpos : 0 < N := by
    have hs := (walkNL_spec w h k).1
    dsimp [N]
    omega
  have hidx : N - 1 + 1 = N := by omega
  have hnot : ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w N).west (act w N)⟩ := by
    simpa [N] using walkNL_activeWest_unreachable w h k
  have hstep : stageReachablePresentEdges w (N - 1 + 1) =
      stageReachablePresentEdges w (N - 1) := by
    rw [stageReachablePresentEdges_succ]
    have hnew : {e | e = act w (N - 1 + 1) ∧
        Reachable (⟨0⟩ : PresentVertex w)
          ⟨(kmswStage w (N - 1 + 1)).west (act w (N - 1 + 1))⟩} = ∅ := by
      ext e
      simp [hidx, hnot]
    rw [hnew, Set.union_empty]
  simpa [N, hidx] using hstep

/-- At L-to-R re-entry, the only possible addition to the reachable present
edge set is the newly active edge, and that edge is reachable from the root -/
theorem lPhase_reentry_reachablePresentEdges (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    stageReachablePresentEdges w (walkNR w h (k + 1)) =
      stageReachablePresentEdges w (walkNR w h (k + 1) - 1) ∪
        {act w (walkNR w h (k + 1))} := by
  let r := walkNR w h (k + 1)
  have hrpos : 0 < r := by
    have hs := (walkNR_succ_spec w h k).1
    dsimp [r]
    omega
  have hidx : r - 1 + 1 = r := by omega
  have hreach := flowLine_entry_all w h (k + 1)
  have hstep : stageReachablePresentEdges w (r - 1 + 1) =
      stageReachablePresentEdges w (r - 1) ∪ {act w (r - 1 + 1)} := by
    rw [stageReachablePresentEdges_succ]
    have hnew : {e | e = act w (r - 1 + 1) ∧
        Reachable (⟨0⟩ : PresentVertex w)
          ⟨(kmswStage w (r - 1 + 1)).west (act w (r - 1 + 1))⟩} =
        {act w (r - 1 + 1)} := by
      ext e
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨rfl, _⟩
        rfl
      · intro he
        subst e
        exact ⟨rfl, by simpa [r, hidx] using hreach⟩
    rw [hnew]
  rw [hidx] at hstep
  simpa [r] using hstep

/-- Across a finite R-phase, the reachable present-edge set is the entry set
adjoined with the active edges encountered at the later R states. Code
correspondence on this interval is `quadrantRStageCodes_at_RPhaseTime` -/
theorem rPhase_reachablePresentEdges_eq (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k n : ℕ)
    (hle : walkNR w h k ≤ n)
    (hlt : n < walkNL w h k) :
    stageReachablePresentEdges w n =
      stageReachablePresentEdges w (walkNR w h k) ∪
        {e | ∃ j, walkNR w h k < j ∧ j ≤ n ∧ e = act w j} := by
  induction n, hle using Nat.le_induction with
  | base =>
      ext e
      change e ∈ stageReachablePresentEdges w (walkNR w h k) ↔
        e ∈ stageReachablePresentEdges w (walkNR w h k) ∨
          ∃ j, walkNR w h k < j ∧ j ≤ walkNR w h k ∧ e = act w j
      constructor
      · exact Or.inl
      · rintro (he | ⟨j, hj, hle, _⟩)
        · exact he
        · omega
  | succ n hle ih =>
      have hstep := rPhase_reachablePresentEdges_succ_eq w h k n hle (by omega)
      have hindices :
          {e | ∃ j, walkNR w h k < j ∧ j ≤ n + 1 ∧ e = act w j} =
            {e | ∃ j, walkNR w h k < j ∧ j ≤ n ∧ e = act w j} ∪
              {act w (n + 1)} := by
        ext e
        change (∃ j, walkNR w h k < j ∧ j ≤ n + 1 ∧ e = act w j) ↔
          (∃ j, walkNR w h k < j ∧ j ≤ n ∧ e = act w j) ∨
            e = act w (n + 1)
        constructor
        · rintro ⟨j, hj, hjn, hje⟩
          by_cases hprev : j ≤ n
          · exact Or.inl ⟨j, hj, hprev, hje⟩
          · right
            have hjEq : j = n + 1 := by omega
            rw [hjEq] at hje
            exact hje
        · rintro (⟨j, hj, hjn, hje⟩ | he)
          · exact ⟨j, hj, by omega, hje⟩
          · exact ⟨n + 1, by omega, by omega, he⟩
      calc
        stageReachablePresentEdges w (n + 1) =
            stageReachablePresentEdges w n ∪ {act w (n + 1)} := hstep
        _ = (stageReachablePresentEdges w (walkNR w h k) ∪
            {e | ∃ j, walkNR w h k < j ∧ j ≤ n ∧ e = act w j}) ∪
              {act w (n + 1)} := by rw [ih (by omega)]
        _ = stageReachablePresentEdges w (walkNR w h k) ∪
            ({e | ∃ j, walkNR w h k < j ∧ j ≤ n ∧ e = act w j} ∪
              {act w (n + 1)}) := Set.union_assoc _ _ _
        _ = stageReachablePresentEdges w (walkNR w h k) ∪
            {e | ∃ j, walkNR w h k < j ∧ j ≤ n + 1 ∧ e = act w j} := by
              rw [← hindices]

/-- At every time in an R-phase, the extracted R stream's current code is
the corresponding global KMSW code (`eqn-quad-pre`,
departing step `w n` at state `n`); `Ẑ` of `eqn-walk-quadrant` differs at each
R-phase exit, where the boundary `(-1,0)` code is replaced. -/
theorem quadrantRStageCodes_at_RPhaseTime (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k n : ℕ)
    (hn : walkNR w h k ≤ n)
    (hnExit : n < walkNL w h k) :
    quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)
        ((quadrantSplitState (quadrantTrajectoryOfStageCodes w) n).rCount) =
      w n := by
  let d := n - walkNR w h k
  have htime : walkNR w h k + d = n := by
    dsimp [d]
    omega
  have hcount := quadrantSplit_rCount_at_RInterval w h k d (by omega)
  rw [← htime, hcount]
  exact quadrantRStageCodes_eq_global_on_RInterval w h k d (by omega)

end DirectedDistances.KMSW
