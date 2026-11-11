/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.QuadKMSWHat
import DirectedDistances.KMSW.PhaseTimesBridge

/-! # Later phase bookkeeping for the reachable KMSW map

Phase-boundary code identities toward `eqn-quad-pre`, -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk
open Quiver

private theorem phase_lazyStep_snd_lower (c : Fin 3) :
    -1 ≤ (lazyTwoDimensionalStep c).2 := by
  fin_cases c <;> simp [lazyTwoDimensionalStep]

private theorem phase_R_ge_before_firstFlowRHit (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (t : ℕ) :
    ∀ n, t ≤ n → n < firstFlowRHit w h t → R w t ≤ R w n := by
  intro n htn
  induction n, htn using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ n htn ih =>
      intro hhit
      have hstep : R w (n + 1) = R w n + (lazyTwoDimensionalStep (w n)).2 :=
        Finset.sum_range_succ _ _
      have hlow : R w n - 1 ≤ R w (n + 1) := by
        rw [hstep]
        have := phase_lazyStep_snd_lower (w n)
        omega
      have hnot : R w (n + 1) ≠ R w t - 1 := by
        intro hEq
        change n + 1 < Nat.find (h.2 t) at hhit
        have hmin := Nat.find_min (h.2 t) hhit
        exact hmin ⟨by omega, hEq⟩
      have hprev := ih (by omega)
      rw [hstep]
      omega

private theorem stage_succ_present_old_or_active (w : ℕ → Fin 3)
    (n e : ℕ) (he : e < (kmswStage w (n + 1)).nextEdge)
    (hp : (kmswStage w (n + 1)).present e = true) :
    (e < (kmswStage w n).nextEdge ∧ (kmswStage w n).present e = true) ∨
      e = act w (n + 1) := by
  have hcode : w n = 0 ∨ w n = 1 ∨ w n = 2 := by
    have hlt := (w n).isLt
    have hval : (w n).val = 0 ∨ (w n).val = 1 ∨ (w n).val = 2 := by omega
    rcases hval with hzero | hone | htwo
    · exact Or.inl (Fin.ext hzero)
    · exact Or.inr (Or.inl (Fin.ext hone))
    · exact Or.inr (Or.inr (Fin.ext htwo))
  by_cases heold : e < (kmswStage w n).nextEdge
  · have hpstep : (kmswStep (kmswStage w n) (w n)).present e = true := by
      simpa [kmswStage] using hp
    rw [kmswStep_present_existing _ _ heold] at hpstep
    by_cases hactive : e = act w (n + 1)
    · exact Or.inr hactive
    · left
      refine ⟨heold, ?_⟩
      have hnotStep : e ≠ (kmswStep (kmswStage w n) (w n)).active := by
        intro hstep
        apply hactive
        simpa [kmswStage, act] using hstep
      simpa [hnotStep] using hpstep
  · have hge : (kmswStage w n).nextEdge ≤ e := by omega
    rcases hcode with hzero | hone | htwo
    · cases hu : (kmswStage w n).UL.dropLast.reverse <;>
        simp [kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep, hzero,
          hu, State.addEdge, act] at he hp ⊢ <;> omega
    · simp [kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep,
        hone, State.addEdge, act] at he hp ⊢
      omega
    · cases hu : (kmswStage w n).UR <;>
        simp [kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep, htwo,
          hu, State.addEdge, act] at he hp ⊢ <;> omega

/-- Present stage edges whose two endpoints are reachable from the global -/
@[expose] def stageReachablePresentEdges (w : ℕ → Fin 3) (n : ℕ) : Set ℕ :=
  {e | e < (kmswStage w n).nextEdge ∧
    (kmswStage w n).present e = true ∧
    Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w n).west e⟩ ∧
    Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w n).east e⟩}

/-- From one stage to the next, the reachable present-edge set can gain only
the new active edge, and it gains it exactly when that edge's west endpoint is
reachable (`lem-flow-line-times`, -/
theorem stageReachablePresentEdges_succ (w : ℕ → Fin 3) (n : ℕ) :
    stageReachablePresentEdges w (n + 1) =
      stageReachablePresentEdges w n ∪
        {e | e = act w (n + 1) ∧
          Reachable (⟨0⟩ : PresentVertex w)
            ⟨(kmswStage w (n + 1)).west (act w (n + 1))⟩} := by
  ext e
  constructor
  · intro he
    change e < (kmswStage w (n + 1)).nextEdge ∧
      (kmswStage w (n + 1)).present e = true ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w (n + 1)).west e⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w (n + 1)).east e⟩ at he
    obtain ⟨heBound, hePresent, hwest, heast⟩ := he
    rcases stage_succ_present_old_or_active w n e heBound hePresent with hold | hactive
    · left
      obtain ⟨heOld, hpOld⟩ := hold
      have hEnds := kmswStage_endpoints_stable w (Nat.le_succ n) heOld
      refine ⟨heOld, hpOld, ?_, ?_⟩
      · rw [← hEnds.1]
        exact hwest
      · rw [← hEnds.2]
        exact heast
    · right
      refine ⟨hactive, ?_⟩
      simpa [hactive] using hwest
  · intro he
    change e ∈ stageReachablePresentEdges w n ∨
      e ∈ {e | e = act w (n + 1) ∧
        Reachable (⟨0⟩ : PresentVertex w)
          ⟨(kmswStage w (n + 1)).west (act w (n + 1))⟩} at he
    rcases he with hold | hnew
    · change e < (kmswStage w n).nextEdge ∧
        (kmswStage w n).present e = true ∧
        Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w n).west e⟩ ∧
        Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w n).east e⟩ at hold
      obtain ⟨heOld, hpOld, hwest, heast⟩ := hold
      have heNew := heOld.trans_le (kmswStage_nextEdge_mono w (Nat.le_succ n))
      have hpNew : (kmswStage w (n + 1)).present e = true := by
        change (kmswStep (kmswStage w n) (w n)).present e = true
        rw [kmswStep_present_existing _ _ heOld]
        split <;> simp [hpOld]
      have hEnds := kmswStage_endpoints_stable w (Nat.le_succ n) heOld
      exact ⟨heNew, hpNew, by rw [hEnds.1]; exact hwest,
        by rw [hEnds.2]; exact heast⟩
    · obtain ⟨rfl, hwest⟩ := hnew
      exact ⟨act_lt_nextEdge w (Nat.le_refl (n + 1)),
        kmswStage_active_present w (n + 1), hwest,
        kmswStage_activeEast_reachable w (n + 1) hwest⟩

/-- The first gluing triangle adds no edge whose two endpoints are reachable:
the old active edge remains, while the new active edge has an unreachable
west endpoint (`lem-flow-line-times`, -/
theorem quadrantFirstR_exit_reachablePresentEdges (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    stageReachablePresentEdges w (walkNL w h 0) =
      stageReachablePresentEdges w (walkNL w h 0 - 1) := by
  let n := walkNL w h 0 - 1
  have hNpos := (quadrantFirstR_exit_predecessor_emptyUL w h).1
  have hidx : n + 1 = walkNL w h 0 := by dsimp [n]; omega
  have hnot : ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (n + 1)).west (act w (n + 1))⟩ := by
    rw [hidx]
    exact quadrantFirstR_exit_activeWest_unreachable w h
  have hstep : stageReachablePresentEdges w (n + 1) =
      stageReachablePresentEdges w n := by
    rw [stageReachablePresentEdges_succ]
    have hnew : {e | e = act w (n + 1) ∧
        Reachable (⟨0⟩ : PresentVertex w)
          ⟨(kmswStage w (n + 1)).west (act w (n + 1))⟩} = ∅ := by
      ext e
      simp [hnot]
    rw [hnew, Set.union_empty]
  simpa [n, hidx] using hstep

/-- edge to activate (`lem-flow-line-times`, -/
theorem kmswLPhase_down_before_reentry_UR_nonempty (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k n : ℕ)
    (hn : walkNL w h k ≤ n)
    (hbefore : n + 1 < walkNR w h (k + 1))
    (hdown : w n = 2) :
    (kmswStage w n).UR ≠ [] := by
  let t := walkNL w h k
  have htime : walkNR w h (k + 1) = firstFlowRHit w h t := rfl
  have hnHit : n < firstFlowRHit w h t := by rw [← htime]; omega
  have hRge := phase_R_ge_before_firstFlowRHit w h t n (by simpa [t] using hn) hnHit
  have hRstrict : R w t < R w n := by
    by_contra hnot
    have hEq : R w n = R w t := by omega
    have hstep : R w (n + 1) = R w n - 1 := by
      have hs : R w (n + 1) = R w n + (lazyTwoDimensionalStep (w n)).2 :=
        Finset.sum_range_succ _ _
      rw [hs, hdown, RandomWalk.lazyTwoDimensionalStep_two]
      omega
    have hnotHit : R w (n + 1) ≠ R w t - 1 := by
      intro hEq'
      have hfirst : n + 1 < Nat.find (h.2 t) := by
        change n + 1 < firstFlowRHit w h t
        rw [← htime]
        exact hbefore
      exact (Nat.find_min (h.2 t) hfirst) ⟨by omega, hEq'⟩
    exact hnotHit (by rw [hstep, hEq])
  have hminR : minR w n ≤ R w t := by
    have hm := runningMin_le (R w) n t (by simpa [t] using hn)
    exact hm
  have hlen := kmswStage_UR_length w n
  change ((kmswStage w n).UR.length : ℤ) = R w n - minR w n at hlen
  intro hUR
  rw [hUR] at hlen
  simp only [List.length_nil, Nat.cast_zero] at hlen
  omega

/-- At every R-phase state, the next extracted R code is the next global -/
theorem quadrantRStageCodes_at_RState (w : ℕ → Fin 3)
    (n : ℕ) (hphase :
      (quadrantSplitState (quadrantTrajectoryOfStageCodes w) n).phase = .r) :
    quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)
        ((quadrantSplitState (quadrantTrajectoryOfStageCodes w) n).rCount) =
      w n := by
  let ω := quadrantTrajectoryOfStageCodes w
  have hcode := phaseSplit_rCode_at_walk_step ω n hphase
  simpa [quadrantRStageCodes, ω, quadrantTrajectoryOfStageCodes] using hcode

/-- At an R-phase re-entry, the next extracted R code is precisely the next
global code at `walkNR` (`eqn-quad-pre`, -/
theorem quadrantRStageCodes_at_reentry (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)
        ((quadrantSplitState (quadrantTrajectoryOfStageCodes w)
          (walkNR w h (k + 1))).rCount) =
      w (walkNR w h (k + 1)) := by
  let ω := quadrantTrajectoryOfStageCodes w
  have hphase := (quadrantSplitState_at_walkNR ω h (k + 1)).1
  exact quadrantRStageCodes_at_RState w (walkNR w h (k + 1)) hphase

/-- During a right flow-line interval, one extracted R code is consumed at
each global step, including its terminating boundary code (`eqn-quad-pre`, -/
theorem quadrantSplit_rCount_at_RInterval (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k d : ℕ)
    (hd : walkNR w h k + d ≤ walkNL w h k) :
    (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
      (walkNR w h k + d)).rCount =
    (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
      (walkNR w h k)).rCount + d := by
  let ω := quadrantTrajectoryOfStageCodes w
  have htimeR : walkNR (fun i => ω (i + 1)) h k = walkNR w h k := rfl
  have htimeL : walkNL (fun i => ω (i + 1)) h k = walkNL w h k := rfl
  induction d with
  | zero => simp
  | succ d ih =>
      have hd' : walkNR w h k + d ≤ walkNL w h k := by omega
      have hphase : (quadrantSplitState ω (walkNR w h k + d)).phase = .r := by
        apply (quadrantSplitState_rPhase_iff ω h (walkNR w h k + d)).2
        exact ⟨k, by rw [htimeR]; omega, by rw [htimeL]; omega⟩
      have hprev := ih hd'
      have hcountStep :
          (quadrantSplitState ω (walkNR w h k + d + 1)).rCount =
            (quadrantSplitState ω (walkNR w h k + d)).rCount + 1 := by
        simp [quadrantSplitState, quadrantSplitAdvance_rCount, hphase]
      rw [show walkNR w h k + (d + 1) =
        (walkNR w h k + d) + 1 by omega]
      rw [hcountStep, hprev]
      omega

/-- On a right flow-line interval, the corresponding consecutive entries of
the extracted R code sequence agree with the global codes -/
theorem quadrantRStageCodes_eq_global_on_RInterval (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k d : ℕ)
    (hd : walkNR w h k + d < walkNL w h k) :
    quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)
        ((quadrantSplitState (quadrantTrajectoryOfStageCodes w)
          (walkNR w h k)).rCount + d) =
      w (walkNR w h k + d) := by
  let ω := quadrantTrajectoryOfStageCodes w
  have htimeR : walkNR (fun i => ω (i + 1)) h k = walkNR w h k := rfl
  have htimeL : walkNL (fun i => ω (i + 1)) h k = walkNL w h k := rfl
  have hphase : (quadrantSplitState ω (walkNR w h k + d)).phase = .r := by
    apply (quadrantSplitState_rPhase_iff ω h (walkNR w h k + d)).2
    exact ⟨k, by rw [htimeR]; omega, by rw [htimeL]; omega⟩
  have hcount := quadrantSplit_rCount_at_RInterval w h k d (by omega)
  rw [← hcount]
  exact quadrantRStageCodes_at_RState w (walkNR w h k + d) hphase

/-- The R code counter does not change while the splitter is in an L-phase,
including the final code that returns it to the R phase (`eqn-quad-pre`, -/
theorem quadrantSplit_rCount_at_LInterval (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k d : ℕ)
    (hd : walkNL w h k + d ≤ walkNR w h (k + 1)) :
    (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
      (walkNL w h k + d)).rCount =
    (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
      (walkNL w h k)).rCount := by
  let ω := quadrantTrajectoryOfStageCodes w
  have htimeL : walkNL (fun i => ω (i + 1)) h k = walkNL w h k := rfl
  have htimeR : walkNR (fun i => ω (i + 1)) h (k + 1) =
      walkNR w h (k + 1) := rfl
  induction d with
  | zero => simp
  | succ d ih =>
      have hd' : walkNL w h k + d ≤ walkNR w h (k + 1) := by omega
      have hphase : (quadrantSplitState ω (walkNL w h k + d)).phase = .l := by
        apply (quadrantSplitState_lPhase_iff ω h (walkNL w h k + d)).2
        exact ⟨k, by rw [htimeL]; omega, by rw [htimeR]; omega⟩
      have hprev := ih hd'
      have hcountStep :
          (quadrantSplitState ω (walkNL w h k + d + 1)).rCount =
            (quadrantSplitState ω (walkNL w h k + d)).rCount := by
        simp [quadrantSplitState, quadrantSplitAdvance_rCount, hphase]
      rw [show walkNL w h k + (d + 1) =
        (walkNL w h k + d) + 1 by omega]
      rw [hcountStep, hprev]

/-- At re-entry, the next R code is indexed immediately after the R counter
at the preceding L-phase entry (`eqn-quad-pre`, -/
theorem quadrantRStageCodes_at_reentry_after_LInterval (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)
        ((quadrantSplitState (quadrantTrajectoryOfStageCodes w)
          (walkNL w h k)).rCount) =
      w (walkNR w h (k + 1)) := by
  have hgap := (walkNR_succ_spec w h k).1
  have hNRpos : walkNL w h k ≤ walkNR w h (k + 1) := by omega
  have hcount := quadrantSplit_rCount_at_LInterval w h k
    (walkNR w h (k + 1) - walkNL w h k) (by omega)
  have hindex : walkNL w h k +
      (walkNR w h (k + 1) - walkNL w h k) = walkNR w h (k + 1) := by omega
  have hcount' :
      (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
        (walkNR w h (k + 1))).rCount =
      (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
        (walkNL w h k)).rCount := by
    rw [← hindex]
    exact hcount
  rw [← hcount']
  exact quadrantRStageCodes_at_reentry w h k

end DirectedDistances.KMSW
