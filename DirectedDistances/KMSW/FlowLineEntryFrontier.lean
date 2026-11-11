/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.FlowLineStageInvariant
public import DirectedDistances.KMSW.FirstPhaseReach

/-! # Entry reachability for later right flow-line phases


This file proves only the forward direction (R-phase ⇒ reachable). The
converse (L-phase ⇒ not reachable) is proved separately in
`KMSW/FlowLineLPhase.lean` (`lPhase_activeWest_unreachable`), and the iff is
assembled in `KMSW/FlowLineTimesIff.lean`. -/

public section
namespace DirectedDistances.KMSW

open Quiver

private theorem flowL_step_lower_frontier (c : Fin 3) :
    -1 ≤ (RandomWalk.lazyTwoDimensionalStep c).1 := by
  fin_cases c <;> simp [RandomWalk.lazyTwoDimensionalStep]

private theorem flowL_before_firstHit_frontier (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (t n : ℕ) (htn : t ≤ n)
    (hn : n < firstFlowLHit w h t) : L w t ≤ L w n := by
  classical
  change (∀ n, ∃ m, n + 1 ≤ m ∧ L w m = L w n - 1) ∧ _ at h
  have hmin : ∀ j, t + 1 ≤ j → j < firstFlowLHit w h t →
      L w j ≠ L w t - 1 := by
    intro j hj hjhit heq
    change j < Nat.find (h.1 t) at hjhit
    exact (Nat.find_min (h.1 t) hjhit) ⟨hj, heq⟩
  have hbefore : ∀ j, t ≤ j → j < firstFlowLHit w h t → L w t ≤ L w j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hj ih =>
        intro hjhit
        have hs : L w (j + 1) = L w j +
            (RandomWalk.lazyTwoDimensionalStep (w j)).1 := Finset.sum_range_succ _ _
        have hstep : L w j - 1 ≤ L w (j + 1) := by
          rw [hs]
          have hlow := flowL_step_lower_frontier (w j)
          omega
        have hprev := ih (by omega)
        by_contra hlt
        have hneq := hmin (j + 1) (by omega) hjhit
        omega
  exact hbefore n htn hn

private theorem walkNL_eq_firstFlowLHit_frontier (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    walkNL w h k = firstFlowLHit w h (walkNR w h k) := by
  cases k <;> rfl

/-- The initial right entrance is the root and hence is reachable from it -/
theorem flowLine_entry_zero (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (walkNR w h 0)).west (act w (walkNR w h 0))⟩ := by
  rw [walkNR_zero]
  change Reachable (⟨0⟩ : PresentVertex w) ⟨0⟩
  exact Reachable.refl _

/-- Entry reachability implies reachability throughout the following right
flow-line phase, before its first strict left-level drop -/
theorem flowLine_phase_reachable_of_entry (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k n : ℕ)
    (hentry : Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (walkNR w h k)).west (act w (walkNR w h k))⟩)
    (hn : walkNR w h k ≤ n) (hnExit : n < walkNL w h k) :
    Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).west (act w n)⟩ := by
  have htn : walkNR w h k ≤ n := hn
  have hmin : ∀ j, walkNR w h k ≤ j → j ≤ n →
      L w (walkNR w h k) ≤ L w j := by
    intro j hj hjn
    rw [walkNL_eq_firstFlowLHit_frontier] at hnExit
    exact flowL_before_firstHit_frontier w h (walkNR w h k) j hj
      (lt_of_le_of_lt hjn hnExit)
  have hphase := firstPhase_activeWest_reachable w (walkNR w h k) n htn hmin
  exact hentry.trans hphase

private def frontierSampleA (n : ℕ) : Fin 3 :=
  if n = 0 then 0 else if n = 1 then 1 else if n = 2 then 2 else
    if n = 3 then 2 else if (n - 4) % 5 < 3 then 0 else 2

private def frontierSampleB (n : ℕ) : Fin 3 :=
  if n = 0 then 1 else if n = 1 then 1 else if n = 2 then 0 else
    if n = 3 then 0 else 2

private def oldPendingFrontier (w : ℕ → Fin 3) (t : ℕ) : Finset ℕ :=
  ((kmswStage w t).UR.map (kmswStage w t).east).toFinset ∪
    { (kmswStage w t).east (kmswStage w t).active }

private def pendingEastFrontier (s : State) : List ℕ :=
  s.east s.active :: s.UR.map s.east

private theorem pendingEastFrontier_left (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) :
    pendingEastFrontier (kmswStage w (n + 1)) =
      pendingEastFrontier (kmswStage w n) := by
  let s := kmswStage w n
  let t := kmswStage w (n + 1)
  have hUR : t.UR = s.UR := by
    change (kmswStep s (w n)).UR = _
    rw [hc]
    cases hp : s.UL.dropLast.reverse <;>
      simp [kmswStep, kmswCodeStep, kmswStepOfStep, hp, State.addEdge]
  have hEast : t.east t.active = s.east s.active := by
    change (kmswStep s (w n)).east (kmswStep s (w n)).active = _
    rw [hc]
    cases hp : s.UL.dropLast.reverse <;>
      simp [kmswStep, kmswCodeStep, kmswStepOfStep, hp, State.addEdge]
  have hmap : s.UR.map t.east = s.UR.map s.east := by
    apply List.map_congr_left
    intro e he
    have heAll : e ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr he))
    have heBound := (kmswStage_boundary_ids_lt_nextEdge w n).2 e heAll
    exact (kmswStage_endpoints_stable w (Nat.le_succ n) heBound).2
  change t.east t.active :: t.UR.map t.east =
    s.east s.active :: s.UR.map s.east
  rw [hEast, hUR, hmap]

private theorem pendingEastFrontier_up (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) :
    pendingEastFrontier (kmswStage w (n + 1)) =
      (kmswStage w n).nextVertex :: pendingEastFrontier (kmswStage w n) := by
  let s := kmswStage w n
  let t := kmswStage w (n + 1)
  have hUR : t.UR = (s.nextEdge + 1) :: s.UR := by
    change (kmswStep s (w n)).UR = _
    simp [hc, kmswStep, kmswCodeStep, kmswStepOfStep]
  have hEast : t.east t.active = s.nextVertex := by
    change (kmswStep s (w n)).east (kmswStep s (w n)).active = _
    simp [hc, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
  have hNewEast : t.east (s.nextEdge + 1) = s.east s.active := by
    change (kmswStep s (w n)).east (s.nextEdge + 1) = _
    simp [hc, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
  have hmap : s.UR.map t.east = s.UR.map s.east := by
    apply List.map_congr_left
    intro e he
    have heAll : e ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr he))
    have heBound := (kmswStage_boundary_ids_lt_nextEdge w n).2 e heAll
    exact (kmswStage_endpoints_stable w (Nat.le_succ n) heBound).2
  change t.east t.active :: t.UR.map t.east =
    s.nextVertex :: s.east s.active :: s.UR.map s.east
  rw [hEast, hUR, List.map_cons, hNewEast, hmap]

private theorem pendingEastFrontier_down_cons (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (e : ℕ) (es : List ℕ)
    (hUR : (kmswStage w n).UR = e :: es) :
    pendingEastFrontier (kmswStage w n) =
      (kmswStage w n).east (act w n) ::
        pendingEastFrontier (kmswStage w (n + 1)) := by
  let s := kmswStage w n
  let t := kmswStage w (n + 1)
  change s.UR = e :: es at hUR
  have hEast : t.east t.active = s.east e := by
    change (kmswStep s (w n)).east (kmswStep s (w n)).active = s.east e
    rw [hc]
    simp [kmswStep, kmswCodeStep, kmswStepOfStep, hUR]
  have hUR' : t.UR = es := by
    change (kmswStep s (w n)).UR = es
    rw [hc]
    simp [kmswStep, kmswCodeStep, kmswStepOfStep, hUR]
  have hmap : es.map t.east = es.map s.east := by
    apply List.map_congr_left
    intro f hf
    have hfmem : f ∈ s.UR := by rw [hUR]; simp [hf]
    have hfAll : f ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr hfmem))
    have hfBound := (kmswStage_boundary_ids_lt_nextEdge w n).2 f hfAll
    exact (kmswStage_endpoints_stable w (Nat.le_succ n) hfBound).2
  change s.east s.active :: s.UR.map s.east =
    s.east s.active :: (t.east t.active :: t.UR.map t.east)
  rw [hUR, List.map_cons, hEast, hUR', hmap]

private theorem pendingEastFrontier_down_nil (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = []) :
    pendingEastFrontier (kmswStage w (n + 1)) =
      [(kmswStage w n).nextVertex] := by
  let s := kmswStage w n
  let t := kmswStage w (n + 1)
  change t.east t.active :: t.UR.map t.east = _
  simp [t, kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep, hc,
    hUR, State.addEdge]

private theorem pendingEastFrontier_balanced (w : ℕ → Fin 3) {t n : ℕ}
    (htn : t ≤ n)
    (habove : ∀ j, t ≤ j → j ≤ n → R w t ≤ R w j) :
    ∃ p : List ℕ,
      pendingEastFrontier (kmswStage w n) =
        p ++ pendingEastFrontier (kmswStage w t) ∧
      (p.length : ℤ) = R w n - R w t := by
  have haux : ∀ n, t ≤ n →
      (∀ j, t ≤ j → j ≤ n → R w t ≤ R w j) →
      ∃ p : List ℕ,
        pendingEastFrontier (kmswStage w n) =
          p ++ pendingEastFrontier (kmswStage w t) ∧
        (p.length : ℤ) = R w n - R w t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro htn hbound
        by_cases hEq : n = t
        · subst n
          refine ⟨[], ?_, ?_⟩
          · simp
          · simp [R]
        · have hnpos : 0 < n := by omega
          obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
          have htq : t ≤ q := by omega
          have hboundq : ∀ j, t ≤ j → j ≤ q → R w t ≤ R w j := by
            intro j hjt hjq
            exact hbound j hjt (by omega)
          obtain ⟨p, hp, hplen⟩ := ih q (by omega) htq hboundq
          have hpost : R w t ≤ R w (q + 1) := hbound (q + 1) (by omega) le_rfl
          have hRstep : R w (q + 1) = R w q +
              (RandomWalk.lazyTwoDimensionalStep (w q)).2 := Finset.sum_range_succ _ _
          by_cases hc0 : w q = 0
          · have hcode : (RandomWalk.lazyTwoDimensionalStep (w q)).2 = 0 := by
              simp [hc0, RandomWalk.lazyTwoDimensionalStep]
            have hpending := pendingEastFrontier_left w q hc0
            refine ⟨p, ?_, ?_⟩
            · simpa [hRstep, hcode] using hpending.trans hp
            · rw [hRstep, hcode]
              omega
          · by_cases hc1 : w q = 1
            · have hcode : (RandomWalk.lazyTwoDimensionalStep (w q)).2 = 1 := by
                simp [hc1, RandomWalk.lazyTwoDimensionalStep]
              have hpending := pendingEastFrontier_up w q hc1
              refine ⟨(kmswStage w q).nextVertex :: p, ?_, ?_⟩
              · rw [hpending, hp]
                simp [List.cons_append]
              · simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
                rw [hRstep, hcode]
                omega
            · have hc2 : w q = 2 := by
                apply Fin.ext
                have hval := (w q).isLt
                have hnot0 : (w q).val ≠ 0 := by
                  intro hv
                  exact hc0 (Fin.ext hv)
                have hnot1 : (w q).val ≠ 1 := by
                  intro hv
                  exact hc1 (Fin.ext hv)
                omega
              have hcode : (RandomWalk.lazyTwoDimensionalStep (w q)).2 = -1 := by
                simp [hc2, RandomWalk.lazyTwoDimensionalStep]
              have hnet : 1 ≤ R w q - R w t := by
                rw [hRstep, hcode] at hpost
                omega
              have hpPos : 0 < p.length := by
                have : (0 : ℤ) < (p.length : ℤ) := by rw [hplen]; omega
                exact_mod_cast this
              have hpne : p ≠ [] := by
                intro he
                simp [he] at hpPos
              obtain ⟨a, ps, rfl⟩ := List.exists_cons_of_ne_nil hpne
              have hURne : (kmswStage w q).UR ≠ [] := by
                intro hUR
                have hlenOld : (pendingEastFrontier (kmswStage w q)).length = 1 := by
                  simp [pendingEastFrontier, hUR]
                have hbasePos : 0 <
                    (pendingEastFrontier (kmswStage w t)).length := by
                  simp [pendingEastFrontier]
                rw [hp] at hlenOld
                simp only [List.length_append, List.length_cons] at hlenOld
                omega
              obtain ⟨e, es, hUR⟩ : ∃ e es, (kmswStage w q).UR = e :: es := by
                cases h : (kmswStage w q).UR with
                | nil => exact (hURne h).elim
                | cons e es => exact ⟨e, es, rfl⟩
              have hpop := pendingEastFrontier_down_cons w q hc2 e es hUR
              have htail : ps ++ pendingEastFrontier (kmswStage w t) =
                  pendingEastFrontier (kmswStage w (q + 1)) := by
                have hcons : a :: (ps ++ pendingEastFrontier (kmswStage w t)) =
                    (kmswStage w q).east (act w q) ::
                      pendingEastFrontier (kmswStage w (q + 1)) := by
                  simpa [List.cons_append] using hp.symm.trans hpop
                exact congrArg List.tail hcons
              refine ⟨ps, htail.symm, ?_⟩
              simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hplen
              rw [hRstep, hcode]
              omega
  exact haux n htn habove

private theorem flowR_step_lower_frontier (c : Fin 3) :
    -1 ≤ (RandomWalk.lazyTwoDimensionalStep c).2 := by
  fin_cases c <;> simp [RandomWalk.lazyTwoDimensionalStep]

private theorem flowR_before_firstHit_frontier (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (t n : ℕ) (htn : t ≤ n)
    (hn : n < firstFlowRHit w h t) : R w t ≤ R w n := by
  classical
  change _ ∧ (∀ n, ∃ m, n + 1 ≤ m ∧ R w m = R w n - 1) at h
  have hmin : ∀ j, t + 1 ≤ j → j < firstFlowRHit w h t →
      R w j ≠ R w t - 1 := by
    intro j hj hjhit heq
    change j < Nat.find (h.2 t) at hjhit
    exact (Nat.find_min (h.2 t) hjhit) ⟨hj, heq⟩
  have hbefore : ∀ j, t ≤ j → j < firstFlowRHit w h t → R w t ≤ R w j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hj ih =>
        intro hjhit
        have hs : R w (j + 1) = R w j +
            (RandomWalk.lazyTwoDimensionalStep (w j)).2 := Finset.sum_range_succ _ _
        have hstep : R w j - 1 ≤ R w (j + 1) := by
          rw [hs]
          have hlow := flowR_step_lower_frontier (w j)
          omega
        have hprev := ih (by omega)
        by_contra hlt
        have hneq := hmin (j + 1) (by omega) hjhit
        omega
  exact hbefore n htn hn

private theorem walkNR_succ_previous_R_frontier (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    R w (walkNR w h (k + 1) - 1) = R w (walkNL w h k) := by
  have hstep := walkNR_succ_previous_step w h k
  have hhit := (walkNR_succ_spec w h k).2
  have hdelta := congrArg Prod.snd hstep
  omega

private theorem left_activeEast_frontier (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) :
    (kmswStage w (n + 1)).east (act w (n + 1)) =
      (kmswStage w n).east (act w n) := by
  cases hpred : (kmswStage w n).UL.dropLast.reverse with
  | nil =>
      simp [act, kmswStage, kmswStep, kmswCodeStep, hc,
        kmswStepOfStep, hpred, State.addEdge]
  | cons e es =>
      simp [act, kmswStage, kmswStep, kmswCodeStep, hc,
        kmswStepOfStep, hpred, State.addEdge]

/-- The next right entrance is reachable from the root when the current one
right-coordinate excursion (`lem-flow-line-times`, -/
theorem flowLine_entry_succ (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ)
    (hentry : Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (walkNR w h k)).west (act w (walkNR w h k))⟩) :
    Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (walkNR w h (k + 1))).west
        (act w (walkNR w h (k + 1)))⟩ := by
  let t := walkNL w h k
  let r := walkNR w h (k + 1)
  let u := t - 1
  let q := r - 1
  have hleftSpec := walkNL_spec w h k
  have hphaseIndex : walkNR w h k ≤ u := by dsimp [u, t]; omega
  have hphaseExit : u < t := by dsimp [u, t]; omega
  have hrootWestU := flowLine_phase_reachable_of_entry w h k u hentry
    hphaseIndex hphaseExit
  have huCode : w u = 0 := by
    dsimp [u, t]
    exact walkNL_previous_code w h k
  have hrootEastU := kmswStage_activeEast_reachable w u hrootWestU
  have hleftEast := left_activeEast_frontier w u huCode
  have huSucc : u + 1 = t := by dsimp [u]; omega
  have hleftEastT : (kmswStage w t).east (act w t) =
      (kmswStage w u).east (act w u) := by
    simpa [huSucc] using hleftEast
  have hrootEastT : Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w t).east (act w t)⟩ := by
    rw [hleftEastT]
    exact hrootEastU
  have hrightSpec := walkNR_succ_spec w h k
  have hqsucc : q + 1 = r := by dsimp [q, r]; omega
  have htq : t ≤ q := by dsimp [t, q, r]; omega
  have hrHit : r = firstFlowRHit w h t := by
    dsimp [r, t, walkNR, walkNL, flowLineTimes]
  have hRabove : ∀ j, t ≤ j → j ≤ q → R w t ≤ R w j := by
    intro j hjt hjq
    have hjr : j < r := by dsimp [q] at hjq; omega
    have hjhit : j < firstFlowRHit w h t := by rw [← hrHit]; exact hjr
    exact flowR_before_firstHit_frontier w h t j hjt hjhit
  obtain ⟨p, hp, hplen⟩ := pendingEastFrontier_balanced w htq hRabove
  have hRprev : R w q = R w t := by
    have h := walkNR_succ_previous_R_frontier w h k
    simpa [q, r, t] using h
  have hpLenZero : p.length = 0 := by
    have hcast : (p.length : ℤ) = 0 := by rw [hplen, hRprev]; omega
    exact_mod_cast hcast
  have hpNil : p = [] := List.length_eq_zero_iff.mp hpLenZero
  have hpending : pendingEastFrontier (kmswStage w q) =
      pendingEastFrontier (kmswStage w t) := by
    simpa [hpNil] using hp
  have hEastEq : (kmswStage w q).east (act w q) =
      (kmswStage w t).east (act w t) := by
    have hh := congrArg List.head? hpending
    have hh' : some ((kmswStage w q).east (kmswStage w q).active) =
        some ((kmswStage w t).east (kmswStage w t).active) := by
      simpa [pendingEastFrontier] using hh
    exact Option.some.inj hh'
  have hdown : w q = 2 := by
    have hc := walkNR_succ_previous_code w h k
    simpa [q, r] using hc
  have hstage : kmswStage w r =
      kmswStepOfStep (kmswStage w q) .down := by
    rw [← hqsucc]
    change kmswStep (kmswStage w q) (w q) = _
    rw [hdown]
    rfl
  have hwestEq : (kmswStage w r).west (act w r) =
      (kmswStage w q).east (act w q) := by
    change (kmswStage w r).west (kmswStage w r).active = _
    rw [hstage]
    cases hUR : (kmswStage w q).UR with
    | nil => simp [act, kmswStepOfStep, hUR, State.addEdge]
    | cons e es =>
        obtain ⟨_, _, _, _, _, hhead, _⟩ := kmswStage_boundary_chain_invariant w q
        simp [act, kmswStepOfStep, hUR, hhead e es hUR]
  change Reachable (⟨0⟩ : PresentVertex w)
    ⟨(kmswStage w r).west (act w r)⟩
  rw [hwestEq, hEastEq]
  exact hrootEastT

/-- Every right flow-line entrance is reachable from the root, by induction -/
theorem flowLine_entry_all (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (walkNR w h k)).west (act w (walkNR w h k))⟩ := by
  induction k with
  | zero => exact flowLine_entry_zero w h
  | succ k ih => exact flowLine_entry_succ w h k ih

/-- Every active west vertex from a right entrance up to, but not including,
the following left exit is root-reachable (`lem-flow-line-times`,
(R-phase ⇒ reachable); the converse (L-phase ⇒ not reachable) is
`lPhase_activeWest_unreachable` in `KMSW/FlowLineLPhase.lean`, and the iff is
assembled in `KMSW/FlowLineTimesIff.lean`. -/
theorem flowLine_phase_reachable (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k n : ℕ) (hn : walkNR w h k ≤ n) (hnExit : n < walkNL w h k) :
    Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).west (act w n)⟩ := by
  exact flowLine_phase_reachable_of_entry w h k n (flowLine_entry_all w h k)
    hn hnExit

private theorem frontierSampleA_data :
    (∀ v ∈ oldPendingFrontier frontierSampleA 5,
      v ∈ stageReachableVertices frontierSampleA 5) ∧
    (kmswStage frontierSampleA 7).east (act frontierSampleA 7) ∈
      oldPendingFrontier frontierSampleA 5 := by
  decide

private theorem frontierSampleB_data :
    (∀ v ∈ oldPendingFrontier frontierSampleB 3,
      v ∈ stageReachableVertices frontierSampleB 3) ∧
    (kmswStage frontierSampleB 4).east (act frontierSampleB 4) ∈
      oldPendingFrontier frontierSampleB 3 := by
  decide

end DirectedDistances.KMSW
