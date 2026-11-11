/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.FlowLineReachability
public import DirectedDistances.KMSW.BoundaryEnumeration
import Mathlib.Tactic.FinCases
meta import Lean.Elab.Tactic.Omega

/-! # First-phase reachability along the lower boundary

Reachability consequences of the flow-line and first-hit constructions in -/

public section
namespace DirectedDistances.KMSW

open Quiver
open MeasureTheory
open scoped Classical

private theorem firstPhase_L_succ (w : ℕ → Fin 3) (n : ℕ) :
    L w (n + 1) = L w n + (RandomWalk.lazyTwoDimensionalStep (w n)).1 := by
  exact Finset.sum_range_succ _ _

private theorem firstPhase_lazy_L_step_bounds (c : Fin 3) :
    -1 ≤ (RandomWalk.lazyTwoDimensionalStep c).1 ∧
      (RandomWalk.lazyTwoDimensionalStep c).1 ≤ 1 := by
  fin_cases c <;> simp [RandomWalk.lazyTwoDimensionalStep]

private theorem firstPhase_L_step_bounds (w : ℕ → Fin 3) (n : ℕ) :
    -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).1 ∧
      (RandomWalk.lazyTwoDimensionalStep (w n)).1 ≤ 1 :=
  firstPhase_lazy_L_step_bounds (w n)

private theorem firstPhase_lazy_L_delta_eq_neg_one_iff (c : Fin 3) :
    (RandomWalk.lazyTwoDimensionalStep c).1 = -1 ↔ c = 0 := by
  fin_cases c <;> simp [RandomWalk.lazyTwoDimensionalStep]

private theorem firstPhase_exists_level_down (f : ℕ → ℤ)
    (hstep : ∀ j, f j - 1 ≤ f (j + 1)) {a : ℤ} {t n : ℕ}
    (htn : t ≤ n) (hstart : a ≤ f t) (hend : f n ≤ a) :
    ∃ m, t ≤ m ∧ m ≤ n ∧ f m = a := by
  induction n generalizing t with
  | zero =>
      have ht : t = 0 := by omega
      subst t
      have hvalue : f 0 = a := by omega
      exact ⟨0, le_rfl, le_rfl, hvalue⟩
  | succ n ih =>
      by_cases hfinal : f (n + 1) = a
      · exact ⟨n + 1, by omega, le_rfl, hfinal⟩
      · have htn' : t ≤ n := by
          by_contra h
          have ht : t = n + 1 := by omega
          rw [ht] at hstart
          have : f (n + 1) = a := by omega
          exact hfinal this
        by_cases hprev : f n ≤ a
        · obtain ⟨m, htm, hmn, hm⟩ := ih htn' hstart hprev
          exact ⟨m, htm, by omega, hm⟩
        · have hgt : a < f n := by omega
          have hlow := hstep n
          have hval : f n = a + 1 := by omega
          have hge : a ≤ f (n + 1) := by rw [hval] at hlow; omega
          have : f (n + 1) = a := by omega
          exact False.elim (hfinal this)

private theorem firstPhase_exists_level_up (f : ℕ → ℤ)
    (hstep : ∀ j, f (j + 1) ≤ f j + 1) {a : ℤ} {t n : ℕ}
    (htn : t ≤ n) (hstart : f t ≤ a) (hend : a ≤ f n) :
    ∃ m, t ≤ m ∧ m ≤ n ∧ f m = a := by
  induction n generalizing t with
  | zero =>
      have ht : t = 0 := by omega
      subst t
      have hvalue : f 0 = a := by omega
      exact ⟨0, le_rfl, le_rfl, hvalue⟩
  | succ n ih =>
      by_cases hfinal : f (n + 1) = a
      · exact ⟨n + 1, by omega, le_rfl, hfinal⟩
      · have htn' : t ≤ n := by
          by_contra h
          have ht : t = n + 1 := by omega
          rw [ht] at hstart
          have : f (n + 1) = a := by omega
          exact hfinal this
        by_cases hprev : a ≤ f n
        · obtain ⟨m, htm, hmn, hm⟩ := ih htn' hstart hprev
          exact ⟨m, htm, by omega, hm⟩
        · have hlt : f n < a := by omega
          have hup := hstep n
          have hle : f (n + 1) ≤ a := by omega
          have : f (n + 1) = a := by omega
          exact False.elim (hfinal this)

private theorem firstPhase_L_succ_lower (w : ℕ → Fin 3) (n : ℕ) :
    L w n - 1 ≤ L w (n + 1) := by
  rw [firstPhase_L_succ]
  have h := firstPhase_L_step_bounds w n
  omega

private theorem firstPhase_L_succ_upper (w : ℕ → Fin 3) (n : ℕ) :
    L w (n + 1) ≤ L w n + 1 := by
  rw [firstPhase_L_succ]
  have h := firstPhase_L_step_bounds w n
  omega

private theorem firstPhase_exists_last_level (f : ℕ → ℤ) {a : ℤ}
    {t n : ℕ} (htn : t ≤ n)
    (hhit : ∃ j, t ≤ j ∧ j ≤ n ∧ f j = a) :
    ∃ m, t ≤ m ∧ m ≤ n ∧ f m = a ∧
      ∀ j, m < j → j ≤ n → f j ≠ a := by
  induction n generalizing t with
  | zero =>
      have ht : t = 0 := by omega
      subst t
      obtain ⟨j, hjt, hjn, hja⟩ := hhit
      have hj : j = 0 := by omega
      subst j
      exact ⟨0, le_rfl, le_rfl, hja, by intro j hj; omega⟩
  | succ n ih =>
      by_cases hfinal : f (n + 1) = a
      · exact ⟨n + 1, by omega, le_rfl, hfinal, by intro j hj hjn; omega⟩
      · obtain ⟨j, hjt, hjle, hja⟩ := hhit
        have hjn : j ≤ n := by
          by_contra h
          have hj : j = n + 1 := by omega
          rw [hj] at hja
          exact hfinal hja
        have htn' : t ≤ n := by
          by_contra h
          have ht : t = n + 1 := by omega
          omega
        obtain ⟨m, htm, hmn, hma, hlast⟩ :=
          ih htn' ⟨j, hjt, hjn, hja⟩
        refine ⟨m, htm, by omega, hma, ?_⟩
        intro q hmq hqn
        by_cases hqn' : q ≤ n
        · exact hlast q hmq hqn'
        · have hq : q = n + 1 := by omega
          rw [hq]
          exact hfinal

private theorem firstPhase_after_last_level_ge (f : ℕ → ℤ)
    (hstep : ∀ j, f (j + 1) ≤ f j + 1) {a : ℤ} {m n : ℕ}
    (hma : f m = a)
    (hlast : ∀ j, m < j → j ≤ n → f j ≠ a)
    (hend : a < f n) :
    ∀ j, m ≤ j → j ≤ n → a ≤ f j := by
  intro j hmj hjn
  by_cases hEq : m = j
  · subst j
    rw [hma]
  · have hmj' : m < j := by omega
    by_contra hnot
    have hjlt : f j < a := by omega
    obtain ⟨q, hjq, hqn, hqa⟩ := firstPhase_exists_level_up f hstep
      (a := a) (t := j) (n := n) (by omega) (by omega) (le_of_lt hend)
    exact (hlast q (lt_of_lt_of_le hmj' hjq) hqn) hqa

private theorem firstPhase_activeEast_reachable_from (w : ℕ → Fin 3)
    (n : ℕ) {u : PresentVertex w}
    (hr : Reachable u ⟨(kmswStage w n).west (act w n)⟩) :
    Reachable u ⟨(kmswStage w n).east (act w n)⟩ := by
  have he : act w n < (kmswStage w n).nextEdge := act_lt_nextEdge w (le_rfl)
  have hends := edge_endpoints_eq w he
  obtain ⟨p⟩ := hr
  let a : (⟨(kmswStage w n).west (act w n)⟩ : PresentVertex w) ⟶
      ⟨(kmswStage w n).east (act w n)⟩ :=
    ⟨act w n, ⟨n, he, kmswStage_active_present w n⟩,
      hends.1.symm, hends.2.symm⟩
  exact ⟨p.cons a⟩

private theorem firstPhase_up_activeWest_reachable_from (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) {u : PresentVertex w}
    (hr : Reachable u ⟨(kmswStage w n).west (act w n)⟩) :
    Reachable u ⟨(kmswStage w (n + 1)).west (act w (n + 1))⟩ := by
  have hwest : (kmswStage w (n + 1)).west (act w (n + 1)) =
      (kmswStage w n).west (act w n) := by
    simp [act, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep,
      State.addEdge]
  rw [hwest]
  exact hr

private theorem firstPhase_down_activeWest_reachable_from (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) {u : PresentVertex w}
    (hr : Reachable u ⟨(kmswStage w n).west (act w n)⟩) :
    Reachable u ⟨(kmswStage w (n + 1)).west (act w (n + 1))⟩ := by
  have hEast := firstPhase_activeEast_reachable_from w n hr
  obtain ⟨_, _, _, _, _, hhead, _⟩ := kmswStage_boundary_chain_invariant w n
  have hwest : (kmswStage w (n + 1)).west (act w (n + 1)) =
      (kmswStage w n).east (act w n) := by
    cases hu' : (kmswStage w n).UR with
    | nil =>
        simp [act, kmswStage, kmswStep, kmswCodeStep, hc,
          kmswStepOfStep, hu', State.addEdge]
    | cons e es =>
        have he := hhead e es hu'
        simp [act, kmswStage, kmswStep, kmswCodeStep, hc,
          kmswStepOfStep, hu', he]
  rw [hwest]
  exact hEast

private theorem firstPhase_horizontal_excursion_reachable_from
    (w : ℕ → Fin 3) {m n : ℕ} (hmn : m ≤ n)
    (hlevel : L w m = L w n)
    (habove : ∀ j, m ≤ j → j ≤ n → L w m ≤ L w j)
    {u : PresentVertex w}
    (hr : Reachable u ⟨(kmswStage w m).west (act w m)⟩) :
    Reachable u ⟨(kmswStage w n).west (act w n)⟩ := by
  have hsame := kmsw_west_act_eq_of_level w hmn hlevel habove
  have hstable := (kmswStage_endpoints_stable w hmn
    (act_lt_nextEdge w (le_rfl : m ≤ m))).1
  have hvertex : (kmswStage w n).west (act w n) =
      (kmswStage w m).west (act w m) := hsame.symm.trans hstable
  rw [hvertex]
  exact hr

/-- On every finite interval where `L` attains its minimum at the initial time,
the initial active vertex reaches every later active initial vertex -/
theorem firstPhase_activeWest_reachable (w : ℕ → Fin 3) (t n : ℕ)
    (htn : t ≤ n)
    (hmin : ∀ j, t ≤ j → j ≤ n → L w t ≤ L w j) :
    Reachable (⟨(kmswStage w t).west (act w t)⟩ : PresentVertex w)
      ⟨(kmswStage w n).west (act w n)⟩ := by
  have haux : ∀ N, ∀ t, t ≤ N →
      (∀ j, t ≤ j → j ≤ N → L w t ≤ L w j) →
      Reachable (⟨(kmswStage w t).west (act w t)⟩ : PresentVertex w)
        ⟨(kmswStage w N).west (act w N)⟩ := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
        intro t htn hmin
        cases N with
        | zero =>
          have ht : t = 0 := by omega
          subst t
          exact Reachable.refl _
        | succ p =>
          by_cases htp : t = p + 1
          · subst t
            exact Reachable.refl _
          · have htp' : t ≤ p := by omega
            have hminPrev : ∀ j, t ≤ j → j ≤ p → L w t ≤ L w j := by
              intro j hjt hjN
              exact hmin j hjt (by omega)
            have hr := ih p (by omega) t htp' hminPrev
            by_cases hc0 : w p = 0
            · have hLstep : L w (p + 1) = L w p - 1 := by
                rw [firstPhase_L_succ]
                simp [hc0, RandomWalk.lazyTwoDimensionalStep]
                omega
              let a := L w (p + 1)
              have hstart : L w t ≤ a := by
                dsimp [a]
                exact hmin (p + 1) htn (le_refl _)
              have hprev : a < L w p := by
                change L w (p + 1) < L w p
                rw [hLstep]
                omega
              obtain ⟨q, htq, hqp, hqa⟩ := firstPhase_exists_level_up (L w)
                (firstPhase_L_succ_upper w) (a := a) (t := t) (n := p)
                htp' hstart (le_of_lt hprev)
              obtain ⟨m, htm, hmp, hma, hlast⟩ :=
                firstPhase_exists_last_level (L w) htp'
                  ⟨q, htq, by omega, hqa⟩
              have haboveOld := firstPhase_after_last_level_ge (L w)
                (firstPhase_L_succ_upper w) hma hlast hprev
              have habove : ∀ j, m ≤ j → j ≤ p + 1 → L w m ≤ L w j := by
                intro j hmj hjN
                by_cases hj : j = p + 1
                · rw [hj]
                  rw [hma]
                · have hjp : j ≤ p := by omega
                  have hge := haboveOld j hmj hjp
                  rw [hma]
                  exact hge
              have hlevel : L w m = L w (p + 1) := by
                simpa [a] using hma
              have hminm : ∀ j, t ≤ j → j ≤ m → L w t ≤ L w j := by
                intro j hjt hjm
                exact hmin j hjt (by omega)
              have hrm := ih m (by omega) t htm hminm
              exact firstPhase_horizontal_excursion_reachable_from w (by omega)
                hlevel habove hrm
            · by_cases hc1 : w p = 1
              · exact firstPhase_up_activeWest_reachable_from w p hc1 hr
              · have hc2 : w p = 2 := by
                  apply Fin.ext
                  have hbound := (w p).isLt
                  have hnot0 : (w p).val ≠ 0 := by
                    intro hval
                    exact hc0 (Fin.ext hval)
                  have hnot1 : (w p).val ≠ 1 := by
                    intro hval
                    exact hc1 (Fin.ext hval)
                  omega
                exact firstPhase_down_activeWest_reachable_from w p hc2 hr
  exact haux n t htn hmin

private theorem firstPhase_L_nonneg_before_walkNL (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    ∀ j, j < walkNL w h 0 → 0 ≤ L w j := by
  intro j hj
  by_contra hneg
  have hzero : L w 0 = 0 := by simp [L]
  have hjle : L w j ≤ -1 := by omega
  have hstart : (-1 : ℤ) ≤ L w 0 := by rw [hzero]; norm_num
  obtain ⟨m, hm0, hmj, hhit⟩ := firstPhase_exists_level_down (L w)
    (firstPhase_L_succ_lower w) (a := -1) (t := 0) (n := j)
    (Nat.zero_le _) hstart hjle
  have hmpos : 1 ≤ m := by
    by_contra hm
    have hmzero : m = 0 := by omega
    rw [hmzero, hzero] at hhit
    omega
  have hN : walkNL w h 0 = Nat.find (h.1 0) := rfl
  rw [hN] at hj
  have hmfind : m < Nat.find (h.1 0) := hmj.trans_lt hj
  have hfirst := Nat.find_min (h.1 0) hmfind
  have hpred : 0 + 1 ≤ m ∧ L w m = L w 0 - 1 := by
    constructor
    · omega
    · rw [hzero]
      exact hhit
  exact hfirst hpred

/-- Before the first strict drop of `L` from zero, the root reaches every
active initial vertex (`lem-flow-line-times`, -/
theorem firstPhase_walkNL_reachable (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (n : ℕ) (hn : n < walkNL w h 0) :
    Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).west (act w n)⟩ := by
  have hmin : ∀ j, 0 ≤ j → j ≤ n → L w 0 ≤ L w j := by
    intro j _ hjn
    have hj := firstPhase_L_nonneg_before_walkNL w h j (lt_of_le_of_lt hjn hn)
    have hzero : L w 0 = 0 := by simp [L]
    omega
  have hreach := firstPhase_activeWest_reachable w 0 n (Nat.zero_le _) hmin
  have hroot : (kmswStage w 0).west (act w 0) = 0 := by
    simp [act, kmswStage, kmswInit]
  rw [hroot] at hreach
  exact hreach

private theorem firstPhase_boundaryHitTime_left_eq_find (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    boundaryHitTime w h k = Nat.find (h.leftHit k hk) := by
  unfold boundaryHitTime
  simp only [dite_eq_right (by omega : k ≠ 0),
    dite_eq_right (by omega : ¬ 0 < k)]

private theorem firstPhase_boundaryHitTime_left_record (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    ∀ j, j < boundaryHitTime w h k → k < L w j := by
  intro j hj
  by_contra hnot
  have hjle : L w j ≤ k := by omega
  have hzero : L w 0 = 0 := by simp [L]
  have hstart : k ≤ L w 0 := by rw [hzero]; omega
  obtain ⟨m, _, hmj, hm⟩ := firstPhase_exists_level_down (L w)
    (firstPhase_L_succ_lower w) (a := k) (t := 0)
    (n := j) (Nat.zero_le _) hstart hjle
  have htime := firstPhase_boundaryHitTime_left_eq_find w h hk
  rw [htime] at hj
  have hmfind : m < Nat.find (h.leftHit k hk) := hmj.trans_lt hj
  exact (Nat.find_min (h.leftHit k hk) hmfind) hm

private theorem firstPhase_leftHit_time_strict_succ (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    boundaryHitTime w h (k + 1) < boundaryHitTime w h k := by
  by_cases hq0 : k + 1 = 0
  · have hk' : k = -1 := by omega
    subst k
    rw [show (-1 : ℤ) + 1 = 0 by norm_num, boundaryHitTime_zero]
    have hhit := boundaryHitTime_left_spec w h (by omega)
    have htpos : 0 < boundaryHitTime w h (-1) := by
      by_contra ht
      have ht0 : boundaryHitTime w h (-1) = 0 := by omega
      rw [ht0] at hhit
      simp [L] at hhit
    exact htpos
  · have hq : k + 1 ≤ -1 := by omega
    have hzero : L w 0 = 0 := by simp [L]
    have hstart : k + 1 ≤ L w 0 := by rw [hzero]; omega
    have hhit := boundaryHitTime_left_spec w h hk
    obtain ⟨m, _, hmt, hm⟩ := firstPhase_exists_level_down (L w)
      (firstPhase_L_succ_lower w) (a := k + 1) (t := 0)
      (n := boundaryHitTime w h k) (Nat.zero_le _) hstart (by omega)
    have htime := firstPhase_boundaryHitTime_left_eq_find w h hq
    have hfirst : boundaryHitTime w h (k + 1) ≤ m := by
      rw [htime]
      exact Nat.find_min' (h.leftHit (k + 1) hq) hm
    have hmtlt : m < boundaryHitTime w h k := by
      by_contra hnot
      have heq : m = boundaryHitTime w h k := by omega
      rw [heq, hhit] at hm
      omega
    omega

private theorem firstPhase_leftHit_previous_code (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    w (boundaryHitTime w h k - 1) = 0 := by
  let τ := boundaryHitTime w h k
  let n := τ - 1
  have hhit : L w τ = k := boundaryHitTime_left_spec w h hk
  have hτpos : 0 < τ := by
    dsimp [τ]
    by_contra hpos
    have hτ0 : boundaryHitTime w h k = 0 := by omega
    change L w (boundaryHitTime w h k) = k at hhit
    rw [hτ0] at hhit
    have hzero : L w 0 = 0 := by simp [L]
    omega
  have hsucc : n + 1 = τ := by dsimp [n, τ]; omega
  have hnlt : n < τ := by dsimp [n, τ]; omega
  have hrecord := firstPhase_boundaryHitTime_left_record w h hk n hnlt
  have hprevlo : k + 1 ≤ L w n := by omega
  have hstep := firstPhase_L_succ w n
  rw [hsucc] at hstep
  have hhit' : L w n + (RandomWalk.lazyTwoDimensionalStep (w n)).1 = k := by
    rw [← hstep]
    exact hhit
  have hbound := firstPhase_L_step_bounds w n
  have hpreveq : L w n = k + 1 := by omega
  have hdelta : (RandomWalk.lazyTwoDimensionalStep (w n)).1 = -1 := by
    rw [hpreveq] at hhit'
    omega
  have hcode := (firstPhase_lazy_L_delta_eq_neg_one_iff (w n)).1 hdelta
  simpa [n, τ] using hcode

private theorem firstPhase_left_activeEast_succ (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0) :
    (kmswStage w (n + 1)).east (act w (n + 1)) =
      (kmswStage w n).east (act w n) := by
  cases hleft : (kmswStage w n).UL.dropLast.reverse with
  | nil =>
      simp [act, kmswStage, kmswStep, kmswCodeStep, hc,
        kmswStepOfStep, hleft, State.addEdge]
  | cons e es =>
      simp [act, kmswStage, kmswStep, kmswCodeStep, hc,
        kmswStepOfStep, hleft, State.addEdge]

/-- Consecutive negative-index boundary vertices have a common directed
descendant at the terminal vertex of the active edge immediately before the
first hit of `L = k` (`eqn-bdy-vertex-kmsw` and `lem-flow-line-times`, -/
theorem firstPhase_leftBoundary_commonDescendant (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    Reachable (⟨boundaryVertex w h k⟩ : PresentVertex w)
      ⟨(kmswStage w (boundaryHitTime w h k - 1)).east
        (act w (boundaryHitTime w h k - 1))⟩ ∧
    Reachable (⟨boundaryVertex w h (k + 1)⟩ : PresentVertex w)
      ⟨(kmswStage w (boundaryHitTime w h k - 1)).east
        (act w (boundaryHitTime w h k - 1))⟩ := by
  let τ := boundaryHitTime w h k
  let n := τ - 1
  let t := boundaryHitTime w h (k + 1)
  have htimeOrder := firstPhase_leftHit_time_strict_succ w h hk
  have htn : t ≤ n := by dsimp [t, n, τ]; omega
  have hlevel : L w t = k + 1 := by
    by_cases hq0 : k + 1 = 0
    · dsimp [t]
      rw [hq0, boundaryHitTime_zero]
      simp [L]
    · exact boundaryHitTime_left_spec w h (by omega)
  have hmin : ∀ j, t ≤ j → j ≤ n → L w t ≤ L w j := by
    intro j hjt hjn
    have hjτ : j < τ := by dsimp [n, τ] at hjn; omega
    have hrecord := firstPhase_boundaryHitTime_left_record w h hk j hjτ
    omega
  have hwestReach := firstPhase_activeWest_reachable w t n htn hmin
  have hsource : boundaryVertex w h (k + 1) =
      (kmswStage w t).west (act w t) := by
    by_cases hq0 : k + 1 = 0
    · dsimp [t]
      rw [hq0, boundaryVertex_zero, boundaryHitTime_zero]
      simp [act, kmswStage, kmswInit]
    · exact (boundaryHit_activeInitial_stable_of_ne_zero w h (by omega)
        (Nat.le_refl t)).symm
  have hleft : Reachable (⟨boundaryVertex w h (k + 1)⟩ : PresentVertex w)
      ⟨(kmswStage w n).east (act w n)⟩ := by
    have hwest : Reachable (⟨boundaryVertex w h (k + 1)⟩ : PresentVertex w)
        ⟨(kmswStage w n).west (act w n)⟩ := by
      rw [hsource]
      exact hwestReach
    exact firstPhase_activeEast_reachable_from w n hwest
  have hcode := firstPhase_leftHit_previous_code w h hk
  have hsucc : n + 1 = τ := by dsimp [n, τ]; omega
  have hEast : (kmswStage w τ).east (act w τ) =
      (kmswStage w n).east (act w n) := by
    rw [← hsucc]
    exact firstPhase_left_activeEast_succ w n hcode
  have hxk : boundaryVertex w h k =
      (kmswStage w τ).west (act w τ) :=
    (boundaryHit_activeInitial_stable_of_ne_zero w h (by omega)
      (Nat.le_refl τ)).symm
  have hright : Reachable (⟨boundaryVertex w h k⟩ : PresentVertex w)
      ⟨(kmswStage w n).east (act w n)⟩ := by
    rw [hxk, ← hEast]
    exact firstPhase_activeEast_reachable_from w τ (Reachable.refl _)
  constructor
  · simpa [n, τ] using hright
  · simpa [n, τ] using hleft

/-- Almost surely, every walk-level time strictly before the first left exit
has an active initial vertex reachable from the root -/
theorem iidCodes_ae_firstPhase_walkNL_reachable :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ h : HasFlowLineHits (fun i => ω (i + 1)),
        ∀ n, n < walkNL (fun i => ω (i + 1)) h 0 →
          Reachable (⟨0⟩ : PresentVertex (fun i => ω (i + 1)))
            ⟨(kmswStage (fun i => ω (i + 1)) n).west
              (act (fun i => ω (i + 1)) n)⟩ := by
  filter_upwards [ae_hasFlowLineHits] with ω hω
  exact ⟨hω, fun n hn => firstPhase_walkNL_reachable _ hω n hn⟩

/-- Almost surely, each consecutive pair of negative-index lower-boundary
vertices has the common descendant constructed at the preceding active edge -/
theorem iidCodes_ae_firstPhase_leftBoundary_commonDescendant :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        ∀ k : ℤ, k ≤ -1 →
          Reachable (⟨boundaryVertex (fun i => ω (i + 1)) h k⟩ :
              PresentVertex (fun i => ω (i + 1)))
            ⟨(kmswStage (fun i => ω (i + 1))
                (boundaryHitTime (fun i => ω (i + 1)) h k - 1)).east
              (act (fun i => ω (i + 1))
                (boundaryHitTime (fun i => ω (i + 1)) h k - 1))⟩ ∧
          Reachable (⟨boundaryVertex (fun i => ω (i + 1)) h (k + 1)⟩ :
              PresentVertex (fun i => ω (i + 1)))
            ⟨(kmswStage (fun i => ω (i + 1))
                (boundaryHitTime (fun i => ω (i + 1)) h k - 1)).east
              (act (fun i => ω (i + 1))
                (boundaryHitTime (fun i => ω (i + 1)) h k - 1))⟩ := by
  filter_upwards [iidCodes_ae_boundaryHitWitnesses] with ω hω
  exact ⟨hω, fun k hk => firstPhase_leftBoundary_commonDescendant _ hω hk⟩

end DirectedDistances.KMSW
