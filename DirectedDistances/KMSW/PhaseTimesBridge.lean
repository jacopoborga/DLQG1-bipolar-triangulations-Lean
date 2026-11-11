/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.QuadrantSplit
public import DirectedDistances.KMSW.FlowLineTimes

/-! # Bridge between code splitting and flow-line times

This file records the deterministic index relation between the quadrant
splitter and the walk-level flow-line times.  Source references: -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk

private theorem codeWalk_succ_add_bridge (w : ℕ → Fin 3) (n : ℕ) :
    codeWalk w (n + 1) = codeWalk w n + lazyTwoDimensionalStep (w (n + 1)) := by
  have h := codeWalk_succ_sub w n
  calc
    codeWalk w (n + 1) =
        (codeWalk w (n + 1) - codeWalk w n) + codeWalk w n := by abel
    _ = lazyTwoDimensionalStep (w (n + 1)) + codeWalk w n := by rw [h]
    _ = codeWalk w n + lazyTwoDimensionalStep (w (n + 1)) := by abel

/-- The two phase walks sum to the original walk after the same number of
codes have been read (`lem-quadrant-walk`, -/
theorem quadrantSplitState_walk_sum (ω : ℕ → Fin 3) (n : ℕ) :
    codeWalk ω n = (quadrantSplitState ω n).rWalk +
      (quadrantSplitState ω n).lWalk := by
  induction n with
  | zero => simp [quadrantSplitState, quadrantSplitStart, codeWalk_zero]
  | succ n ih =>
      rw [quadrantSplitState, codeWalk_succ_add_bridge, ih]
      cases h : (quadrantSplitState ω n).phase <;>
        simp [quadrantSplitAdvance, h] <;> abel

/-- The code read by the splitter at state time `n` is the `n`th code of
the zero-based walk stream used by `FlowLineTimes`. -/
theorem quadrantSplit_nextCode_eq_walkCode (ω : ℕ → Fin 3) (n : ℕ) :
    ω (n + 1) = (fun i => ω (i + 1)) n := rfl

/-- At an `r` state, the next extracted `r` code is the walk code at index
`n` (the source increment at time `n + 1`). -/
theorem phaseSplit_rCode_at_walk_step (ω : ℕ → Fin 3) (n : ℕ)
    (hphase : (quadrantSplitState ω n).phase = .r) :
    (phaseSplit ω).1 ((quadrantSplitState ω n).rCount + 1) =
      (fun i => ω (i + 1)) n := by
  simpa using phaseSplit_rCode_at_step ω n hphase

/-- At an `l` state, the next extracted `l` code is the walk code at index
`n` (the source increment at time `n + 1`). -/
theorem phaseSplit_lCode_at_walk_step (ω : ℕ → Fin 3) (n : ℕ)
    (hphase : (quadrantSplitState ω n).phase = .l) :
    (phaseSplit ω).2 ((quadrantSplitState ω n).lCount + 1) =
      (fun i => ω (i + 1)) n := by
  simpa using phaseSplit_lCode_at_step ω n hphase

private theorem lazyStep_fst_lower_bridge (c : Fin 3) :
    -1 ≤ (lazyTwoDimensionalStep c).1 := by
  fin_cases c <;> simp [lazyTwoDimensionalStep]

private theorem lazyStep_snd_lower_bridge (c : Fin 3) :
    -1 ≤ (lazyTwoDimensionalStep c).2 := by
  fin_cases c <;> simp [lazyTwoDimensionalStep]

private theorem flowL_before_firstHit (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (t n : ℕ) (htn : t ≤ n)
    (hn : n < firstFlowLHit w h t) : L w t ≤ L w n := by
  classical
  change (∀ n, ∃ m, n + 1 ≤ m ∧ L w m = L w n - 1) ∧ _ at h
  have hmin : ∀ j, t + 1 ≤ j → j < firstFlowLHit w h t →
      L w j ≠ L w t - 1 := by
    intro j hj hjhit heq
    change j < Nat.find (h.1 t) at hjhit
    have hfind := Nat.find_min (h.1 t) hjhit
    exact hfind ⟨hj, heq⟩
  have hbefore : ∀ j, t ≤ j → j < firstFlowLHit w h t → L w t ≤ L w j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
        intro _
        exact le_rfl
    | succ j hj ih =>
        intro hjhit
        have hs : L w (j + 1) = L w j +
            (lazyTwoDimensionalStep (w j)).1 := Finset.sum_range_succ _ _
        have hstep : L w j - 1 ≤ L w (j + 1) := by
          rw [hs]
          have hlow := lazyStep_fst_lower_bridge (w j)
          omega
        have hprev := ih (by omega)
        by_contra hlt
        have hneq := hmin (j + 1) (by omega) hjhit
        omega
  exact hbefore n htn hn

private theorem flowR_before_firstHit (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (t n : ℕ) (htn : t ≤ n)
    (hn : n < firstFlowRHit w h t) : R w t ≤ R w n := by
  classical
  change (∀ n, ∃ m, n + 1 ≤ m ∧ L w m = L w n - 1) ∧
    (∀ n, ∃ m, n + 1 ≤ m ∧ R w m = R w n - 1) at h
  have hmin : ∀ j, t + 1 ≤ j → j < firstFlowRHit w h t →
      R w j ≠ R w t - 1 := by
    intro j hj hjhit heq
    change j < Nat.find (h.2 t) at hjhit
    have hfind := Nat.find_min (h.2 t) hjhit
    exact hfind ⟨hj, heq⟩
  have hbefore : ∀ j, t ≤ j → j < firstFlowRHit w h t → R w t ≤ R w j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
        intro _
        exact le_rfl
    | succ j hj ih =>
        intro hjhit
        have hstep : R w j - 1 ≤ R w (j + 1) := by
          have hs : R w (j + 1) = R w j + (lazyTwoDimensionalStep (w j)).2 :=
            Finset.sum_range_succ _ _
          rw [hs]
          have hlow := lazyStep_snd_lower_bridge (w j)
          omega
        have hprev := ih (by omega)
        by_contra hlt
        have hneq := hmin (j + 1) (by omega) hjhit
        omega
  exact hbefore n htn hn

private theorem shifted_L_codeWalk (ω : ℕ → Fin 3) (n : ℕ) :
    L (fun i => ω (i + 1)) n = (codeWalk ω n).1 := by
  simp only [L, codeWalk, Prod.fst_sum]

private theorem shifted_R_codeWalk (ω : ℕ → Fin 3) (n : ℕ) :
    R (fun i => ω (i + 1)) n = (codeWalk ω n).2 := by
  simp only [R, codeWalk, Prod.snd_sum]

private theorem quadrantSplit_R_hit_block (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (t : ℕ)
    (hphase : (quadrantSplitState ω t).phase = .r)
    (hrmin : (quadrantSplitState ω t).rLMin =
      (quadrantSplitState ω t).rWalk.1) :
    ∀ d, d ≤ firstFlowLHit (fun i => ω (i + 1)) h t - t →
      ((quadrantSplitState ω (t + d)).phase =
          if d = firstFlowLHit (fun i => ω (i + 1)) h t - t then .l else .r) ∧
      (quadrantSplitState ω (t + d)).lWalk = (quadrantSplitState ω t).lWalk ∧
      (if d = firstFlowLHit (fun i => ω (i + 1)) h t - t then
        (quadrantSplitState ω (t + d)).rLMin =
          (quadrantSplitState ω (t + d)).rWalk.1
       else (quadrantSplitState ω (t + d)).rLMin =
          (quadrantSplitState ω t).rLMin) ∧
      (quadrantSplitState ω (t + d)).lRMin = (quadrantSplitState ω t).lRMin ∧
      (quadrantSplitState ω (t + d)).rCount =
        (quadrantSplitState ω t).rCount + d := by
  intro d
  induction d with
  | zero =>
      intro hd
      have hpos := firstFlowLHit_spec (fun i => ω (i + 1)) h t
      have hlenpos : 0 ≠ firstFlowLHit (fun i => ω (i + 1)) h t - t := by
        omega
      constructor
      · simpa [hlenpos] using hphase
      constructor
      · rfl
      constructor
      · simpa [hlenpos] using hrmin
      constructor
      · rfl
      · simp
  | succ d ih =>
      intro hd
      have hlen : t < firstFlowLHit (fun i => ω (i + 1)) h t := by
        have := firstFlowLHit_spec (fun i => ω (i + 1)) h t
        omega
      have hdprev : d ≤ firstFlowLHit (fun i => ω (i + 1)) h t - t := by omega
      obtain ⟨hphaseD, hlwalkD, hrminD, hlminD, hcountD⟩ := ih hdprev
      have hdlt : d < firstFlowLHit (fun i => ω (i + 1)) h t - t := by omega
      have htime : t + d < firstFlowLHit (fun i => ω (i + 1)) h t := by omega
      have htimeSucc : t + d + 1 ≤ firstFlowLHit (fun i => ω (i + 1)) h t := by omega
      let s := quadrantSplitState ω (t + d)
      have hneqD : d ≠ firstFlowLHit (fun i => ω (i + 1)) h t - t := by omega
      have hsphase : s.phase = .r := by
        simpa [s, hneqD] using hphaseD
      have hsmin : s.rLMin = (quadrantSplitState ω t).rLMin := by
        simpa [s, hneqD] using hrminD
      have hslwalk : s.lWalk = (quadrantSplitState ω t).lWalk := by
        simpa [s] using hlwalkD
      have hslmin : s.lRMin = (quadrantSplitState ω t).lRMin := by
        simpa [s] using hlminD
      have hscount : s.rCount = (quadrantSplitState ω t).rCount + d := by
        simpa [s] using hcountD
      have hnext : quadrantSplitState ω (t + d + 1) =
          quadrantSplitAdvance s (ω (t + d + 1)) := by
        simp [quadrantSplitState, s, Nat.add_assoc]
      have hcoordNext : L (fun i => ω (i + 1)) (t + d + 1) =
          (quadrantSplitState ω (t + d + 1)).rWalk.1 + s.lWalk.1 := by
        rw [shifted_L_codeWalk, quadrantSplitState_walk_sum]
        rw [hnext]
        simp [quadrantSplitAdvance, hsphase, Prod.fst_add, hslwalk]
      have hcoordStart : L (fun i => ω (i + 1)) t =
          (quadrantSplitState ω t).rWalk.1 + (quadrantSplitState ω t).lWalk.1 := by
        rw [shifted_L_codeWalk, quadrantSplitState_walk_sum]
        rfl
      have hhit_iff :
          (quadrantSplitState ω (t + d + 1)).rWalk.1 < s.rLMin ↔
            L (fun i => ω (i + 1)) (t + d + 1) <
              L (fun i => ω (i + 1)) t := by
        rw [hcoordNext, hsmin, hrmin, hcoordStart, ← hslwalk]
        omega
      have hhit : (quadrantSplitState ω (t + d + 1)).rWalk.1 < s.rLMin ↔
          d + 1 = firstFlowLHit (fun i => ω (i + 1)) h t - t := by
        by_cases heq : d + 1 = firstFlowLHit (fun i => ω (i + 1)) h t - t
        · have hval := (firstFlowLHit_spec (fun i => ω (i + 1)) h t).2
          have htimeEq : t + d + 1 = firstFlowLHit (fun i => ω (i + 1)) h t := by
            omega
          have hcoord : L (fun i => ω (i + 1)) (t + d + 1) =
              L (fun i => ω (i + 1)) t - 1 := by
            simpa [htimeEq] using hval
          rw [hhit_iff, hcoord]
          omega
        · have hbefore := flowL_before_firstHit (fun i => ω (i + 1)) h t
            (t + d + 1) (by omega) (by omega)
          rw [hhit_iff]
          constructor
          · intro _
            omega
          · intro _
            omega
      have hnextR : (quadrantSplitState ω (t + d + 1)).rWalk.1 =
          s.rWalk.1 + (lazyTwoDimensionalStep (ω (t + d + 1))).1 := by
        rw [hnext]
        simp [quadrantSplitAdvance, hsphase]
      have hhitStep : s.rWalk.1 +
          (lazyTwoDimensionalStep (ω (t + d + 1))).1 < s.rLMin ↔
            d + 1 = firstFlowLHit (fun i => ω (i + 1)) h t - t := by
        rw [← hnextR]
        exact hhit
      have hphaseNext : (quadrantSplitState ω (t + d + 1)).phase =
          if d + 1 = firstFlowLHit (fun i => ω (i + 1)) h t - t then .l else .r := by
        rw [hnext]
        simp [quadrantSplitAdvance, hsphase, hhitStep]
      have hlwalkNext : (quadrantSplitState ω (t + d + 1)).lWalk =
          (quadrantSplitState ω t).lWalk := by
        rw [hnext]
        simp [quadrantSplitAdvance, hsphase, hslwalk]
      have hrminNext :
          (if d + 1 = firstFlowLHit (fun i => ω (i + 1)) h t - t then
            (quadrantSplitState ω (t + d + 1)).rLMin =
              (quadrantSplitState ω (t + d + 1)).rWalk.1
           else (quadrantSplitState ω (t + d + 1)).rLMin =
              (quadrantSplitState ω t).rLMin) := by
        have hminNext : (quadrantSplitState ω (t + d + 1)).rLMin =
            if d + 1 = firstFlowLHit (fun i => ω (i + 1)) h t - t then
              (quadrantSplitState ω (t + d + 1)).rWalk.1 else s.rLMin := by
          rw [hnext]
          simp [quadrantSplitAdvance, hsphase, hhitStep]
        rw [hminNext]
        by_cases heq : d + 1 = firstFlowLHit (fun i => ω (i + 1)) h t - t
        · simp [heq]
        · simp [heq, hsmin]
      have hlminNext : (quadrantSplitState ω (t + d + 1)).lRMin =
          (quadrantSplitState ω t).lRMin := by
        rw [hnext]
        simpa [quadrantSplitAdvance, hsphase] using hslmin
      have hcountNext : (quadrantSplitState ω (t + d + 1)).rCount =
          (quadrantSplitState ω t).rCount + (d + 1) := by
        rw [hnext]
        simp [quadrantSplitAdvance_rCount, hsphase, hscount]
        omega
      exact ⟨hphaseNext, hlwalkNext, hrminNext, hlminNext, hcountNext⟩

private theorem quadrantSplit_L_hit_block (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (t : ℕ)
    (hphase : (quadrantSplitState ω t).phase = .l)
    (hlmin : (quadrantSplitState ω t).lRMin =
      (quadrantSplitState ω t).lWalk.2) :
    ∀ d, d ≤ firstFlowRHit (fun i => ω (i + 1)) h t - t →
      ((quadrantSplitState ω (t + d)).phase =
          if d = firstFlowRHit (fun i => ω (i + 1)) h t - t then .r else .l) ∧
      (quadrantSplitState ω (t + d)).rWalk = (quadrantSplitState ω t).rWalk ∧
      (if d = firstFlowRHit (fun i => ω (i + 1)) h t - t then
        (quadrantSplitState ω (t + d)).lRMin =
          (quadrantSplitState ω (t + d)).lWalk.2
       else (quadrantSplitState ω (t + d)).lRMin =
          (quadrantSplitState ω t).lRMin) ∧
      (quadrantSplitState ω (t + d)).rLMin = (quadrantSplitState ω t).rLMin ∧
      (quadrantSplitState ω (t + d)).rCount = (quadrantSplitState ω t).rCount := by
  intro d
  induction d with
  | zero =>
      intro hd
      have hpos := firstFlowRHit_spec (fun i => ω (i + 1)) h t
      have hlenpos : 0 ≠ firstFlowRHit (fun i => ω (i + 1)) h t - t := by omega
      constructor
      · simpa [hlenpos] using hphase
      constructor
      · rfl
      constructor
      · simpa [hlenpos] using hlmin
      constructor
      · rfl
      · rfl
  | succ d ih =>
      intro hd
      have hlen : t < firstFlowRHit (fun i => ω (i + 1)) h t := by
        have := firstFlowRHit_spec (fun i => ω (i + 1)) h t
        omega
      have hdprev : d ≤ firstFlowRHit (fun i => ω (i + 1)) h t - t := by omega
      obtain ⟨hphaseD, hrwalkD, hlminD, hrminD, hcountD⟩ := ih hdprev
      have hdlt : d < firstFlowRHit (fun i => ω (i + 1)) h t - t := by omega
      let s := quadrantSplitState ω (t + d)
      have hneqD : d ≠ firstFlowRHit (fun i => ω (i + 1)) h t - t := by omega
      have hsphase : s.phase = .l := by
        simpa [s, hneqD] using hphaseD
      have hsmin : s.lRMin = (quadrantSplitState ω t).lRMin := by
        simpa [s, hneqD] using hlminD
      have hsrwalk : s.rWalk = (quadrantSplitState ω t).rWalk := by
        simpa [s] using hrwalkD
      have hsrmin : s.rLMin = (quadrantSplitState ω t).rLMin := by
        simpa [s] using hrminD
      have hscount : s.rCount = (quadrantSplitState ω t).rCount := by
        simpa [s] using hcountD
      have hnext : quadrantSplitState ω (t + d + 1) =
          quadrantSplitAdvance s (ω (t + d + 1)) := by
        simp [quadrantSplitState, s, Nat.add_assoc]
      have hcoordNext : R (fun i => ω (i + 1)) (t + d + 1) =
          (quadrantSplitState ω (t + d + 1)).rWalk.2 +
            (quadrantSplitState ω (t + d + 1)).lWalk.2 := by
        rw [shifted_R_codeWalk, quadrantSplitState_walk_sum]
        rfl
      have hcoordStart : R (fun i => ω (i + 1)) t =
          (quadrantSplitState ω t).rWalk.2 + (quadrantSplitState ω t).lWalk.2 := by
        rw [shifted_R_codeWalk, quadrantSplitState_walk_sum]
        rfl
      have hnextRWalk : (quadrantSplitState ω (t + d + 1)).rWalk = s.rWalk := by
        rw [hnext]
        simp [quadrantSplitAdvance, hsphase]
      have hhit_iff :
          (quadrantSplitState ω (t + d + 1)).lWalk.2 < s.lRMin ↔
            R (fun i => ω (i + 1)) (t + d + 1) <
              R (fun i => ω (i + 1)) t := by
        rw [hcoordNext, hsmin, hlmin, hcoordStart, hnextRWalk, hsrwalk]
        omega
      have hhit : (quadrantSplitState ω (t + d + 1)).lWalk.2 < s.lRMin ↔
          d + 1 = firstFlowRHit (fun i => ω (i + 1)) h t - t := by
        by_cases heq : d + 1 = firstFlowRHit (fun i => ω (i + 1)) h t - t
        · have hval := (firstFlowRHit_spec (fun i => ω (i + 1)) h t).2
          have htimeEq : t + d + 1 = firstFlowRHit (fun i => ω (i + 1)) h t := by
            omega
          have hcoord : R (fun i => ω (i + 1)) (t + d + 1) =
              R (fun i => ω (i + 1)) t - 1 := by
            simpa [htimeEq] using hval
          rw [hhit_iff, hcoord]
          omega
        · have hbefore := flowR_before_firstHit (fun i => ω (i + 1)) h t
            (t + d + 1) (by omega) (by omega)
          rw [hhit_iff]
          constructor
          · intro _
            omega
          · intro _
            omega
      have hnextL : (quadrantSplitState ω (t + d + 1)).lWalk.2 =
          s.lWalk.2 + (lazyTwoDimensionalStep (ω (t + d + 1))).2 := by
        rw [hnext]
        simp [quadrantSplitAdvance, hsphase]
      have hhitStep : s.lWalk.2 +
          (lazyTwoDimensionalStep (ω (t + d + 1))).2 < s.lRMin ↔
            d + 1 = firstFlowRHit (fun i => ω (i + 1)) h t - t := by
        rw [← hnextL]
        exact hhit
      have hphaseNext : (quadrantSplitState ω (t + d + 1)).phase =
          if d + 1 = firstFlowRHit (fun i => ω (i + 1)) h t - t then .r else .l := by
        rw [hnext]
        simp [quadrantSplitAdvance, hsphase, hhitStep]
      have hrwalkNext : (quadrantSplitState ω (t + d + 1)).rWalk =
          (quadrantSplitState ω t).rWalk := by
        rw [hnext]
        simp [quadrantSplitAdvance, hsphase, hsrwalk]
      have hrminNext :
          (if d + 1 = firstFlowRHit (fun i => ω (i + 1)) h t - t then
            (quadrantSplitState ω (t + d + 1)).lRMin =
              (quadrantSplitState ω (t + d + 1)).lWalk.2
           else (quadrantSplitState ω (t + d + 1)).lRMin =
              (quadrantSplitState ω t).lRMin) := by
        have hminNext : (quadrantSplitState ω (t + d + 1)).lRMin =
            if d + 1 = firstFlowRHit (fun i => ω (i + 1)) h t - t then
              (quadrantSplitState ω (t + d + 1)).lWalk.2 else s.lRMin := by
          rw [hnext]
          simp [quadrantSplitAdvance, hsphase, hhitStep]
        rw [hminNext]
        by_cases heq : d + 1 = firstFlowRHit (fun i => ω (i + 1)) h t - t
        · simp [heq]
        · simp [heq, hsmin]
      have hrminOtherNext : (quadrantSplitState ω (t + d + 1)).rLMin =
          (quadrantSplitState ω t).rLMin := by
        rw [hnext]
        simpa [quadrantSplitAdvance, hsphase] using hsrmin
      have hcountNext : (quadrantSplitState ω (t + d + 1)).rCount =
          (quadrantSplitState ω t).rCount := by
        rw [hnext]
        simp [quadrantSplitAdvance_rCount, hsphase, hscount]
      exact ⟨hphaseNext, hrwalkNext, hrminNext, hrminOtherNext, hcountNext⟩

private theorem walkNL_eq_firstFlowL (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    walkNL w h k = firstFlowLHit w h (walkNR w h k) := by
  cases k <;> rfl

private theorem walkNR_succ_eq_firstFlowR (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    walkNR w h (k + 1) = firstFlowRHit w h (walkNL w h k) := rfl

/-- At each entrance time the splitter is in its `r` phase, with both
running minima equal to the corresponding current phase walk coordinates. -/
theorem quadrantSplitState_at_walkNR (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k : ℕ) :
    (quadrantSplitState ω (walkNR (fun i => ω (i + 1)) h k)).phase = .r ∧
    (quadrantSplitState ω (walkNR (fun i => ω (i + 1)) h k)).rLMin =
      (quadrantSplitState ω (walkNR (fun i => ω (i + 1)) h k)).rWalk.1 ∧
    (quadrantSplitState ω (walkNR (fun i => ω (i + 1)) h k)).lRMin =
      (quadrantSplitState ω (walkNR (fun i => ω (i + 1)) h k)).lWalk.2 := by
  induction k with
  | zero =>
      simp [walkNR, flowLineTimes, quadrantSplitState, quadrantSplitStart]
  | succ k ih =>
      let w := fun i => ω (i + 1)
      let tR := walkNR w h k
      let tL := walkNL w h k
      have hRblock := quadrantSplit_R_hit_block ω h tR ih.1 ih.2.1
      have hLtime : tL = firstFlowLHit (fun i => ω (i + 1)) h tR := by
        dsimp [tL, tR, w]
        exact walkNL_eq_firstFlowL (fun i => ω (i + 1)) h k
      let dR := firstFlowLHit (fun i => ω (i + 1)) h tR - tR
      have hAtL := hRblock dR (by omega)
      have hIndexL : tR + dR = tL := by
        calc
          tR + dR = firstFlowLHit (fun i => ω (i + 1)) h tR := by
            dsimp [dR]
            have hspec := firstFlowLHit_spec (fun i => ω (i + 1)) h tR
            omega
          _ = tL := hLtime.symm
      have hLphase : (quadrantSplitState ω tL).phase = .l := by
        have := hAtL.1
        rw [hIndexL] at this
        simpa [dR] using this
      have hLrmin : (quadrantSplitState ω tL).rLMin =
          (quadrantSplitState ω tL).rWalk.1 := by
        have := hAtL.2.2.1
        rw [hIndexL] at this
        simpa [dR] using this
      have hLlmin : (quadrantSplitState ω tL).lRMin =
          (quadrantSplitState ω tL).lWalk.2 := by
        calc
          (quadrantSplitState ω tL).lRMin = (quadrantSplitState ω tR).lRMin := by
            have := hAtL.2.2.2.1
            rw [hIndexL] at this
            simpa [dR] using this
          _ = (quadrantSplitState ω tR).lWalk.2 := ih.2.2
          _ = (quadrantSplitState ω tL).lWalk.2 := by
            have hwalk := congrArg Prod.snd hAtL.2.1
            rw [hIndexL] at hwalk
            exact hwalk.symm
      have hLblock := quadrantSplit_L_hit_block ω h tL hLphase hLlmin
      have hRtime : walkNR (fun i => ω (i + 1)) h (k + 1) =
          firstFlowRHit (fun i => ω (i + 1)) h tL := by
        dsimp [tL]
        exact walkNR_succ_eq_firstFlowR (fun i => ω (i + 1)) h k
      let dL := firstFlowRHit (fun i => ω (i + 1)) h tL - tL
      have hAtR := hLblock dL (by omega)
      have hIndexR : tL + dL = walkNR w h (k + 1) := by
        calc
          tL + dL = firstFlowRHit (fun i => ω (i + 1)) h tL := by
            dsimp [dL]
            have hspec := firstFlowRHit_spec (fun i => ω (i + 1)) h tL
            omega
          _ = walkNR w h (k + 1) := by simpa [w] using hRtime.symm
      have hRphase : (quadrantSplitState ω (walkNR w h (k + 1))).phase = .r := by
        have := hAtR.1
        rw [hIndexR] at this
        simpa [dL] using this
      have hRrmin : (quadrantSplitState ω (walkNR w h (k + 1))).rLMin =
          (quadrantSplitState ω (walkNR w h (k + 1))).rWalk.1 := by
        calc
          (quadrantSplitState ω (walkNR w h (k + 1))).rLMin =
              (quadrantSplitState ω tL).rLMin := by
            have := hAtR.2.2.2.1
            rw [hIndexR] at this
            simpa [dL] using this
          _ = (quadrantSplitState ω tL).rWalk.1 := hLrmin
          _ = (quadrantSplitState ω (walkNR w h (k + 1))).rWalk.1 := by
            have hrwalk := congrArg Prod.fst hAtR.2.1
            rw [hIndexR] at hrwalk
            exact hrwalk.symm
      have hRlmin : (quadrantSplitState ω (walkNR w h (k + 1))).lRMin =
          (quadrantSplitState ω (walkNR w h (k + 1))).lWalk.2 := by
        have := hAtR.2.2.1
        rw [hIndexR] at this
        simpa [dL] using this
      exact ⟨hRphase, hRrmin, hRlmin⟩

/-- At each exit time the splitter has just switched from `r` to `l`. -/
theorem quadrantSplitState_at_walkNL (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k : ℕ) :
    (quadrantSplitState ω (walkNL (fun i => ω (i + 1)) h k)).phase = .l ∧
    (quadrantSplitState ω (walkNL (fun i => ω (i + 1)) h k)).rLMin =
      (quadrantSplitState ω (walkNL (fun i => ω (i + 1)) h k)).rWalk.1 ∧
    (quadrantSplitState ω (walkNL (fun i => ω (i + 1)) h k)).lRMin =
      (quadrantSplitState ω (walkNL (fun i => ω (i + 1)) h k)).lWalk.2 := by
  let w := fun i => ω (i + 1)
  let t := walkNR w h k
  have hstart := quadrantSplitState_at_walkNR ω h k
  have hblock := quadrantSplit_R_hit_block ω h t hstart.1 hstart.2.1
  have htime : walkNL w h k = firstFlowLHit (fun i => ω (i + 1)) h t := by
    dsimp [t, w]
    exact walkNL_eq_firstFlowL (fun i => ω (i + 1)) h k
  let d := firstFlowLHit (fun i => ω (i + 1)) h t - t
  have hd := hblock d (by omega)
  have hindex : t + d = walkNL w h k := by
    calc
      t + d = firstFlowLHit (fun i => ω (i + 1)) h t := by
        dsimp [d]
        have hspec := firstFlowLHit_spec (fun i => ω (i + 1)) h t
        omega
      _ = walkNL w h k := htime.symm
  have hphase : (quadrantSplitState ω (walkNL w h k)).phase = .l := by
    have hp := hd.1
    rw [hindex] at hp
    simpa [d] using hp
  have hrmin : (quadrantSplitState ω (walkNL w h k)).rLMin =
      (quadrantSplitState ω (walkNL w h k)).rWalk.1 := by
    have hm := hd.2.2.1
    rw [hindex] at hm
    simpa [d] using hm
  have hlmin : (quadrantSplitState ω (walkNL w h k)).lRMin =
      (quadrantSplitState ω (walkNL w h k)).lWalk.2 := by
    calc
      (quadrantSplitState ω (walkNL w h k)).lRMin =
          (quadrantSplitState ω t).lRMin := by
        have hm := hd.2.2.2.1
        rw [hindex] at hm
        simpa [d] using hm
      _ = (quadrantSplitState ω t).lWalk.2 := hstart.2.2
      _ = (quadrantSplitState ω (walkNL w h k)).lWalk.2 := by
        have hw := congrArg Prod.snd hd.2.1
        rw [hindex] at hw
        exact hw.symm
  exact ⟨hphase, hrmin, hlmin⟩

private theorem walkNR_ge_index (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ k, k ≤ walkNR w h k := by
  intro k
  induction k with
  | zero => simp [walkNR_zero]
  | succ k ih =>
      have hL := walkNL_spec w h k
      have hR := walkNR_succ_spec w h k
      omega

private theorem walkNR_interval_cover (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (n : ℕ) :
    ∃ k, walkNR w h k ≤ n ∧ n < walkNR w h (k + 1) := by
  classical
  let p : ℕ → Prop := fun k => n < walkNR w h k
  have hex : ∃ k, p k := by
    refine ⟨n + 1, ?_⟩
    have hb := walkNR_ge_index w h (n + 1)
    dsimp [p] at *
    omega
  let j := Nat.find hex
  have hj : p j := Nat.find_spec hex
  have hjpos : 0 < j := by
    by_contra hzero
    have hz : j = 0 := by omega
    have hj0 : n < walkNR w h 0 := by simpa [p, hz] using hj
    have : n < 0 := by simpa [walkNR_zero] using hj0
    omega
  let k := j - 1
  have hkj : k + 1 = j := by dsimp [k]; omega
  have hnot : ¬ p k := Nat.find_min hex (by dsimp [k, j]; omega)
  refine ⟨k, ?_, ?_⟩
  · dsimp [p] at hnot
    omega
  · rw [hkj]
    exact hj

private theorem quadrantSplit_phase_r_on_interval (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k n : ℕ)
    (hn0 : walkNR (fun i => ω (i + 1)) h k ≤ n)
    (hn1 : n < walkNL (fun i => ω (i + 1)) h k) :
    (quadrantSplitState ω n).phase = .r := by
  let w := fun i => ω (i + 1)
  let t := walkNR w h k
  let d := n - t
  have hn0' : t ≤ n := by simpa [t, w] using hn0
  have hn1' : n < walkNL w h k := by simpa [w] using hn1
  have hstart := quadrantSplitState_at_walkNR ω h k
  have hblock := quadrantSplit_R_hit_block ω h t hstart.1 hstart.2.1
  have htime : walkNL w h k = firstFlowLHit (fun i => ω (i + 1)) h t := by
    dsimp [t, w]
    exact walkNL_eq_firstFlowL (fun i => ω (i + 1)) h k
  have hidx : t + d = n := by dsimp [d]; omega
  have hlen : d < firstFlowLHit (fun i => ω (i + 1)) h t - t := by
    rw [← htime]
    dsimp [d]
    omega
  have hp := (hblock d (by omega)).1
  rw [hidx] at hp
  have hneq : d ≠ firstFlowLHit (fun i => ω (i + 1)) h t - t := by omega
  simpa [hneq] using hp

private theorem quadrantSplit_phase_l_on_interval (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k n : ℕ)
    (hn0 : walkNL (fun i => ω (i + 1)) h k ≤ n)
    (hn1 : n < walkNR (fun i => ω (i + 1)) h (k + 1)) :
    (quadrantSplitState ω n).phase = .l := by
  let w := fun i => ω (i + 1)
  let t := walkNL w h k
  let d := n - t
  have hn0' : t ≤ n := by simpa [t, w] using hn0
  have hn1' : n < walkNR w h (k + 1) := by simpa [w] using hn1
  have hstart := quadrantSplitState_at_walkNL ω h k
  have hblock := quadrantSplit_L_hit_block ω h t hstart.1 hstart.2.2
  have htime : walkNR w h (k + 1) = firstFlowRHit (fun i => ω (i + 1)) h t := by
    dsimp [t, w]
    exact walkNR_succ_eq_firstFlowR (fun i => ω (i + 1)) h k
  have hidx : t + d = n := by dsimp [d]; omega
  have hlen : d < firstFlowRHit (fun i => ω (i + 1)) h t - t := by
    rw [← htime]
    dsimp [d]
    omega
  have hp := (hblock d (by omega)).1
  rw [hidx] at hp
  have hneq : d ≠ firstFlowRHit (fun i => ω (i + 1)) h t - t := by omega
  simpa [hneq] using hp

/-- The splitter's `r` states occupy exactly the flow-line intervals
`[walkNR k, walkNL k)` (`lem-flow-line-times` and `eqn-quad-pre`, -/
theorem quadrantSplitState_rPhase_iff (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (n : ℕ) :
    (quadrantSplitState ω n).phase = .r ↔
      ∃ k, walkNR (fun i => ω (i + 1)) h k ≤ n ∧
        n < walkNL (fun i => ω (i + 1)) h k := by
  constructor
  · intro hphase
    obtain ⟨k, hleft, hright⟩ :=
      walkNR_interval_cover (fun i => ω (i + 1)) h n
    by_cases hmid : n < walkNL (fun i => ω (i + 1)) h k
    · exact ⟨k, hleft, hmid⟩
    · have hle : walkNL (fun i => ω (i + 1)) h k ≤ n := by omega
      have hphaseL := quadrantSplit_phase_l_on_interval ω h k n hle hright
      rw [hphaseL] at hphase
      cases hphase
  · rintro ⟨k, hleft, hright⟩
    exact quadrantSplit_phase_r_on_interval ω h k n hleft hright

/-- The splitter's `l` states occupy exactly the flow-line intervals
`[walkNL k, walkNR (k + 1))` (`lem-flow-line-times` and `eqn-quad-pre`, -/
theorem quadrantSplitState_lPhase_iff (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (n : ℕ) :
    (quadrantSplitState ω n).phase = .l ↔
      ∃ k, walkNL (fun i => ω (i + 1)) h k ≤ n ∧
        n < walkNR (fun i => ω (i + 1)) h (k + 1) := by
  constructor
  · intro hphase
    obtain ⟨k, hleft, hright⟩ :=
      walkNR_interval_cover (fun i => ω (i + 1)) h n
    by_cases hmid : n < walkNL (fun i => ω (i + 1)) h k
    · have hphaseR := quadrantSplit_phase_r_on_interval ω h k n hleft hmid
      rw [hphaseR] at hphase
      cases hphase
    · have hle : walkNL (fun i => ω (i + 1)) h k ≤ n := by omega
      exact ⟨k, hle, hright⟩
  · rintro ⟨k, hleft, hright⟩
    exact quadrantSplit_phase_l_on_interval ω h k n hleft hright

end DirectedDistances.KMSW
