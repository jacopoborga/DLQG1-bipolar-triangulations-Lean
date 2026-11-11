/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.PrimedQuadrantIntervals
public import DirectedDistances.KMSW.PhaseTimesBridge2
public import DirectedDistances.RandomWalk.QuadrantSplit
public import DirectedDistances.RandomWalk.QuadrantSplitIndependence







public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk

/-- The L-phase stream with its fixed dummy coordinate restored. -/
@[expose] def lExcursionDummyPrefix (x : ℕ → Fin 3) : ℕ → Fin 3
  | 0 => 0
  | n + 1 => x n

/-- Replace each strict new lower-record code of the second-coordinate walk
by the C13 initial code `1`, and prepend the first C13 code. The strict record
codes are the terminal L-phase exits; replacing them starts the next primed
block while omitting that exit. -/
@[expose] def lExcursionShift (x : ℕ → Fin 3) : ℕ → Fin 3
  | 0 => 1
  | n + 1 =>
      if (codeWalk (lExcursionDummyPrefix x) (n + 1)).2 <
          runningMin (fun k => (codeWalk (lExcursionDummyPrefix x) k).2) n
      then 1 else x n

@[simp] theorem lExcursionShift_zero (x : ℕ → Fin 3) :
    lExcursionShift x 0 = 1 := rfl

theorem lExcursionShift_succ (x : ℕ → Fin 3) (n : ℕ) :
    lExcursionShift x (n + 1) =
      if (codeWalk (lExcursionDummyPrefix x) (n + 1)).2 <
          runningMin (fun k => (codeWalk (lExcursionDummyPrefix x) k).2) n
      then 1 else x n := rfl

private theorem measurable_lExcursionDummyPrefix :
    Measurable lExcursionDummyPrefix := by
  apply measurable_pi_iff.mpr
  intro i
  cases i with
  | zero => exact measurable_const
  | succ n => exact measurable_pi_apply n

/-- Each output coordinate uses a finite input prefix, so the block recoding
is measurable. -/
theorem measurable_lExcursionShift : Measurable lExcursionShift := by
  apply measurable_pi_iff.mpr
  intro i
  cases i with
  | zero => exact measurable_const
  | succ n =>
      have hwalk : Measurable (fun x : ℕ → Fin 3 =>
          fun k => codeWalk (lExcursionDummyPrefix x) k) :=
        measurable_codeWalk.comp measurable_lExcursionDummyPrefix
      have hcoord (k : ℕ) : Measurable (fun x : ℕ → Fin 3 =>
          (codeWalk (lExcursionDummyPrefix x) k).2) :=
        ((measurable_pi_apply k).comp hwalk).snd
      have hmin : ∀ k, Measurable (fun x : ℕ → Fin 3 =>
          runningMin (fun j => (codeWalk (lExcursionDummyPrefix x) j).2) k) := by
        intro k
        induction k with
        | zero => exact hcoord 0
        | succ k ih =>
            change Measurable (fun x : ℕ → Fin 3 =>
              min (runningMin (fun j => (codeWalk (lExcursionDummyPrefix x) j).2) k)
                (codeWalk (lExcursionDummyPrefix x) (k + 1)).2)
            have hp : Measurable (fun x : ℕ → Fin 3 =>
                (runningMin (fun j => (codeWalk (lExcursionDummyPrefix x) j).2) k,
                  (codeWalk (lExcursionDummyPrefix x) (k + 1)).2)) :=
              ih.prodMk (hcoord (k + 1))
            have hm :=
              (measurable_of_countable (fun z : ℤ × ℤ => min z.1 z.2)).comp hp
            convert hm using 1
            · funext x
              rfl
      have hnew : MeasurableSet {x : ℕ → Fin 3 |
          (codeWalk (lExcursionDummyPrefix x) (n + 1)).2 <
            runningMin (fun k => (codeWalk (lExcursionDummyPrefix x) k).2) n} :=
        measurableSet_lt (hcoord (n + 1)) (hmin n)
      simpa [lExcursionShift] using
        (Measurable.ite hnew measurable_const (measurable_pi_apply n))

/-- The first corrected primed code agrees with the measurable recoding. -/
theorem primedCode_zero_eq_lExcursionShift (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) :
    primedCode ω h 0 = lExcursionShift (lCode ω) 0 := by
  rw [primedCode_zero, lExcursionShift_zero]

private theorem lExcursionDummyPrefix_lCode_eq_phaseSplit (ω : ℕ → Fin 3) :
    lExcursionDummyPrefix (lCode ω) = (phaseSplit ω).2 := by
  funext n
  cases n <;> simp [lExcursionDummyPrefix, lCode, phaseSplit]

private theorem codeWalk_succ_add_recode (x : ℕ → Fin 3) (n : ℕ) :
    codeWalk x (n + 1) = codeWalk x n + lazyTwoDimensionalStep (x (n + 1)) := by
  have h := codeWalk_succ_sub x n
  calc
    codeWalk x (n + 1) =
        (codeWalk x (n + 1) - codeWalk x n) + codeWalk x n := by abel
    _ = lazyTwoDimensionalStep (x (n + 1)) + codeWalk x n := by rw [h]
    _ = codeWalk x n + lazyTwoDimensionalStep (x (n + 1)) := by abel

private theorem quadrantSplit_lWalk_eq_lStream (ω : ℕ → Fin 3) (n : ℕ) :
    (quadrantSplitState ω n).lWalk =
      codeWalk (lExcursionDummyPrefix (lCode ω))
        (quadrantSplitState ω n).lCount := by
  have hs := quadrantInterleaveState_phaseSplit ω n
  have h := quadrantInterleaveState_lWalk (phaseSplit ω) n
  have hc := congrArg (fun s : QuadrantSplitState => s.lCount) hs.symm
  calc
    (quadrantSplitState ω n).lWalk =
        (quadrantInterleaveState (phaseSplit ω).1 (phaseSplit ω).2 n).lWalk :=
      congrArg (fun s : QuadrantSplitState => s.lWalk) hs.symm
    _ = codeWalk (phaseSplit ω).2
        (quadrantInterleaveState (phaseSplit ω).1 (phaseSplit ω).2 n).lCount := h
    _ = codeWalk (lExcursionDummyPrefix (lCode ω))
        (quadrantSplitState ω n).lCount := by
      rw [hc]
      rw [lExcursionDummyPrefix_lCode_eq_phaseSplit]

/-- The stored L-phase minimum is the running minimum of the second
coordinate of the L code stream (`lem-quadrant-walk`,
C13 measurable recoding, not an identification with the printed `S'_m`. -/
private theorem quadrantSplit_lRMin_eq_lStream_runningMin (ω : ℕ → Fin 3) :
    ∀ n, (quadrantSplitState ω n).lRMin =
      runningMin (fun j =>
        (codeWalk (lExcursionDummyPrefix (lCode ω)) j).2)
        (quadrantSplitState ω n).lCount := by
  intro n
  induction n with
  | zero =>
      change 0 = (codeWalk (lExcursionDummyPrefix (lCode ω)) 0).2
      rw [codeWalk_zero]
  | succ n ih =>
      let s := quadrantSplitState ω n
      by_cases hp : s.phase = .r
      · have hcount : (quadrantSplitState ω (n + 1)).lCount = s.lCount := by
          rw [quadrantSplitState, quadrantSplitAdvance_lCount]
          simp [s, hp]
        have hmin : (quadrantSplitState ω (n + 1)).lRMin = s.lRMin := by
          rw [quadrantSplitState]
          simp [s, quadrantSplitAdvance, hp]
        rw [hmin, ih, hcount]
      · have hpl : s.phase = .l := by
          cases h : s.phase with
          | r => exact False.elim (hp h)
          | l => rfl
        have hstate : quadrantSplitState ω (n + 1) =
            quadrantSplitAdvance s (ω (n + 1)) := by
          simp [s, quadrantSplitState]
        have hcount : (quadrantSplitState ω (n + 1)).lCount = s.lCount + 1 := by
          rw [hstate, quadrantSplitAdvance_lCount]
          simp [hpl]
        have hcode : (lExcursionDummyPrefix (lCode ω)) (s.lCount + 1) = ω (n + 1) := by
          rw [lExcursionDummyPrefix_lCode_eq_phaseSplit]
          exact phaseSplit_lCode_at_step ω n hpl
        have hnext :
            (codeWalk (lExcursionDummyPrefix (lCode ω)) (s.lCount + 1)).2 =
              s.lWalk.2 + (lazyTwoDimensionalStep (ω (n + 1))).2 := by
          rw [codeWalk_succ_add_recode, quadrantSplit_lWalk_eq_lStream ω n, hcode]
          rfl
        have hupdate : (quadrantSplitState ω (n + 1)).lRMin =
            min s.lRMin
              (codeWalk (lExcursionDummyPrefix (lCode ω)) (s.lCount + 1)).2 := by
          rw [hstate]
          simp [quadrantSplitAdvance, hpl]
          rw [hnext]
          by_cases hh :
              s.lWalk.2 + (lazyTwoDimensionalStep (ω (n + 1))).2 < s.lRMin
          · have hle : s.lWalk.2 + (lazyTwoDimensionalStep (ω (n + 1))).2 ≤ s.lRMin := hh.le
            simp [hh, min_eq_right hle]
          · have hle : s.lRMin ≤
                s.lWalk.2 + (lazyTwoDimensionalStep (ω (n + 1))).2 := by omega
            simp [hh, min_eq_left hle]
        rw [hupdate, ih, hcount]
        rfl

private theorem lCount_constant_on_R_interval (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k d : ℕ)
    (hd : walkNR (fun i => ω (i + 1)) h k + d ≤
      walkNL (fun i => ω (i + 1)) h k) :
    (quadrantSplitState ω (walkNR (fun i => ω (i + 1)) h k + d)).lCount =
      (quadrantSplitState ω (walkNR (fun i => ω (i + 1)) h k)).lCount := by
  induction d with
  | zero => rfl
  | succ d ih =>
      have hd' : walkNR (fun i => ω (i + 1)) h k + d ≤
          walkNL (fun i => ω (i + 1)) h k := by omega
      have hp : (quadrantSplitState ω
          (walkNR (fun i => ω (i + 1)) h k + d)).phase = .r := by
        apply (quadrantSplitState_rPhase_iff ω h _).2
        exact ⟨k, by omega, by omega⟩
      have hs : (quadrantSplitState ω
          (walkNR (fun i => ω (i + 1)) h k + d + 1)).lCount =
          (quadrantSplitState ω
            (walkNR (fun i => ω (i + 1)) h k + d)).lCount := by
        rw [quadrantSplitState, quadrantSplitAdvance_lCount]
        simp [hp]
      rw [show walkNR (fun i => ω (i + 1)) h k + (d + 1) =
        (walkNR (fun i => ω (i + 1)) h k + d) + 1 by omega]
      rw [hs, ih hd']

private theorem lCount_add_on_L_interval (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k d : ℕ)
    (hd : walkNL (fun i => ω (i + 1)) h k + d ≤
      walkNR (fun i => ω (i + 1)) h (k + 1)) :
    (quadrantSplitState ω (walkNL (fun i => ω (i + 1)) h k + d)).lCount =
      (quadrantSplitState ω (walkNL (fun i => ω (i + 1)) h k)).lCount + d := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hd' : walkNL (fun i => ω (i + 1)) h k + d ≤
          walkNR (fun i => ω (i + 1)) h (k + 1) := by omega
      have hp : (quadrantSplitState ω
          (walkNL (fun i => ω (i + 1)) h k + d)).phase = .l := by
        apply (quadrantSplitState_lPhase_iff ω h _).2
        exact ⟨k, by omega, by omega⟩
      have hs : (quadrantSplitState ω
          (walkNL (fun i => ω (i + 1)) h k + d + 1)).lCount =
          (quadrantSplitState ω
            (walkNL (fun i => ω (i + 1)) h k + d)).lCount + 1 := by
        rw [quadrantSplitState, quadrantSplitAdvance_lCount]
        simp [hp]
      rw [show walkNL (fun i => ω (i + 1)) h k + (d + 1) =
        (walkNL (fun i => ω (i + 1)) h k + d) + 1 by omega]
      rw [hs, ih hd']
      omega

/-- The cumulative interval width is the number of L codes consumed at the
corresponding L-phase entrance. -/
private theorem lCount_at_primedIntervalLeft (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k : ℕ) :
    (quadrantSplitState ω (primedIntervalLeft ω h k)).lCount =
      primedIntervalBase ω h k := by
  induction k with
  | zero =>
      have hzero : walkNR (fun i => ω (i + 1)) h 0 = 0 := walkNR_zero _ _
      have hconst := lCount_constant_on_R_interval ω h 0
        (walkNL (fun i => ω (i + 1)) h 0) (by rw [hzero]; omega)
      simpa [primedIntervalLeft, primedIntervalBase, hzero,
        quadrantSplitState, quadrantSplitStart] using hconst
  | succ k ih =>
      let tL := walkNL (fun i => ω (i + 1)) h k
      let tR := walkNR (fun i => ω (i + 1)) h (k + 1)
      let tNext := walkNL (fun i => ω (i + 1)) h (k + 1)
      have hL := lCount_add_on_L_interval ω h k (tR - tL) (by
        have hR := walkNR_succ_spec (fun i => ω (i + 1)) h k
        dsimp [tL, tR]
        omega)
      have hR := lCount_constant_on_R_interval ω h (k + 1) (tNext - tR) (by
        have hN := walkNL_spec (fun i => ω (i + 1)) h (k + 1)
        dsimp [tNext, tR]
        omega)
      have hidxR : tL + (tR - tL) = tR := by
        have h := walkNR_succ_spec (fun i => ω (i + 1)) h k
        dsimp [tL, tR]
        omega
      have hidxN : tR + (tNext - tR) = tNext := by
        have h := walkNL_spec (fun i => ω (i + 1)) h (k + 1)
        dsimp [tNext, tR]
        omega
      have hcount :
          (quadrantSplitState ω tNext).lCount =
            (quadrantSplitState ω tL).lCount + (tR - tL) := by
        calc
          (quadrantSplitState ω tNext).lCount =
              (quadrantSplitState ω (tR + (tNext - tR))).lCount := by rw [hidxN]
          _ = (quadrantSplitState ω tR).lCount := hR
          _ = (quadrantSplitState ω (tL + (tR - tL))).lCount := by rw [hidxR]
          _ = (quadrantSplitState ω tL).lCount + (tR - tL) := hL
      have hwidth : tR - tL = primedIntervalWidth ω h k := by
        rfl
      change (quadrantSplitState ω tNext).lCount = primedIntervalBase ω h (k + 1)
      rw [primedIntervalBase_succ, ← ih]
      change (quadrantSplitState ω tNext).lCount =
        (quadrantSplitState ω tL).lCount + (tR - tL)
      exact hcount

private theorem lPhaseTime_eq_of_lPhase_count (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (n m : ℕ)
    (hp : (quadrantSplitState ω n).phase = .l)
    (hc : (quadrantSplitState ω n).lCount = m) :
    n = lPhaseTime ω h m := by
  let t := lPhaseTime ω h m
  have htphase : (quadrantSplitState ω t).phase = .l := by
    exact lPhaseTime_phase ω h m
  have htcount : (quadrantSplitState ω t).lCount = m := by
    exact lPhaseTime_lCount ω h m
  by_contra hne
  rcases lt_or_gt_of_ne hne with hnt | htn
  · have hstep : (quadrantSplitState ω (n + 1)).lCount = m + 1 := by
      rw [quadrantSplitState, quadrantSplitAdvance_lCount]
      simp [hp, hc]
    have hmono := quadrantSplitState_lCount_mono ω (n + 1) t (by omega)
    rw [hstep, htcount] at hmono
    omega
  · have hstep : (quadrantSplitState ω (t + 1)).lCount = m + 1 := by
      rw [quadrantSplitState, quadrantSplitAdvance_lCount]
      simp [htphase, htcount]
    have hmono := quadrantSplitState_lCount_mono ω (t + 1) n (by omega)
    rw [hstep, hc] at hmono
    omega

/-- The enumerated L-phase time at a block offset agrees with the corresponding
source time in `eqn-quad-pre`. -/
private theorem lPhaseTime_eq_primedIntervalTime (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k j : ℕ)
    (hj : j < primedIntervalWidth ω h k) :
    lPhaseTime ω h (primedIntervalBase ω h k + j) =
      primedIntervalLeft ω h k + j := by
  let t := primedIntervalLeft ω h k + j
  have hright : t < primedIntervalRight ω h k := by
    have hgap := walkNR_succ_spec (fun i => ω (i + 1)) h k
    dsimp [t, primedIntervalRight, primedIntervalWidth] at *
    omega
  have hleft : primedIntervalLeft ω h k ≤ t := by dsimp [t]; omega
  have hphase : (quadrantSplitState ω t).phase = .l := by
    apply (quadrantSplitState_lPhase_iff ω h t).2
    exact ⟨k, hleft, hright⟩
  have hbound : primedIntervalLeft ω h k + j ≤ primedIntervalRight ω h k := by
    dsimp [t] at hright
    omega
  have hcountStep := lCount_add_on_L_interval ω h k j (by
    simpa [primedIntervalLeft, primedIntervalRight] using hbound)
  have htime :
      (quadrantSplitState ω t).lCount = primedIntervalBase ω h k + j := by
    calc
      (quadrantSplitState ω t).lCount =
          (quadrantSplitState ω (primedIntervalLeft ω h k)).lCount + j := by
            simpa [t, primedIntervalLeft] using hcountStep
      _ = primedIntervalBase ω h k + j := by rw [lCount_at_primedIntervalLeft]
  have hunique := lPhaseTime_eq_of_lPhase_count ω h t
    (primedIntervalBase ω h k + j) hphase htime
  exact hunique.symm

/-- At the `m`th L-phase code, its strict new-minimum test is true exactly
when that code exits the L phase (`lem-quadrant-walk`, -/
private theorem lCode_strictNew_iff_lPhaseExit (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) :
    ((codeWalk (lExcursionDummyPrefix (lCode ω)) (m + 1)).2 <
        runningMin (fun j =>
          (codeWalk (lExcursionDummyPrefix (lCode ω)) j).2) m) ↔
      (quadrantSplitState ω (lPhaseTime ω h m + 1)).phase = .r := by
  let t := lPhaseTime ω h m
  have hphase : (quadrantSplitState ω t).phase = .l := by
    exact lPhaseTime_phase ω h m
  have hcount : (quadrantSplitState ω t).lCount = m := by
    exact lPhaseTime_lCount ω h m
  have hmin := quadrantSplit_lRMin_eq_lStream_runningMin ω t
  have hwalk := quadrantSplit_lWalk_eq_lStream ω t
  rw [hcount] at hmin hwalk
  have hcode : (lExcursionDummyPrefix (lCode ω)) (m + 1) = ω (t + 1) := by
    rw [lExcursionDummyPrefix_lCode_eq_phaseSplit]
    rw [← hcount]
    exact phaseSplit_lCode_at_step ω t hphase
  have hnext : (codeWalk (lExcursionDummyPrefix (lCode ω)) (m + 1)).2 =
      (quadrantSplitState ω t).lWalk.2 +
        (lazyTwoDimensionalStep (ω (t + 1))).2 := by
    rw [codeWalk_succ_add_recode, hwalk, hcode]
    rfl
  rw [quadrantSplitState, quadrantSplitAdvance, hphase]
  rw [hmin, hnext]
  simp only [Prod.snd_add]
  by_cases hh :
      (quadrantSplitState ω t).lWalk.2 +
          (lazyTwoDimensionalStep (ω (t + 1))).2 <
        runningMin (fun j =>
          (codeWalk (lExcursionDummyPrefix (lCode ω)) j).2) m
  · simp [t, hh]
  · simp [t, hh]

/-- Every corrected primed interval block is the corresponding segment of the
measurable L-phase recoding (C13; helper only, with no claim about the printed -/
theorem primedCode_block_eq_lExcursionShift (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k j : ℕ)
    (hj : j < primedIntervalWidth ω h k) :
    primedCode ω h (primedIntervalBase ω h k + j) =
      lExcursionShift (lCode ω) (primedIntervalBase ω h k + j) := by
  cases j with
  | zero =>
      rw [primedCode_block ω h k 0 hj]
      by_cases hk : k = 0
      · subst k
        rw [primedIntervalBase_zero]
        simp [lExcursionShift]
      · obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
        have hwidth := primedIntervalWidth_pos ω h q
        have hlast : primedIntervalWidth ω h q - 1 < primedIntervalWidth ω h q := by omega
        let r := primedIntervalBase ω h q +
          (primedIntervalWidth ω h q - 1)
        have htime := lPhaseTime_eq_primedIntervalTime ω h q
          (primedIntervalWidth ω h q - 1) hlast
        have htimeExit : lPhaseTime ω h r + 1 =
            walkNR (fun i => ω (i + 1)) h (q + 1) := by
          change lPhaseTime ω h
              (primedIntervalBase ω h q +
                (primedIntervalWidth ω h q - 1)) + 1 =
            walkNR (fun i => ω (i + 1)) h (q + 1)
          rw [htime]
          simp only [primedIntervalLeft, primedIntervalRight,
            primedIntervalWidth]
          have hgap := walkNR_succ_spec (fun i => ω (i + 1)) h q
          omega
        have hphaseExit : (quadrantSplitState ω (lPhaseTime ω h r + 1)).phase = .r := by
          rw [htimeExit]
          exact (quadrantSplitState_at_walkNR ω h (q + 1)).1
        have hrecord :=
          (lCode_strictNew_iff_lPhaseExit ω h r).2 hphaseExit
        have hindex : primedIntervalBase ω h (q + 1) = r + 1 := by
          rw [primedIntervalBase_succ]
          dsimp [r]
          omega
        rw [hindex, lExcursionShift_succ]
        simp [hrecord]
  | succ j =>
      have hj' : j < primedIntervalWidth ω h k := by omega
      have htime := lPhaseTime_eq_primedIntervalTime ω h k j hj'
      have hphaseNext :
          (quadrantSplitState ω
            (primedIntervalLeft ω h k + j + 1)).phase = .l := by
        apply (quadrantSplitState_lPhase_iff ω h _).2
        refine ⟨k, ?_, ?_⟩
        · dsimp [primedIntervalLeft]
          omega
        · have hgap := walkNR_succ_spec (fun i => ω (i + 1)) h k
          dsimp [primedIntervalRight, primedIntervalWidth,
            primedIntervalLeft] at hj ⊢
          omega
      have hnoRecord : ¬
          ((codeWalk (lExcursionDummyPrefix (lCode ω))
              (primedIntervalBase ω h k + j + 1)).2 <
            runningMin (fun n =>
              (codeWalk (lExcursionDummyPrefix (lCode ω)) n).2)
              (primedIntervalBase ω h k + j)) := by
        intro hrecord
        have hphase :=
          (lCode_strictNew_iff_lPhaseExit ω h
            (primedIntervalBase ω h k + j)).1 hrecord
        rw [htime] at hphase
        rw [hphaseNext] at hphase
        cases hphase
      rw [primedCode_block ω h k (j + 1) hj]
      simp
      rw [show primedIntervalBase ω h k + (j + 1) =
          (primedIntervalBase ω h k + j) + 1 by omega,
        lExcursionShift_succ]
      simp [hnoRecord]
      rw [lCode_eq_walk_at_lPhaseTime ω h (primedIntervalBase ω h k + j), htime]

/-- The corrected primed code stream is the measurable recoding of the L-phase
code stream at every index (C13; helper only, with no claim about the printed -/
theorem primedCode_eq_lExcursionShift (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) :
    primedCode ω h m = lExcursionShift (lCode ω) m := by
  let k := primedIntervalIndex ω h m
  have hlt : m < primedIntervalBase ω h (k + 1) := by
    exact primedIntervalIndex_spec ω h m
  have hbase : primedIntervalBase ω h k ≤ m := by
    by_contra hnot
    have hk0 : k ≠ 0 := by
      intro hk
      rw [hk, primedIntervalBase_zero] at hnot
      omega
    obtain ⟨q, hqk⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hq : q < primedIntervalIndex ω h m := by
      change q < k
      omega
    have hmin := Nat.find_min (primedIntervalIndex_exists ω h m) (by
      simpa [primedIntervalIndex] using hq)
    have hmin' : ¬ m < primedIntervalBase ω h (q + 1) := by
      simpa [primedIntervalIndex] using hmin
    have hmLt : m < primedIntervalBase ω h (q + 1) := by
      have ht := Nat.lt_of_not_ge hnot
      rw [hqk] at ht
      simpa using ht
    exact hmin' hmLt
  have hj : m - primedIntervalBase ω h k < primedIntervalWidth ω h k := by
    rw [primedIntervalBase_succ] at hlt
    omega
  have hdecomp : m = primedIntervalBase ω h k +
      (m - primedIntervalBase ω h k) := by omega
  rw [hdecomp]
  exact primedCode_block_eq_lExcursionShift ω h k
    (m - primedIntervalBase ω h k) hj

end DirectedDistances.KMSW
