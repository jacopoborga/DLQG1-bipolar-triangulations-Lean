/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.ZHatReconcile
public import DirectedDistances.KMSW.QuadKMSWHatSim

/-! # Characterize the replaced R-phase codes

The converse code statement uses the arriving-increment convention in
`eqn-walk-quadrant`, the pre-exit indexing in `eqn-quad-pre`, and the proof of
Together with `rPhaseExitCode_replaced` it characterizes `rCodeSequence` as the raw R stream with code `0` replaced by `2` exactly at R-phase exit indices (R-component only, leaving-increment indexing; the L stream and the identification of the full sequence with Ẑ are not addressed here); it does not prove `lem-quad-kmsw`. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk

private theorem quadrantInterleaveState_rLMin_attained
    (ab : (ℕ → Fin 3) × (ℕ → Fin 3)) :
    ∀ n, ∃ j ≤ (quadrantInterleaveState ab.1 ab.2 n).rCount,
      (codeWalk ab.1 j).1 = (quadrantInterleaveState ab.1 ab.2 n).rLMin := by
  intro n
  induction n with
  | zero =>
      refine ⟨0, ?_, ?_⟩ <;> simp [quadrantInterleaveState, quadrantSplitStart,
        codeWalk_zero]
  | succ n ih =>
      cases hphase : (quadrantInterleaveState ab.1 ab.2 n).phase with
      | r =>
          let s := quadrantInterleaveState ab.1 ab.2 n
          have hsphase : s.phase = .r := by simpa [s] using hphase
          have hstep : quadrantInterleaveState ab.1 ab.2 (n + 1) =
              quadrantSplitAdvance s (ab.1 (s.rCount + 1)) := by
            simp [quadrantInterleaveState, s, hsphase]
          have hcount :
              (quadrantInterleaveState ab.1 ab.2 (n + 1)).rCount = s.rCount + 1 := by
            rw [hstep]
            simp [quadrantSplitAdvance, hsphase]
          by_cases hhit :
              (s.rWalk + lazyTwoDimensionalStep (ab.1 (s.rCount + 1))).1 < s.rLMin
          · have hhit' :
                s.rWalk.1 + (lazyTwoDimensionalStep (ab.1 (s.rCount + 1))).1 < s.rLMin := by
              simpa only [Prod.fst_add] using hhit
            refine ⟨s.rCount + 1, by omega, ?_⟩
            have hwalk :
                (quadrantInterleaveState ab.1 ab.2 (n + 1)).rWalk =
                  s.rWalk + lazyTwoDimensionalStep (ab.1 (s.rCount + 1)) := by
              rw [hstep]
              simp [quadrantSplitAdvance, hsphase]
            have hminAfter :
                (quadrantInterleaveState ab.1 ab.2 (n + 1)).rLMin =
                  (s.rWalk + lazyTwoDimensionalStep (ab.1 (s.rCount + 1))).1 := by
              rw [hstep]
              simp [quadrantSplitAdvance, hsphase, hhit']
            have hcountAfter :
                (quadrantInterleaveState ab.1 ab.2 (n + 1)).rCount = s.rCount + 1 := hcount
            have hrwalk := quadrantInterleaveState_rWalk ab (n + 1)
            rw [hcountAfter] at hrwalk
            rw [hwalk] at hrwalk
            rw [hminAfter]
            exact (congrArg Prod.fst hrwalk).symm
          · have hhit' :
                ¬ s.rWalk.1 + (lazyTwoDimensionalStep (ab.1 (s.rCount + 1))).1 < s.rLMin := by
              intro hh
              apply hhit
              simpa only [Prod.fst_add] using hh
            obtain ⟨j, hj, hmin⟩ := ih
            refine ⟨j, ?_, ?_⟩
            · have hjS : j ≤ s.rCount := by simpa [s] using hj
              rw [hcount]
              omega
            · have hminS : (codeWalk ab.1 j).1 = s.rLMin := by
                simpa [s] using hmin
              have hminAfter :
                  (quadrantInterleaveState ab.1 ab.2 (n + 1)).rLMin = s.rLMin := by
                rw [hstep]
                simp [quadrantSplitAdvance, hsphase, hhit']
              rw [hminAfter]
              exact hminS
      | l =>
          let s := quadrantInterleaveState ab.1 ab.2 n
          have hsphase : s.phase = .l := by simpa [s] using hphase
          obtain ⟨j, hj, hmin⟩ := ih
          refine ⟨j, ?_, ?_⟩
          · have hcount :
                (quadrantInterleaveState ab.1 ab.2 (n + 1)).rCount = s.rCount := by
              rw [show quadrantInterleaveState ab.1 ab.2 (n + 1) =
                quadrantSplitAdvance s (ab.2 (s.lCount + 1)) by
                  simp [quadrantInterleaveState, s, hsphase]]
              simp [quadrantSplitAdvance, hsphase]
            rw [hcount]
            simpa [s] using hj
          · rw [show quadrantInterleaveState ab.1 ab.2 (n + 1) =
              quadrantSplitAdvance s (ab.2 (s.lCount + 1)) by
                simp [quadrantInterleaveState, s, hsphase]]
            simpa [quadrantSplitAdvance, hsphase, s] using hmin

/-- A strict new running minimum in the integrated unflipped R stream occurs
exactly at an R-phase exit. This is the converse to the replacement direction
in `rPhaseExitCode_replaced` (`eqn-walk-quadrant`, `eqn-quad-pre`, and the -/
theorem rCodeSequence_strictNew_iff_rPhaseExit (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (i : ℕ) :
    (∀ j ≤ i,
      (integrateCodes (quadrantRStageCodes
        (quadrantTrajectoryOfStageCodes w)) (i + 1)).1 <
        (integrateCodes (quadrantRStageCodes
          (quadrantTrajectoryOfStageCodes w)) j).1) ↔
      ∃ k, i = (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
        (walkNL w h k - 1)).rCount := by
  constructor
  · intro hnew
    let ω := quadrantTrajectoryOfStageCodes w
    let ab := phaseSplit ω
    obtain ⟨n, hnphase, hncount, _⟩ := quadrantRStageCodes_has_RPhaseTime w h i
    have hω : HasFlowLineHits (fun q => ω (q + 1)) := by
      simpa [ω, quadrantTrajectoryOfStageCodes] using h
    have hstate : quadrantInterleaveState ab.1 ab.2 n =
        quadrantSplitState ω n := by
      exact quadrantInterleaveState_phaseSplit ω n
    have hcount : (quadrantInterleaveState ab.1 ab.2 n).rCount = i := by
      rw [hstate]
      exact hncount
    have hphase : (quadrantInterleaveState ab.1 ab.2 n).phase = .r := by
      rw [hstate]
      exact hnphase
    have hnewCode : ∀ j ≤ i,
        (codeWalk ab.1 (i + 1)).1 < (codeWalk ab.1 j).1 := by
      intro j hj
      have hjnew := hnew j hj
      change (integrateCodes (fun q => (phaseSplit ω).1 (q + 1)) (i + 1)).1 <
        (integrateCodes (fun q => (phaseSplit ω).1 (q + 1)) j).1 at hjnew
      rw [← codeWalk_eq_integrateCodes, ← codeWalk_eq_integrateCodes] at hjnew
      simpa [ab] using hjnew
    obtain ⟨j, hj, hjmin⟩ := quadrantInterleaveState_rLMin_attained ab n
    have hj' : j ≤ i := by rw [← hcount]; exact hj
    have hmin :
        (quadrantInterleaveState ab.1 ab.2 n).rLMin = (codeWalk ab.1 j).1 :=
      hjmin.symm
    have hbelow :
        (codeWalk ab.1 (i + 1)).1 <
          (quadrantInterleaveState ab.1 ab.2 n).rLMin := by
      rw [hmin]
      exact hnewCode j hj'
    have hnextCount :
        (quadrantSplitState ω (n + 1)).rCount = i + 1 := by
      rw [quadrantSplitState, quadrantSplitAdvance_rCount, hnphase, if_pos rfl,
        hncount]
    have hnextCountI :
        (quadrantInterleaveState ab.1 ab.2 (n + 1)).rCount = i + 1 := by
      rw [quadrantInterleaveState_phaseSplit ω (n + 1)]
      exact hnextCount
    have hnextWalk :
        (quadrantSplitState ω (n + 1)).rWalk = codeWalk ab.1 (i + 1) := by
      calc
        (quadrantSplitState ω (n + 1)).rWalk =
            (quadrantInterleaveState ab.1 ab.2 (n + 1)).rWalk := by
              rw [← quadrantInterleaveState_phaseSplit ω (n + 1)]
        _ = codeWalk ab.1 (quadrantInterleaveState ab.1 ab.2 (n + 1)).rCount :=
              quadrantInterleaveState_rWalk ab (n + 1)
        _ = codeWalk ab.1 (i + 1) := by rw [hnextCountI]
    have hstep : quadrantSplitState ω (n + 1) =
        quadrantSplitAdvance (quadrantSplitState ω n) (ω (n + 1)) := rfl
    let s := quadrantSplitState ω n
    have hsphase : s.phase = .r := by simpa [s] using hnphase
    have hwalkstep :
        (quadrantSplitState ω (n + 1)).rWalk =
          (quadrantSplitState ω n).rWalk + lazyTwoDimensionalStep (ω (n + 1)) := by
      rw [hstep]
      simp [quadrantSplitAdvance, hsphase, s]
    have hbelowState :
        (codeWalk ab.1 (i + 1)).1 < (quadrantSplitState ω n).rLMin := by
      rw [hstate] at hbelow
      exact hbelow
    have hbelowNext :
        ((quadrantSplitState ω (n + 1)).rWalk).1 < (quadrantSplitState ω n).rLMin := by
      rw [hnextWalk]
      exact hbelowState
    have hhit :
        ((quadrantSplitState ω n).rWalk +
          lazyTwoDimensionalStep (ω (n + 1))).1 <
          (quadrantSplitState ω n).rLMin := by
      rw [← hwalkstep]
      exact hbelowNext
    have hnextPhase : (quadrantSplitState ω (n + 1)).phase = .l := by
      rw [hstep]
      have hhit' :
          (quadrantSplitState ω n).rWalk.1 +
            (lazyTwoDimensionalStep (ω (n + 1))).1 <
            (quadrantSplitState ω n).rLMin := by
        simpa only [Prod.fst_add] using hhit
      simp [quadrantSplitAdvance, hsphase, hhit', s]
    obtain ⟨k, hentry, hexit⟩ :=
      (quadrantSplitState_rPhase_iff ω hω n).mp hnphase
    have hentry' : walkNR w h k ≤ n ∧ n < walkNL w h k := by
      constructor
      · simpa [ω, quadrantTrajectoryOfStageCodes] using hentry
      · simpa [ω, quadrantTrajectoryOfStageCodes] using hexit
    have htime : walkNL w h k = n + 1 := by
      apply le_antisymm
      · by_contra hnot
        have hnlt : n + 1 < walkNL w h k := by omega
        have hnextEntry :
            walkNR (fun q => ω (q + 1)) hω k ≤ n + 1 := by
          have hNR : walkNR (fun q => ω (q + 1)) hω k ≤ n := by
            simpa [ω, quadrantTrajectoryOfStageCodes] using hentry'.1
          omega
        have hnextR := (quadrantSplitState_rPhase_iff ω hω (n + 1)).2
          ⟨k, hnextEntry, hnlt⟩
        rw [hnextPhase] at hnextR
        cases hnextR
      · omega
    refine ⟨k, ?_⟩
    have hpre : walkNL w h k - 1 = n := by omega
    rw [hpre]
    exact hncount.symm
  · rintro ⟨k, rfl⟩
    have hreplace := rPhaseExitCode_replaced w h k
    have hpoint := rCodeSequence_pointwise w
      ((quadrantSplitState (quadrantTrajectoryOfStageCodes w)
        (walkNL w h k - 1)).rCount)
    have hraw : quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)
        ((quadrantSplitState (quadrantTrajectoryOfStageCodes w)
          (walkNL w h k - 1)).rCount) = 0 := hreplace.1
    have hcond : ∀ j ≤
        (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
          (walkNL w h k - 1)).rCount,
        (integrateCodes (quadrantRStageCodes
          (quadrantTrajectoryOfStageCodes w))
          ((quadrantSplitState (quadrantTrajectoryOfStageCodes w)
            (walkNL w h k - 1)).rCount + 1)).1 <
          (integrateCodes (quadrantRStageCodes
            (quadrantTrajectoryOfStageCodes w)) j).1 := by
      by_contra hnot
      have hfalse : ¬ ∀ j ≤
          (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
            (walkNL w h k - 1)).rCount,
          (integrateCodes (quadrantRStageCodes
            (quadrantTrajectoryOfStageCodes w))
            ((quadrantSplitState (quadrantTrajectoryOfStageCodes w)
              (walkNL w h k - 1)).rCount + 1)).1 <
            (integrateCodes (quadrantRStageCodes
              (quadrantTrajectoryOfStageCodes w)) j).1 := hnot
      rw [hpoint, if_neg hfalse] at hreplace
      omega
    exact hcond

/-- Away from every R-phase exit, the law-side R code equals the raw
stage-code input. At each exit it is `2` by `rPhaseExitCode_replaced`; together
these give the exit-replacement characterization, the code-level input to the M-hat proof of
`lem-quad-kmsw`, not its map-level simulation (`eqn-walk-quadrant`, -/
theorem rCodeSequence_eq_raw_of_no_rPhaseExit (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (i : ℕ)
    (hno : ∀ k, i ≠
      (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
        (walkNL w h k - 1)).rCount) :
    rCodeSequence (quadrantTrajectoryOfStageCodes w) i =
      quadrantRStageCodes (quadrantTrajectoryOfStageCodes w) i := by
  have hnotStrict : ¬ ∀ j ≤ i,
      (integrateCodes (quadrantRStageCodes
        (quadrantTrajectoryOfStageCodes w)) (i + 1)).1 <
        (integrateCodes (quadrantRStageCodes
          (quadrantTrajectoryOfStageCodes w)) j).1 := by
    intro hstrict
    obtain ⟨k, hk⟩ :=
      (rCodeSequence_strictNew_iff_rPhaseExit w h i).1 hstrict
    exact hno k hk
  rw [rCodeSequence_pointwise w i]
  simp only [if_neg hnotStrict]

end DirectedDistances.KMSW
