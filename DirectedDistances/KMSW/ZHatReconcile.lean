/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.QuadKMSWHatGeneral
public import DirectedDistances.KMSW.RPhaseLawTransfer
import DirectedDistances.KMSW.PhaseTimesBridge2

/-! # Reconcile the simulated and law-side R streams

`QuadKMSWHatSim` builds the M-hat simulation from the unflipped
`quadrantRStageCodes` stream: at R-state `n` it reads the code leaving that
state, including the exit code at `walkNL w h k - 1`. The law transfer uses
`rCodeSequence`, which is `pitmanCode` applied to `rPhaseCodeSequence`
Thus the law-side code sequence is the Pitman-flipped R stream, not the raw
simulation stream. The exit theorem below proves the explicit replacement
`0 ↦ 2` at every R-phase exit; the pointwise formula records exactly how
`rCodeSequence` is obtained from the raw stream.
The converse — every index where `rCodeSequence` differs from `quadrantRStageCodes` is an R-phase exit index — is not proved in this file. It is proved in `ZHatConverse.lean` (`rCodeSequence_strictNew_iff_rPhaseExit`: strict new minimum ⇔ R-phase exit) and `ZHatCharacterization.lean` (`rCodeSequence_ne_raw_iff`: differs from the raw code ⇔ R-phase exit). -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk

private theorem rPhaseCodeWalk_eq_rWalk (ω : ℕ → Fin 3) (n : ℕ) :
    integrateCodes (rPhaseCodeSequence ω)
        (quadrantSplitState ω n).rCount =
      (quadrantSplitState ω n).rWalk := by
  calc
    integrateCodes (rPhaseCodeSequence ω) (quadrantSplitState ω n).rCount =
        codeWalk (phaseSplit ω).1 (quadrantSplitState ω n).rCount := by
          rw [codeWalk_eq_integrateCodes]
          rfl
    _ = codeWalk (phaseSplit ω).1
          (quadrantInterleaveState (phaseSplit ω).1 (phaseSplit ω).2 n).rCount := by
          rw [quadrantInterleaveState_phaseSplit]
    _ = (quadrantInterleaveState (phaseSplit ω).1 (phaseSplit ω).2 n).rWalk :=
          (quadrantInterleaveState_rWalk (phaseSplit ω) n).symm
    _ = (quadrantSplitState ω n).rWalk := by
          rw [quadrantInterleaveState_phaseSplit]

/-- The exact coordinate formula used by the law-side code sequence. It
agrees with the raw `quadrantRStageCodes` code unless the integrated first
coordinate makes a new strict running minimum, in which case the law-side value is `2` (at R-phase exit indices the raw code is `0`, see `rPhaseExitCode_replaced`) (`lem-quadrant-walk`, -/
theorem rCodeSequence_pointwise (w : ℕ → Fin 3) (i : ℕ) :
    rCodeSequence (quadrantTrajectoryOfStageCodes w) i =
      if ∀ j ≤ i,
        (integrateCodes (quadrantRStageCodes
          (quadrantTrajectoryOfStageCodes w)) (i + 1)).1 <
          (integrateCodes (quadrantRStageCodes
            (quadrantTrajectoryOfStageCodes w)) j).1 then 2
      else quadrantRStageCodes (quadrantTrajectoryOfStageCodes w) i := by
  change pitmanCode (quadrantRStageCodes
    (quadrantTrajectoryOfStageCodes w)) i = _
  unfold pitmanCode
  rfl

/-- At every R-phase exit, the unflipped simulation stream reads the
departing code `0` at the state index `walkNL w h k - 1`, while the
law-side `rCodeSequence` replaces it by `2`. The code index is the number of
R codes consumed at that pre-exit state. The converse — every index where `rCodeSequence` differs from `quadrantRStageCodes` is an R-phase exit index — is not proved in this file. It is proved in `ZHatConverse.lean` (`rCodeSequence_strictNew_iff_rPhaseExit`: strict new minimum ⇔ R-phase exit) and `ZHatCharacterization.lean` (`rCodeSequence_ne_raw_iff`: differs from the raw code ⇔ R-phase exit). (`eqn-quad-pre`, -/
theorem rPhaseExitCode_replaced (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    quadrantRStageCodes (quadrantTrajectoryOfStageCodes w)
        ((quadrantSplitState (quadrantTrajectoryOfStageCodes w)
          (walkNL w h k - 1)).rCount) = 0 ∧
      rCodeSequence (quadrantTrajectoryOfStageCodes w)
        ((quadrantSplitState (quadrantTrajectoryOfStageCodes w)
          (walkNL w h k - 1)).rCount) = 2 := by
  let ω := quadrantTrajectoryOfStageCodes w
  let n := walkNL w h k - 1
  let i := (quadrantSplitState ω n).rCount
  have hbounds : walkNR w h k ≤ n ∧ n < walkNL w h k := by
    dsimp [n]
    have hs := (walkNL_spec w h k).1
    omega
  have hphase : (quadrantSplitState ω n).phase = .r := by
    exact (quadrantSplitState_rPhase_iff ω h n).2 ⟨k, hbounds.1, hbounds.2⟩
  have hExit : (quadrantSplitState ω (n + 1)).phase = .l := by
    have hidx : n + 1 = walkNL w h k := by dsimp [n]; omega
    rw [hidx]
    exact (quadrantSplitState_at_walkNL ω h k).1
  have hstep : quadrantSplitState ω (n + 1) =
      quadrantSplitAdvance (quadrantSplitState ω n) (ω (n + 1)) := by
    rfl
  have hnextBelow :
      (quadrantSplitState ω n).rWalk.1 +
        (lazyTwoDimensionalStep (ω (n + 1))).1 <
        (quadrantSplitState ω n).rLMin := by
    rw [hstep] at hExit
    simpa [quadrantSplitAdvance, hphase] using hExit
  have hcount : (quadrantSplitState ω n).rCount = i := rfl
  have hcountNext : (quadrantSplitState ω (n + 1)).rCount = i + 1 := by
    rw [hstep, quadrantSplitAdvance_rCount, hphase, if_pos rfl, hcount]
  have hprior (j : ℕ) (hj : j ≤ i) :
      (quadrantSplitState ω n).rLMin ≤
        (integrateCodes (rPhaseCodeSequence ω) j).1 := by
    have hj' : j ≤
        (quadrantInterleaveState (phaseSplit ω).1 (phaseSplit ω).2 n).rCount := by
      rw [quadrantInterleaveState_phaseSplit]
      simpa [i] using hj
    have hlow := quadrantInterleaveState_rLMin_le_prefix
      (phaseSplit ω) n j hj'
    rw [quadrantInterleaveState_phaseSplit] at hlow
    rw [codeWalk_eq_integrateCodes (phaseSplit ω).1 j] at hlow
    change (quadrantSplitState ω n).rLMin ≤
      (integrateCodes (fun q => (phaseSplit ω).1 (q + 1)) j).1
    exact hlow
  have hnew :
      (integrateCodes (rPhaseCodeSequence ω) (i + 1)).1 <
        (quadrantSplitState ω n).rLMin := by
    have hwalk := rPhaseCodeWalk_eq_rWalk ω (n + 1)
    rw [hcountNext] at hwalk
    rw [hstep] at hwalk
    have hwalkFst := congrArg Prod.fst hwalk
    simp [quadrantSplitAdvance, hphase] at hwalkFst
    exact lt_of_eq_of_lt hwalkFst hnextBelow
  have hflip : ∀ j ≤ i,
      (integrateCodes (rPhaseCodeSequence ω) (i + 1)).1 <
        (integrateCodes (rPhaseCodeSequence ω) j).1 := by
    intro j hj
    exact lt_of_lt_of_le hnew (hprior j hj)
  have hraw : rPhaseCodeSequence ω i = 0 :=
    pitmanCode_of_flip (rPhaseCodeSequence ω) i hflip
  have hrawEq : quadrantRStageCodes ω i = rPhaseCodeSequence ω i := rfl
  constructor
  · rw [hrawEq, hraw]
  · change pitmanCode (rPhaseCodeSequence ω) i = 2
    unfold pitmanCode
    rw [if_pos hflip]

end DirectedDistances.KMSW
