/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.ZHatConverse

/-! # Exit-replacement characterization of the law-side R codes

Combines `rPhaseExitCode_replaced` and `rCodeSequence_eq_raw_of_no_rPhaseExit`.
R-component only, at code level, in the leaving-increment indexing of `ZHatReconcile`; this file does not relate leaving increments to the arriving increments of `Ẑ` in `eqn-walk-quadrant` and does not prove `lem-quad-kmsw`. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk

open Classical in
/-- The law-side R code sequence is the raw stage-code stream with code `2`
substituted at every R-phase exit index (`eqn-walk-quadrant`, `eqn-quad-pre`,
and the proof of `lem-quadrant-walk`,
R-component only, at code level; it does not prove `lem-quad-kmsw`. -/
theorem rCodeSequence_eq_exitReplaced (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (i : ℕ) :
    rCodeSequence (quadrantTrajectoryOfStageCodes w) i =
      (if ∃ k, i = (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
          (walkNL w h k - 1)).rCount then 2
        else quadrantRStageCodes (quadrantTrajectoryOfStageCodes w) i) := by
  split_ifs with hex
  · obtain ⟨k, rfl⟩ := hex
    exact (rPhaseExitCode_replaced w h k).2
  · push Not at hex
    exact rCodeSequence_eq_raw_of_no_rPhaseExit w h i hex

/-- The law-side R code differs from the raw stage code exactly at R-phase
exit indices (raw code `0`, law-side code `2`). R-component only, at code level, in the leaving-increment indexing of `ZHatReconcile`; this file does not relate leaving increments to the arriving increments of `Ẑ` in `eqn-walk-quadrant` and does not prove `lem-quad-kmsw`. -/
theorem rCodeSequence_ne_raw_iff (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (i : ℕ) :
    rCodeSequence (quadrantTrajectoryOfStageCodes w) i ≠
        quadrantRStageCodes (quadrantTrajectoryOfStageCodes w) i ↔
      ∃ k, i = (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
        (walkNL w h k - 1)).rCount := by
  constructor
  · intro hne
    by_contra hno
    push Not at hno
    exact hne (rCodeSequence_eq_raw_of_no_rPhaseExit w h i hno)
  · rintro ⟨k, rfl⟩
    obtain ⟨h0, h2⟩ := rPhaseExitCode_replaced w h k
    rw [h0, h2]
    decide

end DirectedDistances.KMSW
