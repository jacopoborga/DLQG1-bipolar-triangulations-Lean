/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.ShiftedHatCodes
public import DirectedDistances.KMSW.ZHatCharacterization
public import DirectedDistances.KMSW.QuadKMSWHatFlipped

/-! # R-code identification for shifted finite windows

These are code-level R-component identifications associated with
`eqn-walk-quadrant`, `lem-quad-kmsw`, and `lem-infty-cut`
identify the full walks or maps and do not prove `lem-quad-kmsw`. -/

public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory
open DirectedDistances.RandomWalk

/-- The law-side R-code sequence of the stage-code quadrant trajectory is
the corresponding exit-replaced code sequence. This identifies only the
R-component at code level in `eqn-walk-quadrant`
`lem-quad-kmsw` (`lines 525–540`), not a proof of that lemma. -/
theorem rCodeSequence_quadrantTrajectory_eq_hatCodes
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    rCodeSequence (quadrantTrajectoryOfStageCodes w) = hatCodes w h := by
  classical
  have hExit (i : ℕ) :
      (∃ k, i = (quadrantSplitState (quadrantTrajectoryOfStageCodes w)
          (walkNL w h k - 1)).rCount) ↔
        ∃ k, hatExitIndex w h k = i := by
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa [hatExitIndex] using hk.symm⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa [hatExitIndex] using hk.symm⟩
  funext i
  rw [rCodeSequence_eq_exitReplaced w h i, hatCodes_pointwise w h i, hExit i]

/-- The R-phase codes of a left-hit-shifted finite window agree with the
exit-replaced codes of its shifted stage-code trajectory. This is a
code-level R-component identification related to `eqn-walk-quadrant` and
assert the full map statement of `lem-quad-kmsw` -/
theorem cutWindowRPhaseCodes_eq_hatCodes
    (ω : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => ω (i + 1)))
    (K : ℕ)
    (hτ : HasFlowLineHits
      (fun i => ω (boundaryHitTime (fun j => ω (j + 1)) h (-(K : ℤ)) + i + 1))) :
    cutWindowRPhaseCodes ω h K =
      hatCodes
        (fun i => ω (boundaryHitTime (fun j => ω (j + 1)) h (-(K : ℤ)) + i + 1))
        hτ := by
  rw [cutWindowRPhaseCodes_eq_shiftedStageCodes]
  exact rCodeSequence_quadrantTrajectory_eq_hatCodes _ hτ

/-- Almost surely, every boundary-hit witness and finite window has a
flow-line-hit witness for which its R-phase code sequence equals the
left-hit-shifted exit-replaced code sequence. This is a code-level
R-component helper for `lem-infty-cut`
of `eqn-walk-quadrant` (`lines 498–520`). It does not prove -/
theorem iidCodes_ae_cutWindow_model_hatCodes :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∀ h : BoundaryHitWitnesses (fun i => ω (i + 1)), ∀ K : ℕ,
        ∃ hτ : HasFlowLineHits
          (fun i => ω (boundaryHitTime (fun j => ω (j + 1)) h
            (-(K : ℤ)) + i + 1)),
          cutWindowRPhaseCodes ω h K =
            hatCodes
              (fun i => ω (boundaryHitTime (fun j => ω (j + 1)) h
                (-(K : ℤ)) + i + 1)) hτ := by
  filter_upwards [iidCodes_ae_hasFlowLineHits_at_all_boundary_leftHits] with ω hω
  intro h K
  exact ⟨hω h K, cutWindowRPhaseCodes_eq_hatCodes ω h K (hω h K)⟩

end DirectedDistances.KMSW
