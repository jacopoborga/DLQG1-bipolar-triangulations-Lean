/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.HatInducedBoundary
public import DirectedDistances.KMSW.HatNoFreshLeft

/-! # Existing predecessors for hatted left steps

not the paper result. -/

public section
namespace DirectedDistances.KMSW

/-- A left code in the hatted stream has a nonempty upper-left predecessor
list. Helper toward `lem-quad-kmsw` -/
theorem hatStage_UL_pred_ne_nil_of_left (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ)
    (hc : hatCodes w h m = 0) :
    (kmswStage (hatCodes w h) m).UL.dropLast.reverse ≠ [] := by
  have hleft : kmswCodeStep (hatCodes w h m) = .left := by
    rw [hc]
    rfl
  exact noFreshLeftSource_hatCodes w h m hleft

/-- A non-exit left step preserves induced rotation without a separate
predecessor hypothesis. Helper toward `lem-quad-kmsw` -/
theorem hatDartMap_rot_induced_step_left (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ)
    (hm : ¬ ∃ k, hatExitIndex w h k = m)
    (hc : hatCodes w h m = 0)
    (ih : ∀ d : StageDart (kmswStage (hatCodes w h) m).nextEdge,
      ∃ k : ℕ, 0 < k ∧
        ((kmswMap w (quadrantRStageTime w h m)).rot : _ → _)^[k]
          (hatDartMap w h m d) = hatDartMap w h m ((kmswMap (hatCodes w h) m).rot d) ∧
        ∀ j : ℕ, 0 < j → j < k →
          ((kmswMap w (quadrantRStageTime w h m)).rot : _ → _)^[j]
            (hatDartMap w h m d) ∉ Set.range (hatDartMap w h m)) :
    ∀ d : StageDart (kmswStage (hatCodes w h) (m + 1)).nextEdge,
      ∃ k : ℕ, 0 < k ∧
        ((kmswMap w (quadrantRStageTime w h (m + 1))).rot : _ → _)^[k]
          (hatDartMap w h (m + 1) d) =
            hatDartMap w h (m + 1) ((kmswMap (hatCodes w h) (m + 1)).rot d) ∧
        ∀ j : ℕ, 0 < j → j < k →
          ((kmswMap w (quadrantRStageTime w h (m + 1))).rot : _ → _)^[j]
            (hatDartMap w h (m + 1) d) ∉ Set.range (hatDartMap w h (m + 1)) := by
  exact hatDartMap_rot_induced_step_leftExisting w h m hm hc
    (hatStage_UL_pred_ne_nil_of_left w h m hc) ih

end DirectedDistances.KMSW
