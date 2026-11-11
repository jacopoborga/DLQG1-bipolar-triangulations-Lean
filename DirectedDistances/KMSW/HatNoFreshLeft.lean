module

public import DirectedDistances.KMSW.QuadKMSWHatStructure
public import DirectedDistances.KMSW.QuadKMSWHatAllStages

/-! # No fresh left source in the hatted stream

These are structural helpers for `lem-quad-kmsw`
vertex incidence condition for the generic hatted limit argument. -/

public section
namespace DirectedDistances.KMSW

open Quiver
open DirectedDistances.RandomWalk

/-- Every left step of the hatted stream consumes an existing UL predecessor.
Exit indices carry down codes; away from exits, the positive splitter depth
is bounded by the local predecessor count. Structural helper for -/
theorem noFreshLeftSource_hatCodes (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    NoFreshLeftSource (hatCodes w h) := by
  intro m hleft
  by_cases hex : ∃ k, hatExitIndex w h k = m
  · obtain ⟨k, rfl⟩ := hex
    rw [hatCodes_at_exit] at hleft
    simp [kmswCodeStep] at hleft
  · let n := quadrantRStageTime w h m
    have ht : quadrantRStageTime w h (m + 1) = n + 1 := by
      rw [← hatCodeTime_succ, hatCodeTime_of_not_exit w h m hex]
    have hp := (quadrantRStageTime_spec w h m).1
    have hn := (quadrantRStageTime_spec w h (m + 1)).1
    rw [ht] at hn
    have hc : hatCodes w h m = w n := by
      rw [hatCodes, hatCodeTime_of_not_exit w h m hex]
    have h0 : w n = 0 := by
      rw [hc] at hleft
      by_contra hz
      simp only [kmswCodeStep, if_neg hz] at hleft
      split at hleft <;> contradiction
    have hpos : hatPhaseDepth w n ≠ 0 := by
      intro hz
      have he := (hatPhaseDepth_left_exit_iff w n hp h0).2 hz
      rw [hn] at he
      contradiction
    have hb := (hatAll_sim w h m).depth_le
    intro hempty
    rw [hempty] at hb
    exact hpos (Nat.eq_zero_of_le_zero hb)

/-- Every allocated non-root hatted vertex is incident to a present edge with
root-reachable endpoints, the local incidence field of `HatImageLimitInput`.
Structural helper for `lem-quad-kmsw` -/
theorem hatCodes_allocated_nonroot_incident
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ a : PresentVertex (hatCodes w h),
      (∃ m, a.id < (kmswStage (hatCodes w h) m).nextVertex) → a.id ≠ 0 →
      ∃ e, EdgePresent (hatCodes w h) e ∧
        (edgeWest (hatCodes w h) e = a.id ∨ edgeEast (hatCodes w h) e = a.id) ∧
        Reachable (⟨0⟩ : PresentVertex (hatCodes w h))
          ⟨edgeWest (hatCodes w h) e⟩ ∧
        Reachable (⟨0⟩ : PresentVertex (hatCodes w h))
          ⟨edgeEast (hatCodes w h) e⟩ := by
  exact allocated_nonroot_incident_of_noFreshLeftSource (hatCodes w h)
    (noFreshLeftSource_hatCodes w h)

end DirectedDistances.KMSW
