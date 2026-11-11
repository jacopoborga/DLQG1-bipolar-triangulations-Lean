/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.FlowLineTimes
import DirectedDistances.KMSW.StageIncidenceChains

/-! # Reachability steps for the north flow line

Local present-edge reachability facts for the source argument in -/

public section
namespace DirectedDistances.KMSW

open Quiver

/-- The active edge is present at its own stage, since it is the last edge in -/
theorem kmswStage_active_present (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).present (act w n) = true := by
  obtain ⟨es, hes⟩ := kmswStage_UL_last w n
  have hmem : act w n ∈ (kmswStage w n).UL := by
    rw [hes]
    simp [act]
  exact (kmswStage_status w n).2.1 _ hmem

/-- A reachable initial vertex of the active edge reaches its terminal -/
theorem kmswStage_activeEast_reachable (w : ℕ → Fin 3) (n : ℕ)
    (hr : Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).west (act w n)⟩) :
    Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).east (act w n)⟩ := by
  have he : act w n < (kmswStage w n).nextEdge := act_lt_nextEdge w (le_rfl)
  have hends := edge_endpoints_eq w he
  obtain ⟨p⟩ := hr
  let a : (⟨(kmswStage w n).west (act w n)⟩ : PresentVertex w) ⟶
      ⟨(kmswStage w n).east (act w n)⟩ :=
    ⟨act w n, ⟨n, he, kmswStage_active_present w n⟩,
      hends.1.symm, hends.2.symm⟩
  exact ⟨p.cons a⟩

/-- Root reachability of the active initial vertex is constant across a
horizontal excursion that returns to its starting level without going below -/
theorem kmswStage_activeWest_reachable_of_horizontal_excursion
    (w : ℕ → Fin 3) {m n : ℕ} (hmn : m ≤ n)
    (hlevel : L w m = L w n)
    (habove : ∀ j, m ≤ j → j ≤ n → L w m ≤ L w j)
    (hr : Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w m).west (act w m)⟩) :
    Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).west (act w n)⟩ := by
  have hsame := kmsw_west_act_eq_of_level w hmn hlevel habove
  have hstable := (kmswStage_endpoints_stable w hmn
    (act_lt_nextEdge w (le_rfl : m ≤ m))).1
  have hvertex : (kmswStage w n).west (act w n) =
      (kmswStage w m).west (act w m) := hsame.symm.trans hstable
  rw [hvertex]
  exact hr

/-- An up step preserves the initial vertex of the active edge, so it preserves -/
theorem kmswStage_up_activeWest_reachable (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1)
    (hr : Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).west (act w n)⟩) :
    Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (n + 1)).west (act w (n + 1))⟩ := by
  have hwest : (kmswStage w (n + 1)).west (act w (n + 1)) =
      (kmswStage w n).west (act w n) := by
    simp [act, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep,
      State.addEdge]
  rw [hwest]
  exact hr

/-- A down step preserves root reachability of the active initial vertex by
extending across the old active edge. If a missing upper-right edge is
activated, the stage boundary invariant identifies its west endpoint with the -/
theorem kmswStage_down_activeWest_reachable (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2)
    (hr : Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).west (act w n)⟩) :
    Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (n + 1)).west (act w (n + 1))⟩ := by
  have hEast := kmswStage_activeEast_reachable w n hr
  obtain ⟨_, _, _, _, _, hhead, _⟩ := kmswStage_boundary_chain_invariant w n
  have hwest : (kmswStage w (n + 1)).west (act w (n + 1)) =
      (kmswStage w n).east (act w n) := by
    cases hu : (kmswStage w n).UR with
    | nil =>
        simp [act, kmswStage, kmswStep, kmswCodeStep, hc,
          kmswStepOfStep, hu, State.addEdge]
    | cons e es =>
        have he := hhead e es hu
        simp [act, kmswStage, kmswStep, kmswCodeStep, hc,
          kmswStepOfStep, hu, he]
  rw [hwest]
  exact hEast

end DirectedDistances.KMSW
