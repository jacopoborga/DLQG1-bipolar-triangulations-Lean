/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation12

 

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: under a realization, the stage's geometric
rotation joins each dart's terminal vertex to its successor's initial vertex. -/
theorem kmswStageFiniteBoundaryPresentation13_geometric_join
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (d : StageDart (kmswStage w n).nextEdge) :
    boundaryDartTerminal M d =
      boundaryDartInitial M ((stageRot w n).symm (d.1, !d.2)) := by
  have hrot := P.vert_rotation ((stageRot w n).symm (d.1, !d.2))
  rw [Equiv.apply_symm_apply] at hrot
  calc
    boundaryDartTerminal M d = stageVertex w n (edgeFlip _ d) :=
      kmswStageFiniteBoundaryPresentation6_terminal_endpoint w n P M hreal d
    _ = stageVertex w n ((stageRot w n).symm (d.1, !d.2)) := by
      simpa [edgeFlip] using hrot
    _ = boundaryDartInitial M ((stageRot w n).symm (d.1, !d.2)) :=
      (kmswStageFiniteBoundaryPresentation6_initial_endpoint w n P M hreal _).symm

/-- Helper toward Definition 3.2: the exact-tag stage presentation always
has nonempty upper-left and lower-right present-path index types. -/
theorem kmswStageFiniteBoundaryPresentation13_present_sides_nonempty
    (w : ℕ → Fin 3) (n : ℕ)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)) :
    Nonempty (kmswStageFiniteBoundaryPresentation w n M J).upperLeft.Index ∧
      Nonempty (kmswStageFiniteBoundaryPresentation w n M J).lowerRight.Index := by
  constructor
  · change Nonempty (Fin (kmswStageULDartRun w n).length)
    have hpos : 0 < (kmswStageULDartRun w n).length := by
      cases hrun : kmswStageULDartRun w n with
      | nil => exact False.elim ((kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n) hrun)
      | cons e es => simp
    exact ⟨⟨0, hpos⟩⟩
  · change Nonempty (Fin (kmswStageLRDartRun w n).length)
    have hpos : 0 < (kmswStageLRDartRun w n).length := by
      cases hrun : kmswStageLRDartRun w n with
      | nil => exact False.elim ((kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n) hrun)
      | cons e es => simp
    exact ⟨⟨0, hpos⟩⟩






































end DirectedDistances.PaperProofs.Section3

end
