/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation4

/-! module fixes the four stage-corner vertices from the UL and reversed LR run
endpoints. The presentation's retained junction labels then agree with this
concrete record. Actual endpoint validity still requires a plane-map
realization on the stage edge-ID carrier. -/

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the finite UL dart run is nonempty because
the stage's upper-left edge list contains its active edge. -/
theorem kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil
    (w : ℕ → Fin 3) (n : ℕ) : kmswStageULDartRun w n ≠ [] := by
  have hUL := (kmswStage_UL_nonempty_active_last w n).1
  cases hrun : (kmswStage w n).UL with
  | nil => exact (hUL hrun).elim
  | cons e es => simp [kmswStageULDartRun, stageDarts, hrun]

/-- Helper toward Definition 3.2: the reversed finite LR dart run is
nonempty because the stage's lower-right edge list is nonempty. -/
theorem kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil
    (w : ℕ → Fin 3) (n : ℕ) : kmswStageLRDartRun w n ≠ [] := by
  have hLR := kmswStage_LR_nonempty w n
  cases hrun : (kmswStage w n).LR with
  | nil => exact (hLR hrun).elim
  | cons e es => simp [kmswStageLRDartRun, stageDarts, hrun]

/-- Helper toward Definition 3.2: the four finite junction vertices are read
from the initial UL dart, terminal UL dart, initial reversed-LR dart, and
terminal reversed-LR dart of the ordered stage boundary word. -/
@[expose] def kmswStageFiniteBoundaryPresentation5Junctions
    (w : ℕ → Fin 3) (n : ℕ) :
    FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex) := by
  let ul := kmswStageULDartRun w n
  let lr := kmswStageLRDartRun w n
  have hul : ul ≠ [] := kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n
  have hlr : lr ≠ [] := kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n
  exact
    { lowerLeftUpperLeft := stageVertex w n (ul.head hul)
      upperLeftUpperRight := stageVertex w n (edgeFlip _ (ul.getLast hul))
      upperRightLowerRight := stageVertex w n (lr.head hlr)
      lowerRightLowerLeft := stageVertex w n (edgeFlip _ (lr.getLast hlr)) }

/-- Helper toward Definition 3.2: the first corner is the stage endpoint at
the initial dart of the upper-left run. -/
theorem kmswStageFiniteBoundaryPresentation5_lowerLeftUpperLeft
    (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStageFiniteBoundaryPresentation5Junctions w n).lowerLeftUpperLeft =
      stageVertex w n ((kmswStageULDartRun w n).head
        (kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n)) := rfl

/-- Helper toward Definition 3.2: the upper-left/upper-right corner is the
stage endpoint at the terminal dart of the upper-left run. -/
theorem kmswStageFiniteBoundaryPresentation5_upperLeftUpperRight
    (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStageFiniteBoundaryPresentation5Junctions w n).upperLeftUpperRight =
      stageVertex w n (edgeFlip _ ((kmswStageULDartRun w n).getLast
        (kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n))) := rfl

/-- Helper toward Definition 3.2: the upper-right/lower-right corner is the
stage endpoint at the initial dart of the reversed lower-right run. -/
theorem kmswStageFiniteBoundaryPresentation5_upperRightLowerRight
    (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStageFiniteBoundaryPresentation5Junctions w n).upperRightLowerRight =
      stageVertex w n ((kmswStageLRDartRun w n).head
        (kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n)) := rfl

/-- Helper toward Definition 3.2: the lower-right/lower-left corner is the
stage endpoint at the terminal dart of the reversed lower-right run. -/
theorem kmswStageFiniteBoundaryPresentation5_lowerRightLowerLeft
    (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStageFiniteBoundaryPresentation5Junctions w n).lowerRightLowerLeft =
      stageVertex w n (edgeFlip _ ((kmswStageLRDartRun w n).getLast
        (kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n))) := rfl

/-- Helper toward Definition 3.2: all eight retained junction labels of the
finite stage presentation agree with this concrete four-corner record. -/
theorem kmswStageFiniteBoundaryPresentation5_junction_labels
    (w : ℕ → Fin 3) (n : ℕ)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge)) :
    FiniteBoundaryJunctionLabels6
      (kmswStageFiniteBoundaryPresentation w n M
        (kmswStageFiniteBoundaryPresentation5Junctions w n))
      (kmswStageFiniteBoundaryPresentation5Junctions w n) :=
  kmswStage_finite_boundary_junction_labels w n M
    (kmswStageFiniteBoundaryPresentation5Junctions w n)




















































end DirectedDistances.PaperProofs.Section3
