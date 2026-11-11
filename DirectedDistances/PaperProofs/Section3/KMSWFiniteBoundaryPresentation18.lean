/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation13
public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation14

 

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: when the upper-right run is empty, the
canonical upper-left/upper-right and upper-right/lower-right corners agree
under any realized stage map. -/
theorem kmswStageFiniteBoundaryPresentation18_upperRight_empty_corner_eq
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (hempty : (kmswStage w n).UR = []) :
    (kmswStageFiniteBoundaryPresentation5Junctions w n).upperLeftUpperRight =
      (kmswStageFiniteBoundaryPresentation5Junctions w n).upperRightLowerRight := by
  let UL := kmswStageULDartRun w n
  let UR := kmswStageURDartRun w n
  let LR := kmswStageLRDartRun w n
  let LL := kmswStageLLDartRun w n
  have hUL : UL ≠ [] := by
    exact kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n
  have hLR : LR ≠ [] := by
    exact kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n
  have hLRdirect : kmswStageLRDartRun w n ≠ [] := by
    simpa only [LR] using hLR
  have hUR : UR = [] := by
    simp [UR, kmswStageURDartRun, stageDarts, hempty]
  have hrunUR : kmswStageURDartRun w n = [] := by
    simpa only [UR] using hUR
  have htail : UR ++ LR ++ LL ≠ [] := by
    simpa only [hUR, List.nil_append] using
      List.append_ne_nil_of_left_ne_nil hLR LL
  have hh := (kmswStageFiniteBoundaryPresentation14_four_run_handoffs w n).1 hUL htail
  have hh' : (stageRot w n).symm (edgeFlip _ (UL.getLast hUL)) = LR.head hLR := by
    have hhDirect : (stageRot w n).symm (edgeFlip _ (UL.getLast hUL)) =
        (kmswStageURDartRun w n ++ kmswStageLRDartRun w n ++
          kmswStageLLDartRun w n).head htail := by
      change (stageRot w n).symm (edgeFlip _ (UL.getLast hUL)) =
        (UR ++ LR ++ LL).head htail at hh
      simpa only [UR, LR, LL] using hh
    simp only [hrunUR, List.nil_append] at hhDirect
    rw [List.head_append_of_ne_nil hLRdirect] at hhDirect
    simpa only [LR] using hhDirect
  have hj := kmswStageFiniteBoundaryPresentation13_geometric_join
    w n P M hreal (UL.getLast hUL)
  have hj' : boundaryDartTerminal M (UL.getLast hUL) =
      boundaryDartInitial M (LR.head hLR) := by
    have hjEq : boundaryDartTerminal M (UL.getLast hUL) =
        boundaryDartInitial M ((stageRot w n).symm
          (edgeFlip _ (UL.getLast hUL))) := by
      simpa [edgeFlip] using hj
    rw [hh'] at hjEq
    exact hjEq
  calc
    (kmswStageFiniteBoundaryPresentation5Junctions w n).upperLeftUpperRight =
        stageVertex w n (edgeFlip _ (UL.getLast hUL)) :=
      kmswStageFiniteBoundaryPresentation5_upperLeftUpperRight w n
    _ = boundaryDartTerminal M (UL.getLast hUL) := by
      symm
      exact kmswStageFiniteBoundaryPresentation6_terminal_endpoint w n P M hreal _
    _ = boundaryDartInitial M (LR.head hLR) := hj'
    _ = stageVertex w n (LR.head hLR) :=
      kmswStageFiniteBoundaryPresentation6_initial_endpoint w n P M hreal _
    _ = (kmswStageFiniteBoundaryPresentation5Junctions w n).upperRightLowerRight := by
      symm
      exact kmswStageFiniteBoundaryPresentation5_upperRightLowerRight w n

/-- Helper toward Definition 3.2: when the lower-left run is empty, the
canonical lower-right/lower-left and lower-left/upper-left corners agree
under any realized stage map. -/
theorem kmswStageFiniteBoundaryPresentation18_lowerLeft_empty_corner_eq
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (hempty : (kmswStage w n).LL = []) :
    (kmswStageFiniteBoundaryPresentation5Junctions w n).lowerRightLowerLeft =
      (kmswStageFiniteBoundaryPresentation5Junctions w n).lowerLeftUpperLeft := by
  let UL := kmswStageULDartRun w n
  let UR := kmswStageURDartRun w n
  let LR := kmswStageLRDartRun w n
  let LL := kmswStageLLDartRun w n
  have hUL : UL ≠ [] := by
    exact kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n
  have hULdirect : kmswStageULDartRun w n ≠ [] := by
    simpa only [UL] using hUL
  have hLR : LR ≠ [] := by
    exact kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n
  have hLL : LL = [] := by
    simp [LL, kmswStageLLDartRun, stageDarts, hempty]
  have hrunLL : kmswStageLLDartRun w n = [] := by
    simpa only [LL] using hLL
  have htail : LL ++ UL ++ UR ≠ [] := by
    simpa only [hLL, List.nil_append] using
      List.append_ne_nil_of_left_ne_nil hUL UR
  have hh := (kmswStageFiniteBoundaryPresentation14_four_run_handoffs w n).2.2.1
    hLR htail
  have hh' : (stageRot w n).symm (edgeFlip _ (LR.getLast hLR)) = UL.head hUL := by
    have hhDirect : (stageRot w n).symm (edgeFlip _ (LR.getLast hLR)) =
        (kmswStageLLDartRun w n ++ kmswStageULDartRun w n ++
          kmswStageURDartRun w n).head htail := by
      change (stageRot w n).symm (edgeFlip _ (LR.getLast hLR)) =
        (LL ++ UL ++ UR).head htail at hh
      simpa only [UL, UR, LL] using hh
    simp only [hrunLL, List.nil_append] at hhDirect
    rw [List.head_append_of_ne_nil hULdirect] at hhDirect
    simpa only [UL] using hhDirect
  have hj := kmswStageFiniteBoundaryPresentation13_geometric_join
    w n P M hreal (LR.getLast hLR)
  have hj' : boundaryDartTerminal M (LR.getLast hLR) =
      boundaryDartInitial M (UL.head hUL) := by
    have hjEq : boundaryDartTerminal M (LR.getLast hLR) =
        boundaryDartInitial M ((stageRot w n).symm
          (edgeFlip _ (LR.getLast hLR))) := by
      simpa [edgeFlip] using hj
    rw [hh'] at hjEq
    exact hjEq
  calc
    (kmswStageFiniteBoundaryPresentation5Junctions w n).lowerRightLowerLeft =
        stageVertex w n (edgeFlip _ (LR.getLast hLR)) :=
      kmswStageFiniteBoundaryPresentation5_lowerRightLowerLeft w n
    _ = boundaryDartTerminal M (LR.getLast hLR) := by
      symm
      exact kmswStageFiniteBoundaryPresentation6_terminal_endpoint w n P M hreal _
    _ = boundaryDartInitial M (UL.head hUL) := hj'
    _ = stageVertex w n (UL.head hUL) :=
      kmswStageFiniteBoundaryPresentation6_initial_endpoint w n P M hreal _
    _ = (kmswStageFiniteBoundaryPresentation5Junctions w n).lowerLeftUpperLeft := by
      symm
      exact kmswStageFiniteBoundaryPresentation5_lowerLeftUpperLeft w n























































































end DirectedDistances.PaperProofs.Section3

end
