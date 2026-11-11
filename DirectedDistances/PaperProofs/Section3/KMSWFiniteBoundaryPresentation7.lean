/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation6

/-! module records endpoint identities for the concrete edge-ID drawing and the
remaining exact-missing realization and finite boundary-label obligations.
It does not assert paper completion. -/

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the concrete edge-ID drawing's dart
endpoints are the stage endpoints, independently of its missing-edge tags. -/
theorem kmswStageFiniteBoundaryPresentation7_constructed_dart_endpoints
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (d : StageDart (kmswStage w n).nextEdge) :
    let M := kmswStageFiniteBoundaryPresentation6DirectedPlaneMap w n P
    boundaryDartInitial M d = stageVertex w n d ∧
      boundaryDartTerminal M d = stageVertex w n (edgeFlip _ d) := by
  constructor
  · exact kmswStageFiniteBoundaryPresentation6_constructed_initial_endpoint w n P d
  · exact kmswStageFiniteBoundaryPresentation6_constructed_terminal_endpoint w n P d

/-- Helper toward Definition 3.2: the initial endpoint at the first upper-left
run dart is the corresponding vertex in the concrete four-corner record. -/
theorem kmswStageFiniteBoundaryPresentation7_upperLeft_first_initial
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) :
    boundaryDartInitial
      (kmswStageFiniteBoundaryPresentation6DirectedPlaneMap w n P)
      ((kmswStageULDartRun w n).head
        (kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n)) =
      (kmswStageFiniteBoundaryPresentation5Junctions w n).lowerLeftUpperLeft := by
  rw [kmswStageFiniteBoundaryPresentation6_constructed_initial_endpoint]
  rfl

/-- Helper toward Definition 3.2: the terminal endpoint at the last
upper-left run dart is the corresponding vertex in the concrete four-corner
record. -/
theorem kmswStageFiniteBoundaryPresentation7_upperLeft_last_terminal
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) :
    boundaryDartTerminal
      (kmswStageFiniteBoundaryPresentation6DirectedPlaneMap w n P)
      ((kmswStageULDartRun w n).getLast
        (kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n)) =
      (kmswStageFiniteBoundaryPresentation5Junctions w n).upperLeftUpperRight := by
  rw [kmswStageFiniteBoundaryPresentation6_constructed_terminal_endpoint]
  simp [kmswStageFiniteBoundaryPresentation5Junctions]

/-- Helper toward Definition 3.2: the initial endpoint at the first reversed
lower-right run dart is the corresponding vertex in the concrete four-corner
record. -/
theorem kmswStageFiniteBoundaryPresentation7_lowerRight_first_initial
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) :
    boundaryDartInitial
      (kmswStageFiniteBoundaryPresentation6DirectedPlaneMap w n P)
      ((kmswStageLRDartRun w n).head
        (kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n)) =
      (kmswStageFiniteBoundaryPresentation5Junctions w n).upperRightLowerRight := by
  rw [kmswStageFiniteBoundaryPresentation6_constructed_initial_endpoint]
  rfl

/-- Helper toward Definition 3.2: the terminal endpoint at the last
lower-right run dart is the corresponding vertex in the concrete four-corner
record. -/
theorem kmswStageFiniteBoundaryPresentation7_lowerRight_last_terminal
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) :
    boundaryDartTerminal
      (kmswStageFiniteBoundaryPresentation6DirectedPlaneMap w n P)
      ((kmswStageLRDartRun w n).getLast
        (kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n)) =
      (kmswStageFiniteBoundaryPresentation5Junctions w n).lowerRightLowerLeft := by
  rw [kmswStageFiniteBoundaryPresentation6_constructed_terminal_endpoint]
  simp [kmswStageFiniteBoundaryPresentation5Junctions]












































end DirectedDistances.PaperProofs.Section3
