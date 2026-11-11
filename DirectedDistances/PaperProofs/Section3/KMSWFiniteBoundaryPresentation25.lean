/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation22
public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation23
public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation21

 

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: a geometric successor of a presented dart
has the next cyclic position in the finite outer-word enumeration. -/
theorem kmswStageFiniteBoundaryPresentation25_successor_position
    (w : ℕ → Fin 3) (n : ℕ)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (i j : InfiniteBoundaryDartIndex
      (kmswStageFiniteBoundaryPresentation w n M J))
    (hsucc : (stageRot w n).symm
        (edgeFlip _ (InfiniteBoundaryDartIndex.dart
          (kmswStageFiniteBoundaryPresentation w n M J) i)) =
      InfiniteBoundaryDartIndex.dart
        (kmswStageFiniteBoundaryPresentation w n M J) j) :
    kmswStageFiniteBoundaryPresentation21_position w n M J j =
      boundaryCycleSucc4
        (kmswStageFiniteBoundaryPresentation21_position w n M J i) :=
  (kmswStageFiniteBoundaryPresentation21_successor_iff w n M J i j).mp hsucc















































































































































end DirectedDistances.PaperProofs.Section3

end
