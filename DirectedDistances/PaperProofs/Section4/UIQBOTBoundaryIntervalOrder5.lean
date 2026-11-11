/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTBoundaryIntervalOrder4

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the root right and left boundary edges have
the same west endpoint, as witnessed by the KMSW limiting rotation. -/
theorem uiqbotRootBoundaryEdges_sameWestEndpoint
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    edgeWest w (kmswRightBoundaryEdge w 0) =
      edgeWest w (kmswLeftBoundaryEdge w 0) := by
  have hjunc := kmswInfFaceSucc_junction w hfin
    (stageOuterWord_faceSucc w) hL0 htrans hR
  have hrot : (kmswInfRot w hfin).symm
      (kmswRightBoundaryEdge w 0, false) =
      (kmswLeftBoundaryEdge w 0, false) := by
    simpa [kmswInfFaceSucc] using hjunc
  have hrot' : kmswInfRot w hfin
      (kmswLeftBoundaryEdge w 0, false) =
      (kmswRightBoundaryEdge w 0, false) := by
    have h := congrArg (kmswInfRot w hfin) hrot
    simpa using h.symm
  have hv := kmswLimitDartVertex_rot w hfin
    (kmswLeftBoundaryEdge w 0, false)
  have hv' : kmswLimitDartVertex w
      (kmswRightBoundaryEdge w 0, false) =
      kmswLimitDartVertex w (kmswLeftBoundaryEdge w 0, false) := by
    calc
      kmswLimitDartVertex w (kmswRightBoundaryEdge w 0, false) =
          kmswLimitDartVertex w (kmswInfRot w hfin
            (kmswLeftBoundaryEdge w 0, false)) := by rw [hrot']
      _ = kmswLimitDartVertex w (kmswLeftBoundaryEdge w 0, false) := hv
  simpa [kmswLimitDartVertex] using hv'




















































































end DirectedDistances.PaperProofs.Section4

end
