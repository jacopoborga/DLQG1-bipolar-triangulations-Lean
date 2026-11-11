/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTBoundaryIntervalOrder5



















public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the two root KMSW darts with false
traversal bits have the same limiting vertex. -/
theorem uiqbotRootBoundaryLimitDartVertex_sameWestEndpoint
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    kmswLimitDartVertex w (kmswRightBoundaryEdge w 0, false) =
      kmswLimitDartVertex w (kmswLeftBoundaryEdge w 0, false) := by
  simpa [kmswLimitDartVertex] using
    uiqbotRootBoundaryEdges_sameWestEndpoint w hfin htrans hR hL0





















































































end DirectedDistances.PaperProofs.Section4

end
