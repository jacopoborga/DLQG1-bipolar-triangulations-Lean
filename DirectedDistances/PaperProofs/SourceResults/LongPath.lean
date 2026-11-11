/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section7.LongPathIdentified












public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7

/-- packaging only. -/
theorem lem_long_path_provider :
    ∀ᵐ W ∂RandomWalk.wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      let w := shiftedStream W 0
      let V := wholePlaneVertexι W 0
      let D := m0CutData W H h hLL
      IsIdentifiedM0BusemannLDP D (identifiedLDPBusemann W) ∧
      ∀ ell k : ℕ, 1 ≤ ell → ell < k →
        let n := boundaryHitTime w h (-(k : ℤ))
        ∃ (N : ℕ) (p : Fin (N + 1) → WholePlaneVertex W),
          (∀ i : Fin N, m0CutDirectedStep W H D.seam (p i.castSucc) (p i.succ)) ∧
          IdentifiedStagePath W V n N p ∧
          (max (identifiedLDPBusemann W (-(ell : ℤ)) -
            identifiedLDPBusemann W (-(k : ℤ))) 0).toNat ≤ N := by
  exact DirectedDistances.PaperProofs.Section7.lem_long_path_identified

end DirectedDistances.PaperProofs.SourceResults
