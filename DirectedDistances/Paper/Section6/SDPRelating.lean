 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.SDPRelating

/-!
# Lemma 6.10 (`lem:SDP-relating-X1-X`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/















public section
namespace DirectedDistances.Paper.Section6

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7

 
theorem lem_sdp_relating :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      let W1 : ℤ → Fin 3 := fun i => W (i + 1)
      let X := identifiedSDPBusemann W
      let X1 := identifiedSDPBusemann W1
      (∃ H : WholePlaneRotationHypothesis W,
        ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
        ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
          IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X) ∧
      (∃ H : WholePlaneRotationHypothesis W1,
        ∃ h : BoundaryHitWitnesses (shiftedStream W1 0),
        ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W1
          (wholePlaneEdgeι W1 0 (kmswLLCreatedEdge (shiftedStream W1 0)
            (boundaryHitTime (shiftedStream W1 0) h (k - 1)))),
          IsIdentifiedM0BusemannSDP (m0CutData W1 H h hLL) X1) ∧
      (shiftedStream W 0 0 = 2 →
        (X (-1), X 1) = (X1 (-2) - min (X1 (-1)) 1, -min (X1 (-1)) 1)) ∧
      (shiftedStream W 0 0 = 0 → (X (-1), X 1) = (-X1 1 - 1, -1)) ∧
      (shiftedStream W 0 0 = 1 →
        (X (-1), X 1) =
          (X1 (-1) - min 0 (X1 2 + 1), X1 2 - min 0 (X1 2 + 1))) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.lem_sdp_relating_provider
 
 

end DirectedDistances.Paper.Section6
 
