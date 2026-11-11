 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.SDPFluctuationLinked

/-!
# Lemma 7.7 (`lem-sdp-fluctuation`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/
















public section
namespace DirectedDistances.Paper.Section7

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7

 
theorem lem_sdp_fluctuation :
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) (identifiedSDPBusemann W)) ∧
    ∀ delta : ℝ, 0 < delta → ∃ A0 : ℝ, 1 < A0 ∧
      ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, A0 ≤ A →
        1 - delta ≤ wholePlaneIIDCodeMeasure.real {W | ∀ l : ℤ,
          -(k : ℤ) ≤ l → l ≤ k →
            |(identifiedSDPBusemann W l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 4 : ℝ)} :=
 
by exact DirectedDistances.PaperProofs.SourceResults.lem_sdp_fluctuation_linked_provider
 
 

end DirectedDistances.Paper.Section7
 
