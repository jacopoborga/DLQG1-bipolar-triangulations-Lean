 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.DirectedContain

/-!
# Lemma 5.2 (`lem-directed-contain`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/
















public section
namespace DirectedDistances.Paper.Section5

open MeasureTheory Quiver DirectedDistances.KMSW
open DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section5

 
theorem directed_contain :
    ∀ᵐ W ∂RandomWalk.wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∀ k : ℤ,
        wholePlaneIIDCodeMeasure.map (boundaryFutureCode k) =
          wholePlaneIIDCodeMeasure.map (boundaryFutureCode 0) ∧
        wholePlaneIIDCodeMeasure.map (hatLawCodes ∘ boundaryFutureCode k) =
          iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) ∧
        (fun i => boundaryFutureCode k W (i + 1)) =
          (fun i => shiftedStream W 0 (boundaryHitTime (shiftedStream W 0) h k + i)) ∧
        (∃ hτ : HasFlowLineHits
            (fun i => shiftedStream W 0 (boundaryHitTime (shiftedStream W 0) h k + i)),
          hatLawCodes (boundaryFutureCode k W) =
            hatCodes (fun i => shiftedStream W 0
              (boundaryHitTime (shiftedStream W 0) h k + i)) hτ) ∧
        M0CutShiftContainment W H h hLL k ∧
        boundaryFutureRootedMapClause W h k :=
 
by exact DirectedDistances.PaperProofs.SourceResults.directed_contain_provider
 
 

end DirectedDistances.Paper.Section5
 
