 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.BusemannPropertyTail

/-!
# Theorem 1.7 (`thm-busemann-property`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/
















public section
namespace DirectedDistances.Paper.Section1

open MeasureTheory ProbabilityTheory Filter Asymptotics
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7

 
theorem thm_busemann_property :
    (
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) (identifiedLDPBusemann W)) ∧
    iIndepFun (fun k W => identifiedLDPBusemann W k - identifiedLDPBusemann W (k - 1))
      wholePlaneIIDCodeMeasure ∧
    (∀ k : ℤ, 1 ≤ k → IdentDistrib
      (fun W => identifiedLDPBusemann W k - identifiedLDPBusemann W (k - 1))
      (fun W => identifiedLDPBusemann W 1 - identifiedLDPBusemann W (1 - 1))
      wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun W => identifiedLDPBusemann W k - identifiedLDPBusemann W (k - 1))
      (fun W => identifiedLDPBusemann W 0 - identifiedLDPBusemann W (0 - 1))
      wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure) ∧
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ k : ℤ, 1 ≤ k →
      identifiedLDPBusemann W k - identifiedLDPBusemann W (k - 1) ≤ -1) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun W => identifiedLDPBusemann W k - identifiedLDPBusemann W (k - 1))
      (fun W => identifiedLDPBusemann W (k - 1) - identifiedLDPBusemann W k)
      wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure)) ∧
    (
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) (identifiedSDPBusemann W)) ∧
    iIndepFun (fun k W => identifiedSDPBusemann W k - identifiedSDPBusemann W (k - 1))
      wholePlaneIIDCodeMeasure ∧
    (∀ k : ℤ, 1 ≤ k → IdentDistrib
      (fun W => identifiedSDPBusemann W k - identifiedSDPBusemann W (k - 1))
      (fun W => identifiedSDPBusemann W 1 - identifiedSDPBusemann W (1 - 1))
      wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun W => identifiedSDPBusemann W k - identifiedSDPBusemann W (k - 1))
      (fun W => identifiedSDPBusemann W 0 - identifiedSDPBusemann W (0 - 1))
      wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure) ∧
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ k : ℤ, 1 ≤ k →
      -1 ≤ identifiedSDPBusemann W k - identifiedSDPBusemann W (k - 1)) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun W => identifiedSDPBusemann W k - identifiedSDPBusemann W (k - 1))
      (fun W => identifiedSDPBusemann W (k - 1) - identifiedSDPBusemann W k)
      wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure)) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.thm_busemann_property_provider
 
 

end DirectedDistances.Paper.Section1
 
