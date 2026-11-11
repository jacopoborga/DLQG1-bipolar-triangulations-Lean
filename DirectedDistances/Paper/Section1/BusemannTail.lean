 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.BusemannPropertyTail

/-!
# Theorem 1.8 (`thm-busemann-tail`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/
















public section
namespace DirectedDistances.Paper.Section1

open MeasureTheory ProbabilityTheory Filter Asymptotics
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7

 
theorem thm_busemann_tail :
    (
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) (identifiedLDPBusemann W)) ∧
    ∃ c : ℝ, 0 < c ∧
      ((fun x : ℝ => wholePlaneIIDCodeMeasure.real
        {W | ((identifiedLDPBusemann W 1 - identifiedLDPBusemann W 0 : ℤ) : ℝ) ≤ -x} -
          c * x ^ (-(2 / 3 : ℝ))) =o[atTop]
            (fun x : ℝ => x ^ (-(2 / 3 : ℝ)))) ∧
      ((fun x : ℝ => wholePlaneIIDCodeMeasure.real
        {W | x ≤ |((identifiedLDPBusemann W 0 -
          identifiedLDPBusemann W (-1) : ℤ) : ℝ)|} -
            2 * c * x ^ (-(2 / 3 : ℝ))) =o[atTop]
              (fun x : ℝ => x ^ (-(2 / 3 : ℝ))))) ∧
    (
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) (identifiedSDPBusemann W)) ∧
    (∃ c : ℝ, 0 < c ∧
      ((fun x : ℝ => wholePlaneIIDCodeMeasure.real
        {W | x ≤ ((identifiedSDPBusemann W 1 - identifiedSDPBusemann W 0 : ℤ) : ℝ)} -
          c * x ^ (-(4 / 3 : ℝ))) =o[atTop]
            (fun x : ℝ => x ^ (-(4 / 3 : ℝ)))) ∧
      ((fun x : ℝ => wholePlaneIIDCodeMeasure.real
        {W | x ≤ |((identifiedSDPBusemann W 0 -
          identifiedSDPBusemann W (-1) : ℤ) : ℝ)|} -
            2 * c * x ^ (-(4 / 3 : ℝ))) =o[atTop]
              (fun x : ℝ => x ^ (-(4 / 3 : ℝ))))) ∧
    ∀ k : ℤ,
      Integrable (fun W => ((identifiedSDPBusemann W k -
        identifiedSDPBusemann W (k - 1) : ℤ) : ℝ)) wholePlaneIIDCodeMeasure ∧
        (∫ W, ((identifiedSDPBusemann W k -
          identifiedSDPBusemann W (k - 1) : ℤ) : ℝ) ∂wholePlaneIIDCodeMeasure) = 0) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.thm_busemann_tail_provider
 
 

end DirectedDistances.Paper.Section1
 
