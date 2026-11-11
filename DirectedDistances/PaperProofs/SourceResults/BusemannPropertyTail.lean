/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section1.BusemannPropertyIdentified
public import DirectedDistances.PaperProofs.Section1.BusemannTailIdentified

/- # Isolated proof providers for Theorems 1.7 and 1.8 on the identified future map M_{0,infinity}

forward to proved helpers; installation, sealing and counting are separate gates.


Reading (Team w369): the first conjunct in each case pins the selector to the Busemann
function almost surely, with existential witnesses `H h hLL`. Item (iii) of Theorem 1.7
holds almost surely simultaneously for all `k >= 1`. Probabilities are `.real` of
null-measurable events under the probability measure `RandomWalk.wholePlaneIIDCodeMeasure`.
Integer-indexed independence is `iIndepFun` of the selector increments themselves.
Theorem 1.8 uses one positive constant per case shared by both displays; SDP mean zero
includes integrability. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory ProbabilityTheory Filter Asymptotics
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7

/-- LDP and SDP cases; packaging only. -/
theorem thm_busemann_property_provider :
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
      wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure)) := by
  exact ⟨DirectedDistances.PaperProofs.Section1.thm_busemann_property_ldp_identified,
    DirectedDistances.PaperProofs.Section1.thm_busemann_property_sdp_identified⟩

/-- items (va) and (vb); packaging only. -/
theorem thm_busemann_tail_provider :
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
          identifiedSDPBusemann W (k - 1) : ℤ) : ℝ) ∂wholePlaneIIDCodeMeasure) = 0) := by
  exact ⟨DirectedDistances.PaperProofs.Section1.thm_busemann_tail_ldp_identified,
    DirectedDistances.PaperProofs.Section1.thm_busemann_tail_sdp_identified⟩

end DirectedDistances.PaperProofs.SourceResults
