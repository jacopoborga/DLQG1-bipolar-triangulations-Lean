/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section1.BusemannConvergenceUnconditional

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/










public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory Filter
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Probability
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7
open scoped Topology



theorem thm_busemann_conv_provider :
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
        IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) (identifiedLDPBusemann W)) ∧
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) (identifiedSDPBusemann W)) ∧
    (∃ (a b : ℝ) (μL νL μS νS : ProbabilityMeasure CadlagLocalZero),
      LdpStableHalfLaw a μL ∧ SymmetricStableProcessLaw (2 / 3) a νL ∧
      SdpStableHalfLaw b μS ∧ SymmetricStableProcessLaw (4 / 3) b νS ∧
      Tendsto identifiedLDPScalingLaw atTop
        (𝓝 ((probabilityProduct μL νL).map wholeLineGlueZero)) ∧
      Tendsto identifiedSDPScalingLaw atTop
        (𝓝 ((probabilityProduct μS νS).map wholeLineGlueZero))) := by
  refine ⟨?_, ?_, thm16_holds⟩
  · filter_upwards [thm_busemann_paper,
      identifiedLDPBusemann_characterization_ae] with W hW hc
    obtain ⟨H, h, hLL, _⟩ := hW
    exact ⟨H, h, hLL, hc H h hLL⟩
  · filter_upwards [thm_busemann_paper,
      identifiedSDPBusemann_characterization_ae] with W hW hc
    obtain ⟨H, h, hLL, _⟩ := hW
    exact ⟨H, h, hLL, hc H h hLL⟩

end DirectedDistances.PaperProofs.SourceResults
