/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section7.LDPFluctuationPaper
public import DirectedDistances.PaperProofs.Section1.BusemannPaperStatement

/-! Supporting lemmas for paper labels `lem-ldp-fluctuation` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1




theorem lem_ldp_fluctuation_linked :
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
        IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) (identifiedLDPBusemann W)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, 1 < A →
      1 - C * A ^ (-(2 / 3 : ℝ)) ≤
        wholePlaneIIDCodeMeasure.real {W | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
          |(identifiedLDPBusemann W l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)} := by
  constructor
  · filter_upwards [thm_busemann_paper,
      identifiedLDPBusemann_characterization_ae] with W hW hc
    obtain ⟨H, h, hLL, _⟩ := hW
    exact ⟨H, h, hLL, hc H h hLL⟩
  · exact lem_ldp_fluctuation_paper

end DirectedDistances.PaperProofs.Section7
