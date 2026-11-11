/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section7.LDPFluctuationLinked

/- # Isolated proof provider for Lemma 7.3 with the identified LDP Busemann selector

forwards to a proved helper; installation, sealing and counting are separate gates.


Reading: on one whole-plane probability-one event under
`RandomWalk.wholePlaneIIDCodeMeasure`, the selector `identifiedLDPBusemann` is the
identified LDP Busemann function for the cut data `m0CutData` of Theorem 1.4.
One constant works for every `k >= 1` as printed and every `A > 1`, over the full integer
window `[-k, k]`; the helper's `k = 0` extension is not used. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7

/-- packaging only. -/
theorem lem_ldp_fluctuation_linked_provider :
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
  exact DirectedDistances.PaperProofs.Section7.lem_ldp_fluctuation_linked

end DirectedDistances.PaperProofs.SourceResults
