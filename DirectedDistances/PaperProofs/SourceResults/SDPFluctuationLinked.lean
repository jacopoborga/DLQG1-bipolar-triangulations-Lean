/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section7.SDPFluctuationLinked

/- # Isolated proof provider for Lemma 7.7 with the identified SDP Busemann selector

forwards to a proved helper; installation, sealing and counting are separate gates.


Reading: on one whole-plane probability-one event under
`RandomWalk.wholePlaneIIDCodeMeasure`, the selector `identifiedSDPBusemann` is the
identified SDP Busemann function for the cut data `m0CutData` of Theorem 1.4.
For every `delta > 0`, one threshold `A0 > 1` works for every `k >= 1` as printed
and every `A >= A0`, over the full integer window `[-k, k]`. The convention that -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7

/-- packaging only. -/
theorem lem_sdp_fluctuation_linked_provider :
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
            |(identifiedSDPBusemann W l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 4 : ℝ)} := by
  exact DirectedDistances.PaperProofs.Section7.lem_sdp_fluctuation_linked

end DirectedDistances.PaperProofs.SourceResults
