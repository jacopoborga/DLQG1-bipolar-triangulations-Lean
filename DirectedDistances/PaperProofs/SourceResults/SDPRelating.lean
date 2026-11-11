/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section6.SDPRelatingIdentified

/-! # Isolated proof provider for Lemma 6.10 (lem:SDP-relating-X1-X)

The relations hold on the identified maps M_{0,infinity} and M_{1,infinity}.
Packaging only: the theorem type is exactly the identified helper's type and the proof
forwards to that helper; installation, sealing and counting are separate gates.


Reading: on one whole-plane probability-one event under
`RandomWalk.wholePlaneIIDCodeMeasure`, X and X^1 are the pinned identified SDP Busemann
functions of the time-zero cuts of W and of `W1 := fun i => W (i + 1)`, respectively.
The latter cut is M_{1,infinity}, the KMSW map of Z restricted to [1,infinity).
The code c is `shiftedStream W 0 0`, the first genuine step Z(1) - Z(0) of M_{0,infinity}.
Codes 0, 1, 2 represent (-1,0), (0,1), (1,-1), respectively. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7

/-- Lemma 6.10 isolated provider (lem:SDP-relating-X1-X, -/
theorem lem_sdp_relating_provider :
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
          (X1 (-1) - min 0 (X1 2 + 1), X1 2 - min 0 (X1 2 + 1))) := by
  exact DirectedDistances.PaperProofs.Section6.lem_sdp_relating_identified

end DirectedDistances.PaperProofs.SourceResults
