/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftySideReader

/-! This assembles the nonnegative-index right-side reader with the code-level
independence and law results. The law is stated on the existing measurable
`RPlusSidePresentation` space. Independence below is from the left code
observation only; no geometric left-side presentation is available here. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section4

/-- Helper toward Lemma 5.5: decoding the nonnegative right code into its
existing measurable presentation space preserves its index-invariant law. -/
theorem rightSidePresentation_law_eq_zero (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    wholePlaneIIDCodeMeasure.map
        (fun W => decodeRPlus x k (rightSideObsNonneg x k W)) =
      wholePlaneIIDCodeMeasure.map
        (fun W => decodeRPlus x 0 (rightSideObsNonneg x 0 W)) := by
  have hobs (j : ℤ) :
      AEMeasurable (rightSideObsNonneg x j) wholePlaneIIDCodeMeasure := by
    change AEMeasurable (boundaryFourObservations x j 2)
      wholePlaneIIDCodeMeasure
    exact aemeasurable_boundaryFourObservations x j 2
  change wholePlaneIIDCodeMeasure.map
      (decodeRPlus x k ∘ rightSideObsNonneg x k) =
    wholePlaneIIDCodeMeasure.map
      (decodeRPlus x 0 ∘ rightSideObsNonneg x 0)
  rw [← AEMeasurable.map_map_of_aemeasurable
        (measurable_decodeRPlus x k).aemeasurable
        (hobs k),
    ← AEMeasurable.map_map_of_aemeasurable
        (measurable_decodeRPlus x 0).aemeasurable
        (hobs 0),
    rightSideObsNonneg_law_eq_zero x k hk]
  rfl

/-- Helper toward Lemma 5.5: the decoded right presentation is independent
of the left code observation at the same index. This is code-level
independence, without a geometric left-side identification. -/
theorem leftSideObsNonneg_indep_rightSidePresentation (x : XDP) (k : ℤ) :
    IndepFun (leftSideObsNonneg x k)
      (fun W => decodeRPlus x k (rightSideObsNonneg x k W))
      wholePlaneIIDCodeMeasure := by
  exact (leftSideObsNonneg_indep_rightSideObsNonneg x k).comp
    (φ := id) (ψ := decodeRPlus x k) measurable_id
    (measurable_decodeRPlus x k)

/-- Helper toward Lemma 5.5: one full-measure event supplies the existing
simultaneous marked-isomorphism reader for every nonnegative index and both
geodesic modes, while both decoded presentation laws equal their index-zero
law in the existing measurable presentation spaces. The left observation in
the separate independence theorem remains only a code observation. -/
theorem ae_boundaryGluing_nonneg_right_markedIso_decodeRPlus_law_eq_zero :
    (∀ longest : Bool, ∀ k : ℤ, 0 ≤ k →
      wholePlaneIIDCodeMeasure.map
          (fun W => decodeRPlus (if longest then XDP.ldp else XDP.sdp) k
            (rightSideObsNonneg (if longest then XDP.ldp else XDP.sdp) k W)) =
        wholePlaneIIDCodeMeasure.map
          (fun W => decodeRPlus (if longest then XDP.ldp else XDP.sdp) 0
            (rightSideObsNonneg (if longest then XDP.ldp else XDP.sdp) 0 W))) ∧
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      ∀ longest : Bool,
      ∃ R : ℤ → KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
        (∀ k, (R k).vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
          (T k).edge = (R k).edge ∧
          ∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
            ((T k).initial n).1.id ((T k).edge n)) ∧
        (∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        (∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL longest k Q (T k) → Q = P k) ∧
        (∀ k k' : ℤ, ∃ i j : ℕ, ∀ n : ℕ,
          wholePlaneEdgeι W 0 ((P k).codePath.edge (i + n)) =
            wholePlaneEdgeι W 0 ((P k').codePath.edge (j + n))) ∧
        ∀ k : ℤ, 0 ≤ k →
          ∃ hreal : (decodeRPlus (if longest then XDP.ldp else XDP.sdp) k
            (rightSideObsNonneg (if longest then XDP.ldp else XDP.sdp) k W)).realization.isSome,
          Nonempty (GeometricSideMarkedIso
            (m0GeodesicSide hp (P k) .right)
            ((decodeRPlus (if longest then XDP.ldp else XDP.sdp) k
              (rightSideObsNonneg (if longest then XDP.ldp else XDP.sdp) k W)).realization.get
              hreal))) := by
  refine ⟨?_, ae_boundaryGluing_nonneg_right_markedIso_decodeRPlus⟩
  intro longest k hk
  exact rightSidePresentation_law_eq_zero
    (if longest then XDP.ldp else XDP.sdp) k hk

end DirectedDistances.PaperProofs.Section5
