/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section7.SDPTriIdentified
public import DirectedDistances.PaperProofs.Section7.LDPFluctuationPaper

/- # Isolated proof providers for Lemmas 7.3 and 7.5 on the identified future map M_{0,infinity}

forwards to a proved helper; installation, sealing and counting are separate gates.


Reading: on one whole-plane probability-one event under
`RandomWalk.wholePlaneIIDCodeMeasure`, the cut data `m0CutData` identifies the rooted
future map M_{0,infinity}, its labels, edges, status and distances. Lemma 7.5 retains this
identification and the unique identified SDP Busemann function, and gives reachability,
finite SDP and the inequality simultaneously for every `0 <= l < k`. Lemma 7.3 uses
`identifiedLDPBusemann`, with its proved almost-sure identified LDP characterization.
One constant works for every `k >= 1` as printed and every `A > 1`, over the full integer
window `[-k, k]`; the helper's `k = 0` extension is not used. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7

/-- packaging only. -/
theorem lem_sdp_tri_provider :
    ∀ᵐ W ∂RandomWalk.wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
      let w := shiftedStream W 0
      let V := wholePlaneVertexι W 0
      let E := wholePlaneEdgeι W 0
      let D := m0CutData W H h hLL
      (Function.Injective V ∧
        Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
        Function.Injective E ∧
        Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
        (∀ j, D.x j = V (boundaryVertex w h j)) ∧
        (D.rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
          D.rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
          wholePlaneEdgeWest W D.rootDart.1 = D.x 0 ∧
          wholePlaneEdgeEast W D.rootDart.1 = D.x 1 ∧
          wholePlaneEdgePresent W D.rootDart.1 ∧ D.tail D.rootDart) ∧
        (∀ e, EdgePresent w e ↔
          (wholePlaneEdgePresent W (E e) ∧
            ¬ ∃ j : ℤ, j ≤ -1 ∧ e = boundaryOuterEdge w h j)) ∧
        (∀ e, D.missing (E e) ↔
          ∃ j : ℤ, j ≤ -1 ∧ e = boundaryOuterEdge w h j) ∧
        (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
          ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧
            V (edgeEast w e) = V b) ∧
        (∀ a b, D.sdp (V a) (V b) =
          DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
        (∀ a b, D.ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
        (∀ j j', D.sdp (D.x j) (D.x j') =
          DirectedDistances.sdp (boundaryPresentVertex w h j)
            (boundaryPresentVertex w h j')) ∧
        (∀ j j', D.ldp (D.x j) (D.x j') =
          presentLdp (boundaryPresentVertex w h j) (boundaryPresentVertex w h j'))) ∧
      (∃! X : ℤ → ℤ, IsIdentifiedM0BusemannSDP D X) ∧
      ∀ X : ℤ → ℤ, IsIdentifiedM0BusemannSDP D X →
        ∀ l k : ℤ, 0 ≤ l → l < k →
          m0CutReachable W H D.seam (D.x l) (D.x k) ∧
          D.sdp (D.x l) (D.x k) ≠ ⊤ ∧
          X l - X k ≤ ((D.sdp (D.x l) (D.x k)).toNat : ℤ) := by
  exact DirectedDistances.PaperProofs.Section7.sdp_tri_identified_ae

/-- packaging only. -/
theorem lem_ldp_fluctuation_provider :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, 1 < A →
      1 - C * A ^ (-(2 / 3 : ℝ)) ≤
        wholePlaneIIDCodeMeasure.real {W | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
          |(identifiedLDPBusemann W l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)} := by
  exact DirectedDistances.PaperProofs.Section7.lem_ldp_fluctuation_paper

end DirectedDistances.PaperProofs.SourceResults
