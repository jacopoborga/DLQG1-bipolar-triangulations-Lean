 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.Section7Identified

/-!
# Lemma 7.5 (`lem-sdp-tri`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/














public section
namespace DirectedDistances.Paper.Section7

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7

 
theorem lem_sdp_tri :
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
          X l - X k ≤ ((D.sdp (D.x l) (D.x k)).toNat : ℤ) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.lem_sdp_tri_provider
 
 

end DirectedDistances.Paper.Section7
 
