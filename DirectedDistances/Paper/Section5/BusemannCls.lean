 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.BusemannCls

/-!
# Lemma 5.7 (`lem-busemann-cls`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/























public section
namespace DirectedDistances.Paper.Section5

open MeasureTheory Quiver DirectedDistances.KMSW
open DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section5.Xdp



theorem busemann_cls :
    ∀ᵐ W ∂RandomWalk.wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      let w := shiftedStream W 0
      let V := wholePlaneVertexι W 0
      let E := wholePlaneEdgeι W 0
      let D := m0CutData W H h hLL
      (Function.Injective V ∧
      Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
      Function.Injective E ∧
      Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
      (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
      ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
        (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
        wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
        wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
        wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
      (∀ e, EdgePresent w e ↔
        (wholePlaneEdgePresent W (E e) ∧
          ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
      (∀ e, (D).missing (E e) ↔
        ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
      (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
        ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
      (∀ a b, (D).sdp (V a) (V b) =
        DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ k k', (D).sdp ((D).x k) ((D).x k') =
        DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
      (∀ k k', (D).ldp ((D).x k) ((D).x k') =
        presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
      ∀ longest : Bool,
      ∃ R : ℤ → KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
        (∀ k, (R k).vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
          (T k).edge = (R k).edge ∧
          (∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
            ((T k).initial n).1.id ((T k).edge n))) ∧
        (∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        (∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL longest k Q (T k) → Q = P k) ∧
        (∃! X : ℤ → ℤ, if longest then
          IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X else
          IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X) ∧
        (∀ k : ℤ, ∃! q : ℕ × ℕ,
          M0CutLeastEdgeCoalescence (P k) (P (k - 1)) q.1 q.2) ∧
        ∀ X : ℤ → ℤ,
          (if longest then IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X
            else IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X) →
          ∀ (k : ℤ) (theta theta' : ℕ),
            M0CutLeastEdgeCoalescence (P k) (P (k - 1)) theta theta' →
            X k - X (k - 1) = (theta : ℤ) - (theta' : ℤ) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.busemann_cls_provider
 
 

end DirectedDistances.Paper.Section5
 
