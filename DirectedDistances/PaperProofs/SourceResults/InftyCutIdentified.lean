/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.InftyCutIdentified

/-! # Isolated proof provider for Lemma 5.3 (lem-infty-cut)

Packaging only: the theorem type is exactly the identified helper's type and the proof
forwards to that helper; installation, sealing and counting are separate gates.


Reading: one whole-plane probability-one event under
`RandomWalk.wholePlaneIIDCodeMeasure` before all k < k', l and endpoint sequences,
as in reading (i) of Q-53-scope. The same H, h and hLL witnesses retain the complete
identification of vertices, edges, root, boundary, directed steps, and SDP and LDP distances.
For each k < k', v is chosen before l and the endpoint sequence; every directed cut path
to each sufficiently late endpoint visits each prescribed v m. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory Quiver DirectedDistances.KMSW
open DirectedDistances.RandomWalk



theorem lem_infty_cut_provider :
    ∀ᵐ W ∂RandomWalk.wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
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
      ∀ k k' : ℤ, k < k' →
        ∃ v : ℕ → WholePlaneVertex W,
          Function.Injective v ∧
          (∀ m, v m ∈ m0CutLeftVertices W H D.seam) ∧
          ∀ ell : ℤ, ell ∈ Set.Icc k k' →
            ∀ y : ℕ → WholePlaneVertex W,
              Function.Injective y →
              (∀ j, m0CutReachable W H D.seam (D.x ell) (y j)) →
              ∀ m, ∃ J, ∀ j, J ≤ j →
                ∀ n : ℕ, ∀ p : Fin (n + 1) → WholePlaneVertex W,
                  p 0 = D.x ell →
                  p (Fin.last n) = y j →
                  (∀ i : Fin n,
                    m0CutDirectedStep W H D.seam
                      (p i.castSucc) (p i.succ)) →
                  ∃ i, p i = v m := by
  exact DirectedDistances.PaperProofs.Section5.lem_infty_cut_identified

end DirectedDistances.PaperProofs.SourceResults
