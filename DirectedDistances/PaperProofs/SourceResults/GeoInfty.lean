/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyCutLeftmostXdp
import DirectedDistances.KMSW.M0CutIdentificationPackaged

/-! Supporting lemmas for paper labels `lem-geo-infty` (see CORRESPONDENCE.md). -/

/-! # Isolated proof provider for Lemma 5.4 (lem-geo-infty)


The glued drawing `WholePlanePastGlueDrawing.glueDrawing W h hp H` is the
representative of the two-sided map used by `CutLeftmostXdp`. The same witnesses
identify the cut vertices, geometric edges, boundary labels, root, presence,
missing edges, directed steps, and extended SDP and LDP distances.

The mode `true` states LDP; `false` states SDP separately. The SDP companion is
proved in the imported helper, as required by both-mode scope, rather than assumed from the
literal LDP-only Lemma 4.6. Source edges are indexed from 1; Lean streams start
at 0. Coalescence retains geometric edge identities, including parallel edges.
and counting remain the coordinator's responsibility. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory Quiver DirectedDistances.KMSW
open DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section5.Xdp



theorem geo_infty_provider :
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
        (∀ k, CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        (∀ k Q, CutLeftmostXdp W H h hp hLL longest k Q (T k) → Q = P k) ∧
        ∀ k k' : ℤ, ∃ i j : ℕ, ∀ n : ℕ,
          wholePlaneEdgeι W 0 ((P k).codePath.edge (i + n)) =
            wholePlaneEdgeι W 0 ((P k').codePath.edge (j + n)) := by
  filter_upwards [m0Cut_ae_leftmost_xdp_and_pairwise_coalescence] with W hW
  obtain ⟨H, h, hLL, hp, hpaths⟩ := hW
  exact ⟨H, h, hLL, hp, m0Cut_identification W H h hLL, hpaths⟩

end DirectedDistances.PaperProofs.SourceResults
