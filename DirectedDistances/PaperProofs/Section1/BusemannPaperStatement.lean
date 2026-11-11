/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section1.BusemannM0Identified
public import DirectedDistances.KMSW.M0CutLabelsOrder

public section
namespace DirectedDistances.PaperProofs.Section1

open MeasureTheory DirectedDistances.KMSW

/-- Helper toward Theorem 1.4 (thm-busemann; paper-side statement on the identified future map
M_{0,infinity}); not a paper result.

Theorem `thm-busemann`: "There exists a unique function" called the Busemann function,
normalized at zero, whose difference for each boundary pair equals the corresponding
XDP difference along every common reachable sequence of distinct vertices for all large indices.
Both SDP and LDP hold on one probability-one event. The explicit identification, injective
boundary enumeration, geometric order, root, and reachable-distance finiteness clauses certify
the paper-side carrier and the finite differences in the existing predicates. -/
theorem thm_busemann_paper :
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
        Function.Injective D.x ∧
        Set.range D.x = {v | ∃ e, m0CutSeamEdge W H e ∧
          (wholePlaneEdgeWest W e = v ∨ wholePlaneEdgeEast W e = v)} ∧
        (∀ k : ℤ,
          m0CutSeamEdge W H
              (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) ∧
          wholePlaneEdgeWest W
              (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) = D.x k ∧
          wholePlaneEdgeEast W
              (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) =
            D.x (k + 1)) ∧
        (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h 0) =
            m0CutLambdaZero W ∧
          m0CutSeamEdge W H (m0CutLambdaZero W) ∧
          wholePlaneEdgeWest W (m0CutLambdaZero W) = D.x 0 ∧
          wholePlaneEdgeEast W (m0CutLambdaZero W) = D.x 1) ∧
        (∀ a b : WholePlaneVertex W, m0CutReachable W H D.seam a b → D.sdp a b ≠ ⊤) ∧
        (∀ a b : WholePlaneVertex W, m0CutReachable W H D.seam a b →
          ∃ n : ℕ, D.ldp a b = ((n : ℕ∞) : WithBot ℕ∞)) ∧
        (∃! X : ℤ → ℤ, IsIdentifiedM0BusemannSDP D X) ∧
        (∃! X : ℤ → ℤ, IsIdentifiedM0BusemannLDP D X) := by
  filter_upwards [m0Cut_busemann_identified_ae] with W hW
  obtain ⟨H, h, hLL, hid, hsdp, hldp⟩ := hW
  exact ⟨H, h, hLL, hid,
    m0CutData_x_injective W H h hLL,
    m0CutData_x_range W H h hLL,
    m0CutData_x_order W H h hLL,
    m0CutData_x_root W H h hLL,
    m0CutData_sdp_ne_top_of_reachable W H h hLL,
    m0CutData_ldp_eq_finite_of_reachable W H h hLL,
    hsdp, hldp⟩

end DirectedDistances.PaperProofs.Section1
