module

public import DirectedDistances.KMSW.M0CutIdentificationPackaged
public import DirectedDistances.KMSW.M0CutLLPresenceAE
public import DirectedDistances.KMSW.WholePlaneLeftmostIncomingAmbient

public section
namespace DirectedDistances.KMSW

open MeasureTheory

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: almost-sure packaged identification); not a paper result.
Almost surely the run-zero witnesses identify the rooted directed carrier, boundary
labels, present and missing edges, directed steps, and all stated extended distances. -/
theorem m0Cut_identification_ae :
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
        Function.Injective V ∧
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
          presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) := by
  apply wholePlaneIID_ae_leftBoundary_leftmost_chain.mono
  intro W hW
  obtain ⟨H, hRuns⟩ := hW
  obtain ⟨h, hLL, _⟩ := hRuns 0
  exact ⟨H, h, hLL, m0Cut_identification W H h hLL⟩

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: almost-sure packaged identification); not a paper result.
On one probability-one event the full identification holds for every rotation
hypothesis and boundary-hit witness, with its lower-left presence proof. -/
theorem m0Cut_identification_ae_all :
    ∀ᵐ W ∂RandomWalk.wholePlaneIIDCodeMeasure,
      ∀ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0)),
        ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0
            (kmswLLCreatedEdge (shiftedStream W 0)
              (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        let w := shiftedStream W 0
        let V := wholePlaneVertexι W 0
        let E := wholePlaneEdgeι W 0
        let D := m0CutData W H h hLL
        Function.Injective V ∧
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
          presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) := by
  apply m0Cut_llPresence_ae.mono
  intro W hpresence H h
  exact ⟨hpresence h, m0Cut_identification W H h (hpresence h)⟩

end DirectedDistances.KMSW
