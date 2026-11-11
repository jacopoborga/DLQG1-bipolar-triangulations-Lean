module

public import DirectedDistances.KMSW.M0CutSeam
public import DirectedDistances.KMSW.M0CutLeftSide

public section
namespace DirectedDistances.KMSW

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: the left side of the cut is the run-zero map); not a paper result.
The seam-defined geometric edge set equals the run-zero map, given presence
of the left boundary edges in the whole-plane map. -/
theorem m0Cut_leftEdges_seam_eq_runZero (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))) :
    m0CutLeftEdges W H (m0CutSeamEdge W H) = Set.range (wholePlaneEdgeι W 0) := by
  apply m0Cut_leftEdges_eq_runZero W H h (m0CutSeamEdge W H)
  intro e
  exact m0Cut_seamEdge_iff W H h hLL e

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,infinity} identification,
Q-M0-repr: the left side of the cut is the run-zero map); not a paper result.
The seam-defined dart set is the run-zero dart image off the outer boundary,
given presence of the left boundary edges in the whole-plane map. -/
theorem m0Cut_leftDarts_seam_eq_runZero (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))) :
    m0CutLeftDarts W H (m0CutSeamEdge W H) = wholePlaneDartι W 0 ''
      {d | ∀ k : ℤ, d ≠ futureMapBoundaryDart (shiftedStream W 0) h k} := by
  apply m0Cut_leftDarts_eq_runZero W H h (m0CutSeamEdge W H)
  intro e
  exact m0Cut_seamEdge_iff W H h hLL e

end DirectedDistances.KMSW
