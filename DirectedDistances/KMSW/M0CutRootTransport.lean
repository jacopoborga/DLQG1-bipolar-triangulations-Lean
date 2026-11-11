module

public import DirectedDistances.KMSW.KMSWFutureMapCarrier
public import DirectedDistances.KMSW.KMSWWholePlaneColimit
public import DirectedDistances.KMSW.KMSWWholePlaneFaces
public import DirectedDistances.KMSW.WholePlaneLeftBoundaryMissing
public import DirectedDistances.KMSW.WholePlaneRootedMapFields
public import DirectedDistances.KMSW.DirectedContain

/-! Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Sources:
This file proves only run-zero root transport, not the cut identification. -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. The run-zero representative
of the whole-plane root edge used by `wholePlaneRootEdge_present`. -/
@[expose] def m0CutLambdaZero (W : ℤ → Fin 3) : WholePlaneEdge W :=
  wholePlaneEdgeι W 0 0

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. The run-zero initial edge
maps to the run-zero representative of λ₀. -/
theorem m0Cut_runZero_initialEdge_maps_to_lambdaZero (W : ℤ → Fin 3) :
    wholePlaneEdgeι W 0 futureMapRootDart.1 = m0CutLambdaZero W := rfl

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. The west and east endpoints
of λ₀ are the run-zero images of boundary vertices x₀ and x₁, respectively. -/
theorem m0Cut_lambdaZero_endpoints (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (shiftedStream W 0)) :
    wholePlaneEdgeWest W (m0CutLambdaZero W) =
        wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h 0) ∧
      wholePlaneEdgeEast W (m0CutLambdaZero W) =
        wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h 1) := by
  have hr := futureMap_root_endpoints (shiftedStream W 0)
  have hw : edgeWest (shiftedStream W 0) 0 = 0 := by
    simpa [futureMapRootDart, kmswLimitDartVertex] using hr.1
  have he : edgeEast (shiftedStream W 0) 0 = 1 := by
    simpa [futureMapRootDart, futureMapEdgeInv, kmswLimitDartVertex] using hr.2
  constructor
  · rw [m0CutLambdaZero, wholePlaneEdgeWest_ι, boundaryVertex_zero, hw]
  · rw [m0CutLambdaZero, wholePlaneEdgeEast_ι, boundaryVertex_one, he]

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. The root edge is present in
both carriers, and each carrier's west dart is its directed tail. -/
theorem m0Cut_lambdaZero_present_orientation (W : ℤ → Fin 3) :
    EdgePresent (shiftedStream W 0) futureMapRootDart.1 ∧
      wholePlaneEdgePresent W (m0CutLambdaZero W) ∧
      futureMapTail (shiftedStream W 0) futureMapRootDart ∧
      wholePlaneDartTail W (m0CutLambdaZero W, false) := by
  refine ⟨futureMap_root_present (shiftedStream W 0), ?_, ?_, ?_⟩
  · simpa [m0CutLambdaZero] using wholePlaneRootEdge_present W 0
  · exact ⟨rfl, futureMap_root_present (shiftedStream W 0)⟩
  · exact ⟨by simp, by simpa [m0CutLambdaZero] using wholePlaneRootEdge_present W 0⟩

end DirectedDistances.KMSW
