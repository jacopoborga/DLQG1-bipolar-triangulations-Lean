module

public import DirectedDistances.KMSW.KMSWWholePlaneFaces
public import DirectedDistances.KMSW.M0CutRootTransport
public import DirectedDistances.KMSW.M0CutEdgeTransport
public import DirectedDistances.KMSW.WholePlaneRootedMapFields

public section
namespace DirectedDistances.KMSW

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Source:
The whole-plane rotation agrees with the run-zero rotation when the dart's
base endpoint remains fresh at every later transition. -/
theorem m0Cut_rotation_runZero_of_fresh (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (d : ℕ × Bool)
    (hf : ∀ M (h0M : 0 ≤ M), wholePlaneFresh W 0 M h0M
      (if d.2 then edgeEast (shiftedStream W 0) d.1
        else edgeWest (shiftedStream W 0) d.1)) :
    wholePlaneRotation W H (wholePlaneDartι W 0 d) =
      wholePlaneDartι W 0 (kmswInfRot (shiftedStream W 0) (H.1 0) d) :=
  wholePlaneRotation_ι_of_fresh W H 0 d hf








theorem m0Cut_faceSucc_runZero_of_fresh (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (d : ℕ × Bool)
    (hf : ∀ M (h0M : 0 ≤ M), wholePlaneFresh W 0 M h0M
      (if !d.2 then edgeEast (shiftedStream W 0) d.1
        else edgeWest (shiftedStream W 0) d.1)) :
    wholePlaneFaceSucc W H (wholePlaneDartι W 0 d) =
      wholePlaneDartι W 0
        (kmswInfFaceSucc (shiftedStream W 0) (H.1 0) d) :=
  wholePlaneFaceSucc_ι_of_fresh W H 0 d hf








theorem m0Cut_missing_leftBoundary_faceSucc (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ) (hk : k ≤ -1)
    (hm : ¬ wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k))) :
    ¬ wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h (k - 1))) ∧
      wholePlaneFaceSucc W H
          (wholePlaneDartι W 0 (futureMapBoundaryDart (shiftedStream W 0) h k)) =
        wholePlaneDartι W 0
          (futureMapBoundaryDart (shiftedStream W 0) h (k - 1)) :=
  wholePlane_missing_boundary_faceSucc W H 0 h k hk hm

end DirectedDistances.KMSW
