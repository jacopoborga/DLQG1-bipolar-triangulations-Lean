module

public import DirectedDistances.KMSW.RunRightBoundaryChain
public import DirectedDistances.KMSW.RunRightmostRayExists
public import DirectedDistances.KMSW.WholePlaneRightmostRays
public import DirectedDistances.KMSW.M0CutRootTransport

/-! Supporting lemmas for paper labels `lem-uibot-bdy` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.KMSW





theorem kmswRunRightmostRay_tied_to_ambient
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0))
    (hR : R.vertex 0 = boundaryVertex (shiftedStream W 0) h 1)
    (P : WholePlaneRightmostRay W H)
    (hP : P.vertex 0 = wholePlaneEdgeEast W (m0CutLambdaZero W)) :
    ∀ i, wholePlaneVertexι W 0 (R.vertex i) = P.vertex i ∧
      wholePlaneEdgeι W 0 (R.edge i) = P.edge i := by
  let w := shiftedStream W 0
  let B := kmswRunRightBoundaryRay w (H.1 0) h
  obtain ⟨v, e, hv0, he, hs⟩ := wholePlaneRightBoundary_rightmost_chain W H 0 h
  let Q : WholePlaneRightmostRay W H := {
    vertex := v
    edge := e
    rightmost := fun j => (hs j).1
    target := fun j => (hs j).2
  }
  have hvertex (i : ℕ) : v i = wholePlaneVertexι W 0
      (boundaryVertex w h ((i : ℤ) + 1)) := by
    induction i with
    | zero =>
        simpa [boundaryVertex_one] using hv0
    | succ i ih =>
        have hp := boundaryVertex_right_edge_present_source w h (k := i + 1) (by omega)
        calc
          v (i + 1) = wholePlaneEdgeEast W (e i) := (hs i).2.symm
          _ = wholePlaneEdgeEast W
              (wholePlaneEdgeι W 0 (kmswRightBoundaryEdge w (i + 1))) := by rw [he i]
          _ = wholePlaneVertexι W 0
              (edgeEast w (kmswRightBoundaryEdge w (i + 1))) := by
                rw [wholePlaneEdgeEast_ι]
          _ = wholePlaneVertexι W 0
              (boundaryVertex w h (((i + 1 : ℕ) : ℤ) + 1)) := by rw [hp.2.2]
  have hroot : wholePlaneEdgeEast W (m0CutLambdaZero W) =
      wholePlaneVertexι W 0 1 := by
    simpa [boundaryVertex_one] using (m0Cut_lambdaZero_endpoints W h).2
  have hPQ : P.vertex 0 = Q.vertex 0 := hP.trans (hroot.trans hv0.symm)
  have hPQs := wholePlaneRightmostRays_coalesce_of_common_vertex P Q 0 0 hPQ
  have hPQv (i : ℕ) : P.vertex i = Q.vertex i := by
    simpa only [Nat.zero_add] using hPQs i
  have hPQe (i : ℕ) : P.edge i = Q.edge i :=
    wholePlaneRightmostOutgoingAt_unique W H (P.vertex i) (P.rightmost i)
      (by rw [hPQv i]; exact Q.rightmost i)
  have hRB0 : R.vertex 0 = B.vertex 0 := by
    simpa [B, kmswRunRightBoundaryRay] using hR
  have hRBs := kmswRunRightmostRays_agree_after_common_vertex R B 0 0 hRB0
  have hRBv (i : ℕ) : R.vertex i = B.vertex i := by
    simpa only [Nat.zero_add] using hRBs i
  have hRBe (i : ℕ) : R.edge i = B.edge i :=
    kmswRunRightmostOutAt_unique w (H.1 0) (R.vertex i) (R.rightmost i)
      (by rw [hRBv i]; exact B.rightmost i)
  intro i
  constructor
  · calc
      wholePlaneVertexι W 0 (R.vertex i) = wholePlaneVertexι W 0 (B.vertex i) :=
        congrArg (wholePlaneVertexι W 0) (hRBv i)
      _ = Q.vertex i := by
        change wholePlaneVertexι W 0
          (boundaryVertex w h ((i : ℤ) + 1)) = v i
        rw [← hvertex i]
      _ = P.vertex i := (hPQv i).symm
  · calc
      wholePlaneEdgeι W 0 (R.edge i) = wholePlaneEdgeι W 0 (B.edge i) :=
        congrArg (wholePlaneEdgeι W 0) (hRBe i)
      _ = Q.edge i := by
        change wholePlaneEdgeι W 0 (kmswRightBoundaryEdge w (i + 1)) = e i
        exact (he i).symm
      _ = P.edge i := (hPQe i).symm

end DirectedDistances.KMSW
