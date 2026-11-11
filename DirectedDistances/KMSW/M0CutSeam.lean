module

public import DirectedDistances.KMSW.M0CutRootTransport
public import DirectedDistances.KMSW.WholePlaneRightmostRays
public import DirectedDistances.KMSW.WholePlaneLeftmostIncomingAmbient
public import DirectedDistances.KMSW.WholePlaneLeftmostIncomingExists
public import DirectedDistances.KMSW.BoundaryLabelling

/-! Supporting lemmas for paper labels `thm-busemann` (see CORRESPONDENCE.md). -/

/-! Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Sources: -/

public section
namespace DirectedDistances.KMSW

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Sources:
An incoming leftmost chain, indexed backward from its terminal vertex. -/
structure M0CutLeftmostChain (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (v : WholePlaneVertex W) where
  


  vertex : ℕ → WholePlaneVertex W
  


  edge : ℕ → WholePlaneEdge W
  


  endpoint : vertex 0 = v
  


  leftmost : ∀ i, wholePlaneLeftmostIncomingAt W H (vertex i) (edge i)
  


  westEndpoint : ∀ i, wholePlaneEdgeWest W (edge i) = vertex (i + 1)

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Sources:
Two rightmost rays from the terminal root endpoint have identical sequences. -/
theorem m0Cut_betaR_unique (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (P Q : WholePlaneRightmostRay W H)
    (hP : P.vertex 0 = wholePlaneEdgeEast W (m0CutLambdaZero W))
    (hQ : Q.vertex 0 = wholePlaneEdgeEast W (m0CutLambdaZero W)) :
    P.vertex = Q.vertex ∧ P.edge = Q.edge := by
  have hvertices : ∀ i, P.vertex i = Q.vertex i := by
    intro i
    induction i with
    | zero => exact hP.trans hQ.symm
    | succ i ih =>
      have hedge := wholePlaneRightmostOutgoingAt_unique W H (P.vertex i)
        (P.rightmost i) (by rw [ih]; exact Q.rightmost i)
      calc
        P.vertex (i + 1) = wholePlaneEdgeEast W (P.edge i) := (P.target i).symm
        _ = wholePlaneEdgeEast W (Q.edge i) := congrArg (wholePlaneEdgeEast W) hedge
        _ = Q.vertex (i + 1) := Q.target i
  constructor
  · funext i
    exact hvertices i
  · funext i
    exact wholePlaneRightmostOutgoingAt_unique W H (P.vertex i)
      (P.rightmost i) (by rw [hvertices i]; exact Q.rightmost i)

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Sources:
Every ray from the terminal root endpoint uses the run-zero right-record edges. -/
theorem m0Cut_betaR_edges (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (P : WholePlaneRightmostRay W H)
    (hP : P.vertex 0 = wholePlaneEdgeEast W (m0CutLambdaZero W)) :
    ∀ j, P.edge j = wholePlaneEdgeι W 0
      (kmswRightBoundaryEdge (shiftedStream W 0) (j + 1)) := by
  obtain ⟨Q, hQ, hedge⟩ := wholePlaneRightmostRay_exists_root_terminal W H 0 h
  have hroot : wholePlaneEdgeEast W (m0CutLambdaZero W) =
      wholePlaneVertexι W 0 1 := by
    rw [(m0Cut_lambdaZero_endpoints W h).2, boundaryVertex_one]
  have hQroot : Q.vertex 0 = wholePlaneEdgeEast W (m0CutLambdaZero W) :=
    hQ.trans hroot.symm
  have hsame := m0Cut_betaR_unique W H P Q hP hQroot
  intro j
  rw [hsame.2]
  exact hedge j

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Sources:
A canonical leftmost chain into the initial root endpoint, under the source
left-edge-presence premise of `wholePlaneLeftBoundary_leftmost_chain`. -/
theorem m0Cut_betaL_exists (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))) :
    ∃ P : M0CutLeftmostChain W H (wholePlaneEdgeWest W (m0CutLambdaZero W)),
      ∀ j, P.edge j = wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (-(j : ℤ) - 1))) := by
  obtain ⟨v, e, hv, he, hchain⟩ :=
    wholePlaneLeftBoundary_leftmost_chain W H 0 h hLL
  have hroot : wholePlaneEdgeWest W (m0CutLambdaZero W) =
      wholePlaneVertexι W 0 0 := by
    rw [(m0Cut_lambdaZero_endpoints W h).1, boundaryVertex_zero]
  refine ⟨⟨v, e, hv.trans hroot.symm, fun j => (hchain j).1,
    fun j => (hchain j).2⟩, ?_⟩
  intro j
  exact he j

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Sources:
Two leftmost chains into the initial root endpoint have identical sequences. -/
theorem m0Cut_betaL_unique (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (P Q : M0CutLeftmostChain W H (wholePlaneEdgeWest W (m0CutLambdaZero W))) :
    P.vertex = Q.vertex ∧ P.edge = Q.edge := by
  obtain ⟨R, _⟩ := m0Cut_betaL_exists W H h hLL
  have hvertices : ∀ i, P.vertex i = Q.vertex i := by
    intro i
    induction i with
    | zero =>
      exact (P.endpoint.trans R.endpoint.symm).trans
        (R.endpoint.trans Q.endpoint.symm)
    | succ i ih =>
      have hedge := wholePlaneLeftmostIncomingAt_unique W H (P.vertex i)
        (P.leftmost i) (by rw [ih]; exact Q.leftmost i)
      calc
        P.vertex (i + 1) = wholePlaneEdgeWest W (P.edge i) :=
          (P.westEndpoint i).symm
        _ = wholePlaneEdgeWest W (Q.edge i) := congrArg (wholePlaneEdgeWest W) hedge
        _ = Q.vertex (i + 1) := Q.westEndpoint i
  constructor
  · funext i
    exact hvertices i
  · funext i
    exact wholePlaneLeftmostIncomingAt_unique W H (P.vertex i)
      (P.leftmost i) (by rw [hvertices i]; exact Q.leftmost i)

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Sources:
Every leftmost chain into the initial root endpoint uses the run-zero LL edges. -/
theorem m0Cut_betaL_edges (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (P : M0CutLeftmostChain W H (wholePlaneEdgeWest W (m0CutLambdaZero W))) :
    ∀ j, P.edge j = wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (-(j : ℤ) - 1))) := by
  obtain ⟨Q, hedge⟩ := m0Cut_betaL_exists W H h hLL
  have hsame := m0Cut_betaL_unique W H h hLL P Q
  intro j
  rw [hsame.2]
  exact hedge j

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Sources:
The seam consists of the root and the source rightmost and leftmost paths. -/
@[expose] def m0CutSeamEdge (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (e : WholePlaneEdge W) : Prop :=
  e = m0CutLambdaZero W ∨
    (∃ P : WholePlaneRightmostRay W H,
      P.vertex 0 = wholePlaneEdgeEast W (m0CutLambdaZero W) ∧
        ∃ j, P.edge j = e) ∨
    ∃ P : M0CutLeftmostChain W H (wholePlaneEdgeWest W (m0CutLambdaZero W)),
      ∃ j, P.edge j = e

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Sources:
The source-defined seam edges are exactly the time-zero boundary edge images. -/
theorem m0Cut_seamEdge_iff (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (e : WholePlaneEdge W) :
    m0CutSeamEdge W H e ↔
      e ∈ wholePlaneEdgeι W 0 ''
        boundaryOuterEdgeSet (shiftedStream W 0) h := by
  rw [← boundaryOuterEdge_range (shiftedStream W 0) h]
  constructor
  · intro hs
    have himage (k : ℤ) :
        wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k) ∈
          wholePlaneEdgeι W 0 '' Set.range (boundaryOuterEdge (shiftedStream W 0) h) :=
      Set.mem_image_of_mem _ (Set.mem_range_self k)
    rcases hs with hroot | hrest
    · refine hroot ▸ ?_
      simpa [m0CutLambdaZero, boundaryOuterEdge_zero] using himage 0
    · rcases hrest with hright | hleft
      · rcases hright with ⟨P, hP, j, hedge⟩
        have hboundary := m0Cut_betaR_edges W H h P hP j
        have hk : 1 ≤ (j : ℤ) + 1 := by omega
        have hindex : boundaryOuterEdge (shiftedStream W 0) h
            ((j : ℤ) + 1) = kmswRightBoundaryEdge (shiftedStream W 0) (j + 1) := by
          rw [boundaryOuterEdge_of_positive (shiftedStream W 0) h hk]
          congr 1
        have hmem := himage ((j : ℤ) + 1)
        rw [hindex, ← hboundary] at hmem
        rw [hedge] at hmem
        exact hmem
      · rcases hleft with ⟨P, j, hedge⟩
        have hboundary := m0Cut_betaL_edges W H h hLL P j
        have hk : -(j : ℤ) - 1 ≤ -1 := by omega
        have hindex : boundaryOuterEdge (shiftedStream W 0) h
            (-(j : ℤ) - 1) =
              kmswLLCreatedEdge (shiftedStream W 0)
                (boundaryHitTime (shiftedStream W 0) h (-(j : ℤ) - 1)) :=
          boundaryOuterEdge_of_negative (shiftedStream W 0) h hk
        have hmem := himage (-(j : ℤ) - 1)
        rw [hindex, ← hboundary] at hmem
        rw [hedge] at hmem
        exact hmem
  · intro he
    simp only [Set.mem_image, Set.mem_range] at he
    rcases he with ⟨a, ha, hae⟩
    rcases ha with ⟨k, rfl⟩
    by_cases hkneg : k ≤ -1
    · obtain ⟨P, hP⟩ := m0Cut_betaL_exists W H h hLL
      let j : ℕ := (-k - 1).toNat
      have hjcast : (j : ℤ) = -k - 1 := by
        dsimp [j]
        exact Int.toNat_of_nonneg (by omega)
      have hindex : -(j : ℤ) - 1 = k := by omega
      have hedge := m0Cut_betaL_edges W H h hLL P j
      have hboundary := boundaryOuterEdge_of_negative (shiftedStream W 0) h hkneg
      rw [hindex] at hedge
      rw [hboundary] at hae
      right
      right
      refine ⟨P, j, ?_⟩
      exact hedge.trans hae
    · by_cases hkpos : 1 ≤ k
      · obtain ⟨P, hP, hPedge⟩ :=
          wholePlaneRightmostRay_exists_root_terminal W H 0 h
        have hroot : wholePlaneEdgeEast W (m0CutLambdaZero W) =
            wholePlaneVertexι W 0 1 := by
          rw [(m0Cut_lambdaZero_endpoints W h).2, boundaryVertex_one]
        have hP0 : P.vertex 0 = wholePlaneEdgeEast W (m0CutLambdaZero W) :=
          hP.trans hroot.symm
        let j : ℕ := k.toNat - 1
        have hj : j + 1 = k.toNat := by
          dsimp [j]
          omega
        have hboundary := boundaryOuterEdge_of_positive (shiftedStream W 0) h hkpos
        have hindex : boundaryOuterEdge (shiftedStream W 0) h k =
            kmswRightBoundaryEdge (shiftedStream W 0) (j + 1) := by
          rw [hboundary, hj]
        have hedge : P.edge j = e := by
          rw [hindex] at hae
          exact (hPedge j).trans hae
        right
        left
        exact ⟨P, hP0, j, hedge⟩
      · have hkzero : k = 0 := by omega
        subst k
        have hboundary := boundaryOuterEdge_zero (shiftedStream W 0) h
        have hroot : wholePlaneEdgeι W 0 0 = m0CutLambdaZero W := rfl
        rw [hboundary] at hae
        left
        exact hae.symm.trans hroot

end DirectedDistances.KMSW
