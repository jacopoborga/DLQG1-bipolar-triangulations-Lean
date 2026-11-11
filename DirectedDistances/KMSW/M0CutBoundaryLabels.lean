module

public import DirectedDistances.KMSW.M0CutPresence
public import DirectedDistances.KMSW.KMSWFutureMapOuterBoundary

public section
namespace DirectedDistances.KMSW

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
The source boundary labels follow the two extremal paths from the root. -/
@[expose] def m0CutBoundaryLabel (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (k : ℤ) (x : WholePlaneVertex W) : Prop :=
  (k = 0 ∧ x = wholePlaneEdgeWest W (m0CutLambdaZero W)) ∨
    (k = 1 ∧ x = wholePlaneEdgeEast W (m0CutLambdaZero W)) ∨
    (2 ≤ k ∧ ∃ P : WholePlaneRightmostRay W H,
      P.vertex 0 = wholePlaneEdgeEast W (m0CutLambdaZero W) ∧
        P.vertex (k - 1).toNat = x) ∨
    (k ≤ -1 ∧ ∃ P : M0CutLeftmostChain W H
      (wholePlaneEdgeWest W (m0CutLambdaZero W)), P.vertex (-k).toNat = x)

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
The right ray vertex at time n has boundary label n + 1. -/
theorem m0Cut_betaR_vertices (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (P : WholePlaneRightmostRay W H)
    (hP : P.vertex 0 = wholePlaneEdgeEast W (m0CutLambdaZero W)) (n : ℕ) :
    P.vertex n = wholePlaneVertexι W 0
      (boundaryVertex (shiftedStream W 0) h ((n : ℤ) + 1)) := by
  have he : P.edge n = wholePlaneEdgeι W 0
      (boundaryOuterEdge (shiftedStream W 0) h ((n : ℤ) + 1)) := by
    rw [m0Cut_betaR_edges W H h P hP n,
      boundaryOuterEdge_of_positive (shiftedStream W 0) h (by omega)]
    have hi : ((n : ℤ) + 1).toNat = n + 1 := by omega
    rw [hi]
  calc
    P.vertex n = wholePlaneEdgeWest W (P.edge n) := (P.rightmost n).2.1.symm
    _ = wholePlaneEdgeWest W (wholePlaneEdgeι W 0
        (boundaryOuterEdge (shiftedStream W 0) h ((n : ℤ) + 1))) :=
      congrArg (wholePlaneEdgeWest W) he
    _ = wholePlaneVertexι W 0
        (boundaryVertex (shiftedStream W 0) h ((n : ℤ) + 1)) := by
      rw [wholePlaneEdgeWest_ι,
        (boundaryOuterEdge_endpoints (shiftedStream W 0) h ((n : ℤ) + 1)).1]

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
The backward left chain vertex at time n has boundary label -n. -/
theorem m0Cut_betaL_vertices
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (P : M0CutLeftmostChain W H (wholePlaneEdgeWest W (m0CutLambdaZero W)))
    (n : ℕ) :
    P.vertex n = wholePlaneVertexι W 0
      (boundaryVertex (shiftedStream W 0) h (-(n : ℤ))) := by
  cases n with
  | zero =>
    exact P.endpoint.trans (m0Cut_lambdaZero_endpoints W h).1
  | succ n =>
    have hi : -((n + 1 : ℕ) : ℤ) = -(n : ℤ) - 1 := by omega
    have he : P.edge n = wholePlaneEdgeι W 0
        (boundaryOuterEdge (shiftedStream W 0) h (-(n : ℤ) - 1)) := by
      rw [m0Cut_betaL_edges W H h hLL P n,
        boundaryOuterEdge_of_negative (shiftedStream W 0) h (by omega)]
    rw [hi, ← P.westEndpoint n, he, wholePlaneEdgeWest_ι,
      (boundaryOuterEdge_endpoints (shiftedStream W 0) h (-(n : ℤ) - 1)).1]

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
The path-defined labels agree exactly with the run-zero boundary labels. -/
theorem m0Cut_boundaryLabel_iff
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (k : ℤ) (x : WholePlaneVertex W) :
    m0CutBoundaryLabel W H k x ↔
      x = wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h k) := by
  constructor
  · intro hx
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hk, P, hP, hx⟩ | ⟨hk, P, hx⟩
    · exact (m0Cut_lambdaZero_endpoints W h).1
    · exact (m0Cut_lambdaZero_endpoints W h).2
    · rw [← hx, m0Cut_betaR_vertices W H h P hP]
      have hi : ((k - 1).toNat : ℤ) + 1 = k := by omega
      rw [hi]
    · rw [← hx, m0Cut_betaL_vertices W H h hLL P]
      have hi : -((-k).toNat : ℤ) = k := by omega
      rw [hi]
  · intro hx
    by_cases hk0 : k = 0
    · left
      refine ⟨hk0, hx.trans ?_⟩
      rw [hk0]
      exact (m0Cut_lambdaZero_endpoints W h).1.symm
    by_cases hk1 : k = 1
    · right; left
      refine ⟨hk1, hx.trans ?_⟩
      rw [hk1]
      exact (m0Cut_lambdaZero_endpoints W h).2.symm
    by_cases hk : 2 ≤ k
    · right; right; left
      obtain ⟨P, hP, _⟩ := wholePlaneRightmostRay_exists_root_terminal W H 0 h
      have hroot : P.vertex 0 = wholePlaneEdgeEast W (m0CutLambdaZero W) := by
        rw [(m0Cut_lambdaZero_endpoints W h).2, boundaryVertex_one]
        exact hP
      refine ⟨hk, P, hroot, ?_⟩
      rw [m0Cut_betaR_vertices W H h P hroot]
      have hi : ((k - 1).toNat : ℤ) + 1 = k := by omega
      rw [hi]
      exact hx.symm
    · right; right; right
      obtain ⟨P, _⟩ := m0Cut_betaL_exists W H h hLL
      refine ⟨by omega, P, ?_⟩
      rw [m0Cut_betaL_vertices W H h hLL P]
      have hi : -((-k).toNat : ℤ) = k := by omega
      rw [hi]
      exact hx.symm

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
Every integer has exactly one source boundary label. -/
theorem m0Cut_boundaryLabel_existsUnique
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (k : ℤ) : ∃! x, m0CutBoundaryLabel W H k x := by
  refine ⟨wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h k),
    (m0Cut_boundaryLabel_iff W H h hLL k _).mpr rfl, ?_⟩
  intro x hx
  exact (m0Cut_boundaryLabel_iff W H h hLL k x).mp hx

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
Distinct integer labels give distinct ambient vertices. -/
theorem m0Cut_boundaryLabel_ne
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    {k k' : ℤ} {x x' : WholePlaneVertex W} (hk : k ≠ k')
    (hx : m0CutBoundaryLabel W H k x) (hx' : m0CutBoundaryLabel W H k' x') :
    x ≠ x' := by
  rw [m0Cut_boundaryLabel_iff W H h hLL] at hx hx'
  intro he
  apply hk
  apply boundaryVertex_injective (shiftedStream W 0) h
  exact wholePlaneVertexι_injective W 0 (hx.symm.trans (he.trans hx'))

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
The specified geometric seam edge joins each pair of consecutive labels. -/
theorem m0Cut_boundaryLabel_consecutive
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (k : ℤ) {x y : WholePlaneVertex W}
    (hx : m0CutBoundaryLabel W H k x) (hy : m0CutBoundaryLabel W H (k + 1) y) :
    m0CutSeamEdge W H
        (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) ∧
      wholePlaneEdgeWest W
        (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) = x ∧
      wholePlaneEdgeEast W
        (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) = y := by
  rw [m0Cut_boundaryLabel_iff W H h hLL] at hx hy
  refine ⟨?_, ?_, ?_⟩
  · apply (m0Cut_seamEdge_iff W H h hLL _).mpr
    apply Set.mem_image_of_mem
    rw [← boundaryOuterEdge_range]
    exact Set.mem_range_self k
  · rw [wholePlaneEdgeWest_ι, (boundaryOuterEdge_endpoints (shiftedStream W 0) h k).1]
    exact hx.symm
  · rw [wholePlaneEdgeEast_ι,
      (boundaryOuterEdge_endpoints (shiftedStream W 0) h k).2.1]
    exact hy.symm

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
After geometric reversal, the first inverse-rotation return traverses the cut
boundary from east to west, including the darts of missing geometric edges. -/
theorem m0Cut_outerFace_firstReturn (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ) :
    ∃ n : ℕ, 0 < n ∧
      ((wholePlaneRotation W H).symm ^ n)
          (wholePlaneDartFlip W
            (wholePlaneDartι W 0 (futureMapBoundaryDart (shiftedStream W 0) h k))) =
        wholePlaneDartι W 0 (futureMapBoundaryDart (shiftedStream W 0) h (k - 1)) ∧
      ∀ j : ℕ, 0 < j → j < n →
        ((wholePlaneRotation W H).symm ^ j)
            (wholePlaneDartFlip W
              (wholePlaneDartι W 0 (futureMapBoundaryDart (shiftedStream W 0) h k))) ∉
          Set.range (wholePlaneDartι W 0) := by
  obtain ⟨n, hn, hret, hmin⟩ := m0Cut_rotation_symm_firstReturn W H
    (futureMapEdgeInv (futureMapBoundaryDart (shiftedStream W 0) h k))
  have hf := futureMapBoundaryDart_faceSucc (shiftedStream W 0) (H.1 0) h k
  change (kmswInfRot (shiftedStream W 0) (H.1 0)).symm
    (futureMapEdgeInv (futureMapBoundaryDart (shiftedStream W 0) h k)) =
      futureMapBoundaryDart (shiftedStream W 0) h (k - 1) at hf
  refine ⟨n, hn, ?_, hmin⟩
  exact hret.trans (congrArg (wholePlaneDartι W 0) hf)

end DirectedDistances.KMSW
