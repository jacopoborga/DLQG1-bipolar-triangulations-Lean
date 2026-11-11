module

public import DirectedDistances.KMSW.RunRightmostRay
public import DirectedDistances.KMSW.Lemma38DegreeZero
public import DirectedDistances.KMSW.KMSWFutureMapOuterBoundary

/-! Helper toward Lemma 3.10 (lem-uibot-bdy, clause C4, intrinsic reading); not a paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, clause C4, intrinsic reading); not a paper
vertex has an outgoing edge and a dart at that vertex that is not a future-map tail. -/
theorem lemma38_run_rightmost_premises
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (P : M0CutLeftmostChain W H (wholePlaneEdgeWest W (m0CutLambdaZero W))) :
    ∀ v : ℕ,
      (∃ e, EdgePresent (shiftedStream W 0) e ∧
        edgeWest (shiftedStream W 0) e = v) ∧
      (∃ d, kmswLimitDartVertex (shiftedStream W 0) d = v ∧
        ¬ futureMapTail (shiftedStream W 0) d) := by
  let w := shiftedStream W 0
  have hC3 := lemma38_degree_zero W H h hLL P
  have hLb : ∀ a : ℤ, ∃ n, L w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.leftHit (min a (-1)) (min_le_right _ _)
    exact ⟨n, hn.le.trans (min_le_left _ _)⟩
  have hR : ∀ a : ℤ, ∃ n, R w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.rightHit (max (-a) 1) (le_max_right _ _)
    refine ⟨n, ?_⟩
    rw [hn]
    have hm := le_max_left (-a) 1
    omega
  have halloc : ∀ v : ℕ, ∃ m, v < (kmswStage w m).nextVertex := by
    intro v
    exact kmsw_vertex_allocated_of_finite_incidence w
      (fun u => kmsw_finite_incident_edges_of_unbounded_below w hLb hR u) v
  intro v
  have hdegree := kmswRunBoundaryDegree w h v (halloc v)
  refine ⟨hC3.1 v, ?_⟩
  by_cases hin : ∃ e, EdgePresent w e ∧ edgeEast w e = v
  · obtain ⟨e, he, hev⟩ := hin
    refine ⟨(e, true), ?_, ?_⟩
    · simpa [kmswLimitDartVertex, hev]
    · simp [futureMapTail]
  · obtain ⟨k, hk, hv⟩ := hdegree.2.mp hin
    have hv' : boundaryVertex w h ((k - 1) + 1) = v := by
      rw [show (k - 1) + 1 = k by omega]
      exact hv.symm
    refine ⟨futureMapBoundaryDart w h (k - 1), ?_, ?_⟩
    · exact (futureMapBoundaryDart_endpoints w h (k - 1)).1.trans hv'
    · simp [futureMapBoundaryDart, futureMapTail]

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, clause C4, intrinsic reading); not a paper
selector, including at the root vertex. -/
theorem kmswRunRightmostOutAt_exists'
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (P : M0CutLeftmostChain W H (wholePlaneEdgeWest W (m0CutLambdaZero W)))
    (v : ℕ) :
    ∃ e, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0) v e := by
  obtain ⟨hout, hstop⟩ := lemma38_run_rightmost_premises W H h hLL P v
  exact kmswRunRightmostOutAt_exists (shiftedStream W 0) (H.1 0) v hout hstop

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, clause C4, intrinsic reading); not a paper
vertex, retaining its edge identity. -/
@[expose] noncomputable def kmswRunRightmostRayFrom
    (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (hprem : ∀ v, (∃ e, EdgePresent w e ∧ edgeWest w e = v) ∧
      ∃ d, kmswLimitDartVertex w d = v ∧ ¬ futureMapTail w d)
    (v : ℕ) : KMSWRunRightmostRay w hfin := by
  classical
  let select : ℕ → ℕ := fun u =>
    Classical.choose (kmswRunRightmostOutAt_exists w hfin u (hprem u).1 (hprem u).2)
  let vertex : ℕ → ℕ := Nat.rec v (fun _ u => edgeEast w (select u))
  refine ⟨vertex, fun i => select (vertex i), ?_, ?_⟩
  · intro i
    exact Classical.choose_spec
      (kmswRunRightmostOutAt_exists w hfin (vertex i)
        (hprem (vertex i)).1 (hprem (vertex i)).2)
  · intro i
    rfl

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, clause C4, intrinsic reading); not a paper -/
theorem kmswRunRightmostRays_agree_after_common_vertex
    {w : ℕ → Fin 3} {hfin : KMSWFiniteIncidence w}
    (P Q : KMSWRunRightmostRay w hfin) (i j : ℕ)
    (h : P.vertex i = Q.vertex j) :
    ∀ t, P.vertex (i + t) = Q.vertex (j + t) :=
  kmswRunRightmostRays_coalesce_of_common_vertex P Q i j h

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, clause C4, intrinsic reading); not a paper -/
theorem kmswRunRightmostRay_exists'
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (P : M0CutLeftmostChain W H (wholePlaneEdgeWest W (m0CutLambdaZero W)))
    (v : ℕ) :
    ∃ R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0), R.vertex 0 = v := by
  refine ⟨kmswRunRightmostRayFrom (shiftedStream W 0) (H.1 0)
    (lemma38_run_rightmost_premises W H h hLL P) v, ?_⟩
  rfl

end DirectedDistances.KMSW
