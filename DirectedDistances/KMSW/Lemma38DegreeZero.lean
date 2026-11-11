module

public import DirectedDistances.KMSW.WholePlaneRunBoundaryDegree
public import DirectedDistances.KMSW.M0CutBoundaryLabels
public import DirectedDistances.KMSW.M0CutSeam
public import DirectedDistances.KMSW.M0CutPresence
public import DirectedDistances.KMSW.Lemma38SourceZero
public import DirectedDistances.KMSW.AllocatedVertices
public import DirectedDistances.KMSW.LocalFinitenessIID

public section
namespace DirectedDistances.KMSW

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, author ruling probability-one scope); not a paper result.
At start zero, the run degree classification identifies the vertices of the
leftmost chain as exactly those with no incoming present run edge. The directed
cut steps give the source's outgoing/incoming degree clauses. -/
theorem lemma38_degree_zero
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (P : M0CutLeftmostChain W H (wholePlaneEdgeWest W (m0CutLambdaZero W))) :
    (∀ v : ℕ, ∃ e, EdgePresent (shiftedStream W 0) e ∧
      edgeWest (shiftedStream W 0) e = v) ∧
    (∀ v : ℕ, (¬ ∃ e, EdgePresent (shiftedStream W 0) e ∧
          edgeEast (shiftedStream W 0) e = v) ↔
        wholePlaneVertexι W 0 v ∈ Set.range P.vertex) ∧
    (let S : WholePlaneEdge W → Prop := fun e =>
      e ∈ wholePlaneEdgeι W 0 ''
        boundaryOuterEdgeSet (shiftedStream W 0) h
     ∀ v : WholePlaneVertex W,
       v ∈ Set.range (wholePlaneVertexι W 0) →
       ((v ∈ Set.range P.vertex →
          (∃ x, m0CutDirectedStep W H S v x) ∧
            ¬ ∃ x, m0CutDirectedStep W H S x v) ∧
        (v ∉ Set.range P.vertex →
          (∃ x, m0CutDirectedStep W H S x v) ∧
            ∃ x, m0CutDirectedStep W H S v x))) := by
  let w := shiftedStream W 0
  let S : WholePlaneEdge W → Prop := fun e =>
    e ∈ wholePlaneEdgeι W 0 '' boundaryOuterEdgeSet w h
  have hS : ∀ e, S e ↔
      e ∈ wholePlaneEdgeι W 0 '' boundaryOuterEdgeSet w h := fun e => Iff.rfl
  have hLb : ∀ a : ℤ, ∃ n, L w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.leftHit (min a (-1)) (min_le_right _ _)
    exact ⟨n, by
      calc
        L w n = min a (-1) := hn
        _ ≤ a := min_le_left _ _⟩
  have hR : ∀ a : ℤ, ∃ n, R w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.rightHit (max (-a) 1) (le_max_right _ _)
    exact ⟨n, by
      calc
        R w n = -(max (-a) 1) := hn
        _ ≤ a := by have hm := le_max_left (-a) 1; omega⟩
  have halloc : ∀ v : ℕ, ∃ m, v < (kmswStage w m).nextVertex := by
    intro v
    exact kmsw_vertex_allocated_of_finite_incidence w
      (fun u => kmsw_finite_incident_edges_of_unbounded_below w hLb hR u) v
  have hdegree := kmswRunBoundaryDegree w h
  refine ⟨?_, ?_, ?_⟩
  · intro v
    exact (hdegree v (halloc v)).1
  · intro v
    obtain ⟨_, hclass⟩ := hdegree v (halloc v)
    constructor
    · rintro hno
      obtain ⟨k, hk, hvk⟩ := hclass.mp hno
      let j := (-k).toNat
      have hj : -((j : ℕ) : ℤ) = k := by
        dsimp [j]
        omega
      refine ⟨j, ?_⟩
      rw [m0Cut_betaL_vertices W H h hLL P j, hj, hvk]
    · rintro ⟨j, hj⟩
      have hmap : wholePlaneVertexι W 0 v =
          wholePlaneVertexι W 0 (boundaryVertex w h (-(j : ℤ))) := by
        rw [← m0Cut_betaL_vertices W H h hLL P j]
        exact hj.symm
      have hvk := wholePlaneVertexι_injective W 0 hmap
      exact hclass.mpr ⟨-(j : ℤ), by omega, hvk⟩
  · dsimp only
    intro v hv
    obtain ⟨a, rfl⟩ := hv
    have ha : ∃ m, a < (kmswStage w m).nextVertex := halloc a
    obtain ⟨hout, hclass⟩ := hdegree a ha
    have hnoRange : (¬ ∃ e, EdgePresent w e ∧ edgeEast w e = a) ↔
        wholePlaneVertexι W 0 a ∈ Set.range P.vertex := by
      constructor
      · intro hno
        obtain ⟨k, hk, hav⟩ := hclass.mp hno
        let j := (-k).toNat
        have hj : -((j : ℕ) : ℤ) = k := by
          dsimp [j]
          omega
        refine ⟨j, ?_⟩
        rw [m0Cut_betaL_vertices W H h hLL P j, hj, hav]
      · rintro ⟨j, hj⟩
        have hmap : wholePlaneVertexι W 0 a =
            wholePlaneVertexι W 0 (boundaryVertex w h (-(j : ℤ))) := by
          rw [← m0Cut_betaL_vertices W H h hLL P j]
          exact hj.symm
        have hav := wholePlaneVertexι_injective W 0 hmap
        exact hclass.mpr ⟨-(j : ℤ), by omega, hav⟩
    have hcutNo : (¬ ∃ x, m0CutDirectedStep W H S x
          (wholePlaneVertexι W 0 a)) ↔
        ¬ ∃ e, EdgePresent w e ∧ edgeEast w e = a := by
      constructor
      · intro hno
        rintro ⟨e, he, heast⟩
        apply hno
        refine ⟨wholePlaneVertexι W 0 (edgeWest w e), ?_⟩
        apply (m0Cut_directedStep_iff_present W H h hLL S hS _ _).mpr
        exact ⟨e, he, rfl, congrArg (wholePlaneVertexι W 0) heast⟩
      · intro hno
        rintro ⟨x, hx⟩
        obtain ⟨e, he, _, heast⟩ :=
          (m0Cut_directedStep_iff_present W H h hLL S hS _ _).mp hx
        apply hno
        exact ⟨e, he, wholePlaneVertexι_injective W 0 heast⟩
    have houtCut : ∃ x, m0CutDirectedStep W H S
        (wholePlaneVertexι W 0 a) x := by
      obtain ⟨e, he, hwest⟩ := hout
      refine ⟨wholePlaneVertexι W 0 (edgeEast w e), ?_⟩
      apply (m0Cut_directedStep_iff_present W H h hLL S hS _ _).mpr
      exact ⟨e, he, congrArg (wholePlaneVertexι W 0) hwest, rfl⟩
    constructor
    · intro hleft
      constructor
      · exact houtCut
      · exact hcutNo.mpr (hnoRange.mpr hleft)
    · intro hright
      constructor
      · have hinRun : ∃ e, EdgePresent w e ∧ edgeEast w e = a := by
          by_contra hnone
          exact hright (hnoRange.mp hnone)
        obtain ⟨e, he, heast⟩ := hinRun
        refine ⟨wholePlaneVertexι W 0 (edgeWest w e), ?_⟩
        apply (m0Cut_directedStep_iff_present W H h hLL S hS _ _).mpr
        exact ⟨e, he, rfl, congrArg (wholePlaneVertexι W 0) heast⟩
      · exact houtCut

end DirectedDistances.KMSW
