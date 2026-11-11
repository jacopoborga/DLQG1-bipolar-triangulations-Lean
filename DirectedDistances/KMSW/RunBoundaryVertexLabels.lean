module

public import DirectedDistances.KMSW.BoundaryLabelling
public import DirectedDistances.KMSW.RunBoundaryOuterFace

/-! # Hit-indexed labels of the combinatorial run outer face

source embedded boundary and not the paper result. -/

public section
namespace DirectedDistances.KMSW

open scoped Classical

/-- The right-boundary edge with index zero is the root, and each later edge joins
`x_j` to `x_{j+1}` in west-to-east order. Helper toward Lemma 3.10
the combinatorial run boundary, not the source embedded boundary or paper result. -/
theorem kmswRightBoundaryEdge_hit_endpoints (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (j : ℕ) :
    edgeWest w (kmswRightBoundaryEdge w j) = boundaryVertex w h (j : ℤ) ∧
      edgeEast w (kmswRightBoundaryEdge w j) = boundaryVertex w h ((j : ℤ) + 1) := by
  cases j with
  | zero =>
      rw [kmswRightBoundaryEdge_zero]
      constructor
      · simp [edgeWest, boundaryVertex_zero, kmswStage, kmswInit]
      · simp [edgeEast, boundaryVertex_one, kmswStage, kmswInit]
  | succ j =>
      have hp := boundaryVertex_right_edge_present_source w h
        (k := j + 1) (by omega)
      simpa only [Nat.cast_succ] using And.intro hp.2.1 hp.2.2

/-- The first-hit LL edge indexed by `j` has geometric west and east endpoints
`x_{-(j+1)}` and `x_{-j}` and is missing from the directed run. These are
geometric endpoints, not a directed orientation. Helper toward Lemma 3.10
source embedded boundary or paper result. -/
theorem kmswLLCreatedEdge_hit_endpoints (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (j : ℕ) :
    edgeWest w (kmswLLCreatedEdge w
      (boundaryHitTime w h (-((j : ℤ) + 1)))) =
        boundaryVertex w h (-((j : ℤ) + 1)) ∧
      edgeEast w (kmswLLCreatedEdge w
        (boundaryHitTime w h (-((j : ℤ) + 1)))) =
          boundaryVertex w h (-(j : ℤ)) ∧
      ¬ EdgePresent w (kmswLLCreatedEdge w
        (boundaryHitTime w h (-((j : ℤ) + 1)))) := by
  let k : ℤ := -((j : ℤ) + 1)
  have hk : k ≤ -1 := by dsimp [k]; omega
  have hends := boundaryOuterEdge_endpoints w h k
  rw [boundaryOuterEdge_of_negative w h hk] at hends
  have heastIndex : k + 1 = -(j : ℤ) := by dsimp [k]; omega
  rcases hends with ⟨hw, he, _, hmissing⟩
  refine ⟨?_, ?_, hmissing hk⟩
  · simpa [k] using hw
  · rw [heastIndex] at he
    simpa [k] using he

/-- The hit-indexed labels are injective. Helper toward Lemma 3.10
not identify these labels with the source embedded boundary. -/
theorem boundaryVertexLabels_injective (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) : Function.Injective (boundaryVertex w h) :=
  boundaryVertex_injective w h

/-- Endpoints of all right-boundary edges are exactly the hit-indexed labels
with nonnegative indices. Helper toward Lemma 3.10 (`lem-uibot-bdy`,
boundary or paper result. -/
theorem kmswRightBoundaryEdge_endpoint_vertices_eq_nonneg (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) :
    {v | ∃ j : ℕ,
      v = edgeWest w (kmswRightBoundaryEdge w j) ∨
        v = edgeEast w (kmswRightBoundaryEdge w j)} =
      {v | ∃ k : ℤ, 0 ≤ k ∧ v = boundaryVertex w h k} := by
  ext v
  constructor
  · rintro ⟨j, hv | hv⟩
    · refine ⟨j, by omega, ?_⟩
      exact hv.trans (kmswRightBoundaryEdge_hit_endpoints w h j).1
    · refine ⟨(j : ℤ) + 1, by omega, ?_⟩
      exact hv.trans (kmswRightBoundaryEdge_hit_endpoints w h j).2
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k.toNat, Or.inl ?_⟩
    have hw := (kmswRightBoundaryEdge_hit_endpoints w h k.toNat).1
    simpa [Int.toNat_of_nonneg hk] using hw.symm

/-- Endpoints of the first-hit LL edges are exactly the hit-indexed labels
with nonpositive indices. The edges are geometrically ordered west-to-east but
are missing from the directed run. Helper toward Lemma 3.10 (`lem-uibot-bdy`,
boundary or paper result. -/
theorem kmswLLCreatedEdge_endpoint_vertices_eq_nonpos (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) :
    {v | ∃ j : ℕ,
      v = edgeWest w (kmswLLCreatedEdge w
        (boundaryHitTime w h (-((j : ℤ) + 1)))) ∨
        v = edgeEast w (kmswLLCreatedEdge w
          (boundaryHitTime w h (-((j : ℤ) + 1))))} =
      {v | ∃ k : ℤ, k ≤ 0 ∧ v = boundaryVertex w h k} := by
  ext v
  constructor
  · rintro ⟨j, hv | hv⟩
    · refine ⟨-((j : ℤ) + 1), by omega, ?_⟩
      exact hv.trans (kmswLLCreatedEdge_hit_endpoints w h j).1
    · refine ⟨-(j : ℤ), by omega, ?_⟩
      exact hv.trans (kmswLLCreatedEdge_hit_endpoints w h j).2.1
  · rintro ⟨k, hk, rfl⟩
    let j := (-k).toNat
    have hj : (j : ℤ) = -k := by
      dsimp [j]
      exact Int.toNat_of_nonneg (by omega)
    refine ⟨j, Or.inr ?_⟩
    have hlabel : -(j : ℤ) = k := by rw [hj]; omega
    calc
      boundaryVertex w h k = boundaryVertex w h (-(j : ℤ)) :=
        congrArg (boundaryVertex w h) hlabel.symm
      _ = edgeEast w (kmswLLCreatedEdge w
          (boundaryHitTime w h (-((j : ℤ) + 1)))) :=
        (kmswLLCreatedEdge_hit_endpoints w h j).2.1.symm

/-- The vertices incident to the run outer-face edge set are exactly the range
of `boundaryVertex`. The edge set is the one characterized in
`RunBoundaryOuterFace.lean:85`; these hit-indexed labels are not thereby
identified with the source embedded boundary. Helper toward Lemma 3.10
paper result. -/
theorem kmswRun_outerFace_endpoint_vertices_eq_range (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) :
    {v | ∃ e ∈ {e : ℕ | ¬ ∃ j : TriangleCreationTime w,
      (e, true) ∈ stageTriangleDartList w j},
      v = edgeWest w e ∨ v = edgeEast w e} =
      Set.range (boundaryVertex w h) := by
  ext v
  constructor
  · rintro ⟨e, he, hv | hv⟩
    · rw [kmswRun_outerFace_edges_eq_of_hits w h] at he
      simp only [Set.mem_union] at he
      rcases he with hr | hl
      · obtain ⟨j, rfl⟩ := Set.mem_range.mp hr
        refine ⟨j, ?_⟩
        exact (kmswRightBoundaryEdge_hit_endpoints w h j).1.symm.trans hv.symm
      · obtain ⟨j, rfl⟩ := Set.mem_range.mp hl
        refine ⟨-((j : ℤ) + 1), ?_⟩
        exact (kmswLLCreatedEdge_hit_endpoints w h j).1.symm.trans hv.symm
    · rw [kmswRun_outerFace_edges_eq_of_hits w h] at he
      simp only [Set.mem_union] at he
      rcases he with hr | hl
      · obtain ⟨j, rfl⟩ := Set.mem_range.mp hr
        refine ⟨(j : ℤ) + 1, ?_⟩
        exact (kmswRightBoundaryEdge_hit_endpoints w h j).2.symm.trans hv.symm
      · obtain ⟨j, rfl⟩ := Set.mem_range.mp hl
        refine ⟨-(j : ℤ), ?_⟩
        exact (kmswLLCreatedEdge_hit_endpoints w h j).2.1.symm.trans hv.symm
  · rintro ⟨k, rfl⟩
    by_cases hk : 0 ≤ k
    · let j := k.toNat
      have hj : (j : ℤ) = k := by
        dsimp [j]
        exact Int.toNat_of_nonneg hk
      refine ⟨kmswRightBoundaryEdge w j, ?_, Or.inl ?_⟩
      · rw [kmswRun_outerFace_edges_eq_of_hits w h]
        exact Set.mem_union_left _ ⟨j, rfl⟩
      · have he := (kmswRightBoundaryEdge_hit_endpoints w h j).1
        rw [hj] at he
        exact he.symm
    · have hkneg : k ≤ -1 := by omega
      let j := (-k - 1).toNat
      have hj : (j : ℤ) = -k - 1 := by
        dsimp [j]
        exact Int.toNat_of_nonneg (by omega)
      have hindex : -((j : ℤ) + 1) = k := by omega
      refine ⟨kmswLLCreatedEdge w (boundaryHitTime w h k), ?_, Or.inl ?_⟩
      · rw [kmswRun_outerFace_edges_eq_of_hits w h]
        apply Set.mem_union_right
        simpa [hindex] using
          (show kmswLLCreatedEdge w (boundaryHitTime w h
              (-((j : ℤ) + 1))) ∈
            Set.range (fun j : ℕ => kmswLLCreatedEdge w
              (boundaryHitTime w h (-((j : ℤ) + 1))) ) from ⟨j, rfl⟩)
      · have he := (kmswLLCreatedEdge_hit_endpoints w h j).1
        rw [hindex] at he
        exact he.symm

end DirectedDistances.KMSW
