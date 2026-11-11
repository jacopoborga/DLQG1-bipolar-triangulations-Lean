module

public import DirectedDistances.KMSW.BoltzmannEdgeMarkedLaw
import DirectedDistances.PlanarMap.PlanarPathGlueRep

/-! Helper toward lem-boltzmann-finite / Lemma 3.12
the left-boundary edge and vertex mark positions are in bijection with the actual
left-boundary edges and vertices of the class representative; marked-vertex convention unresolved;
not the paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- Helper toward lem-boltzmann-finite / Lemma 3.12
distinct left-boundary edge mark positions select distinct geometric edge orbits
of the class representative; marked-vertex convention unresolved; not the paper result. -/
theorem leftEdgeMarkEdge_injective {r : ℕ} (q : AllBoltzmannSpace r) :
    Function.Injective (leftEdgeMarkEdge q) := by
  intro i j hij
  have h := simplePath_edgeOrbit_injective q.2.2.out.B.leftPath hij
  exact Fin.ext (congrArg (fun k : Fin q.2.2.out.B.leftPath.darts.length => k.val) h)

/-- Helper toward lem-boltzmann-finite / Lemma 3.12
the left-boundary edge marks have image exactly the geometric edge orbits of
the left-path darts; marked-vertex convention unresolved; not the paper result. -/
theorem leftEdgeMarkEdge_range {r : ℕ} (q : AllBoltzmannSpace r) :
    Set.range (leftEdgeMarkEdge q) =
      {e | ∃ d ∈ q.2.2.out.B.leftPath.darts, Quotient.mk _ d = e} := by
  ext e
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, List.get_mem _ _, rfl⟩
  · rintro ⟨d, hd, hde⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
    refine ⟨⟨i.val, by
      simpa only [q.2.2.out.B.leftPath.darts_length] using i.isLt⟩, ?_⟩
    change Quotient.mk _ (q.2.2.out.B.leftPath.darts.get i) = e
    exact (congrArg (Quotient.mk _) hi).trans hde

/-- Helper toward lem-boltzmann-finite / Lemma 3.12
the left-boundary edge mark positions are in bijection with the actual
left-boundary edges of the class representative, by `leftEdgeMarkEdge`;
marked-vertex convention unresolved; not the paper result. -/
@[expose] noncomputable def leftEdgeMarkEquiv {r : ℕ} (q : AllBoltzmannSpace r) :
    Fin q.1 ≃
      {e : CombinatorialMap.EdgeQuotient q.2.2.out.B.map.toCombinatorialMap //
        ∃ d ∈ q.2.2.out.B.leftPath.darts, Quotient.mk _ d = e} := by
  refine Equiv.ofBijective (fun i => ⟨leftEdgeMarkEdge q i, ?_⟩) ⟨?_, ?_⟩
  · have hi : leftEdgeMarkEdge q i ∈ Set.range (leftEdgeMarkEdge q) := ⟨i, rfl⟩
    rw [leftEdgeMarkEdge_range q] at hi
    exact hi
  · intro i j hij
    exact leftEdgeMarkEdge_injective q (congrArg Subtype.val hij)
  · intro e
    have he : e.val ∈ Set.range (leftEdgeMarkEdge q) := by
      rw [leftEdgeMarkEdge_range q]
      exact e.property
    obtain ⟨i, hi⟩ := he
    exact ⟨i, Subtype.ext hi⟩

/-- Helper toward lem-boltzmann-finite / Lemma 3.12
select the indexed vertex on the representative's simple left path, including
both endpoints; marked-vertex convention unresolved; not the paper result. -/
@[expose] noncomputable def leftVertexMark {r : ℕ} (q : AllBoltzmannSpace r)
    (j : Fin (q.1 + 1)) : MapVertex q.2.2.out.B.map :=
  q.2.2.out.B.leftPath.vertices.get
    ⟨j.val, by rw [q.2.2.out.B.leftPath.vertices_length]; exact j.isLt⟩

/-- Helper toward lem-boltzmann-finite / Lemma 3.12
distinct left-boundary vertex positions select distinct vertices of the class
representative; marked-vertex convention unresolved; not the paper result. -/
theorem leftVertexMark_injective {r : ℕ} (q : AllBoltzmannSpace r) :
    Function.Injective (leftVertexMark q) := by
  intro i j hij
  have h := q.2.2.out.B.leftPath.vertices_nodup.get_inj_iff.mp hij
  exact Fin.ext (congrArg (fun k : Fin q.2.2.out.B.leftPath.vertices.length => k.val) h)

/-- Helper toward lem-boltzmann-finite / Lemma 3.12
the vertex marks have image exactly the vertices of the representative's left
path; marked-vertex convention unresolved; not the paper result. -/
theorem leftVertexMark_range {r : ℕ} (q : AllBoltzmannSpace r) :
    Set.range (leftVertexMark q) = {v | v ∈ q.2.2.out.B.leftPath.vertices} := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact List.get_mem _ _
  · intro hv
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
    refine ⟨⟨i.val, by
      simpa only [q.2.2.out.B.leftPath.vertices_length] using i.isLt⟩, ?_⟩
    exact hi

/-- Helper toward lem-boltzmann-finite / Lemma 3.12
the left-boundary vertex mark positions are in bijection with the actual
left-boundary vertices of the class representative, by `leftVertexMark`;
marked-vertex convention unresolved; not the paper result. -/
@[expose] noncomputable def leftVertexMarkEquiv {r : ℕ} (q : AllBoltzmannSpace r) :
    Fin (q.1 + 1) ≃ {v : MapVertex q.2.2.out.B.map //
      v ∈ q.2.2.out.B.leftPath.vertices} := by
  refine Equiv.ofBijective (fun i => ⟨leftVertexMark q i, ?_⟩) ⟨?_, ?_⟩
  · have hi : leftVertexMark q i ∈ Set.range (leftVertexMark q) := ⟨i, rfl⟩
    rw [leftVertexMark_range q] at hi
    exact hi
  · intro i j hij
    exact leftVertexMark_injective q (congrArg Subtype.val hij)
  · intro v
    have hv : v.val ∈ Set.range (leftVertexMark q) := by
      rw [leftVertexMark_range q]
      exact v.property
    obtain ⟨i, hi⟩ := hv
    exact ⟨i, Subtype.ext hi⟩

/-- Helper toward lem-boltzmann-finite / Lemma 3.12
every boundary-preserving isomorphism carries the selected left-boundary vertex
to the same position in its target; marked-vertex convention unresolved; not the paper result. -/
theorem leftVertexMark_map {r : ℕ} (q : AllBoltzmannSpace r)
    {R : KMSWMapRep q.1 r q.2.1}
    (I : BipolarBoundaryBaseIso q.2.2.out.B R.B) (j : Fin (q.1 + 1)) :
    I.vertexEquiv (leftVertexMark q j) =
      R.B.leftPath.vertices.get
        ⟨j.val, by rw [R.B.leftPath.vertices_length]; exact j.isLt⟩ := by
  rcases j with ⟨j, hj⟩
  by_cases hjl : j < q.1
  · let i : Fin q.1 := ⟨j, hjl⟩
    let a : Fin q.2.2.out.B.leftPath.darts.length :=
      ⟨j, by rw [q.2.2.out.B.leftPath.darts_length]; exact hjl⟩
    let b : Fin R.B.leftPath.darts.length :=
      ⟨j, by rw [R.B.leftPath.darts_length]; exact hjl⟩
    have ha := q.2.2.out.B.leftPath.edge_step a
    have hb := R.B.leftPath.edge_step b
    calc
      _ = I.vertexEquiv (dartTailVertex q.2.2.out.B.map
          (q.2.2.out.B.leftPath.darts.get a)) := congrArg I.vertexEquiv ha.2.2.1
      _ = dartTailVertex R.B.map
          (I.toEquiv (q.2.2.out.B.leftPath.darts.get a)) :=
        I.vertexEquiv_dartTailVertex _
      _ = dartTailVertex R.B.map (R.B.leftPath.darts.get b) :=
        congrArg (dartTailVertex R.B.map) (leftBoundaryDart_eq_of_baseIso I i)
      _ = _ := hb.2.2.1.symm
  · have hjEq : j = q.1 := by omega
    subst j
    change I.vertexEquiv (q.2.2.out.B.leftPath.vertices.get _) = _
    rw [q.2.2.out.B.leftPath.end_vertex, R.B.leftPath.end_vertex]
    exact I.vertexEquiv_sink

end DirectedDistances.KMSW
