/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.ClosedHalfVertices
public import DirectedDistances.PlanarMap.PlanarPathCutOneSided

/-! # Vertex counts for the two closed path-cut halves

paper result. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r n : ℕ}

private theorem pathCutVertexSum_source_ne_sink
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.source ≠ B.sink := by
  intro h
  have hlen : 0 < B.leftPath.darts.length := by
    rw [B.leftPath.darts_length]
    exact B.left_length_pos
  let i : Fin B.leftPath.darts.length := ⟨0, hlen⟩
  obtain ⟨_, htail, hstart, _⟩ := B.leftPath.edge_step i
  have hstart' : B.leftPath.vertices.get ⟨0, by
      rw [B.leftPath.vertices_length]
      omega⟩ = dartTailVertex B.map (B.leftPath.darts.get i) := by
    simpa [i] using hstart
  have hv : dartTailVertex B.map (B.leftPath.darts.get i) = B.source :=
    hstart'.symm.trans B.leftPath.start_vertex
  have hstep : B.map.directedStep B.source
      (dartHeadVertex B.map (B.leftPath.darts.get i)) := by
    exact ⟨B.leftPath.darts.get i, B.noMissingDarts _, htail, hv, rfl⟩
  apply B.isSink
  refine ⟨dartHeadVertex B.map (B.leftPath.darts.get i), ?_⟩
  simpa [h] using hstep

/-- Every vertex of the base map is represented by a dart in at least one
closed half of the path cut. Helper toward `lem-lr-ind` -/
theorem pathCut_vertex_meets_a_closed_half
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (v : MapVertex B.map) :
    (∃ d : D, d ∈ pathCutLeftHalfDarts B P ∧ dartTailVertex B.map d = v) ∨
      (∃ d : D, d ∈ pathCutRightHalfDarts B P ∧ dartTailVertex B.map d = v) := by
  obtain ⟨d, hd⟩ := Quotient.exists_rep v
  change dartTailVertex B.map d = v at hd
  rcases pathCut_halves_cover B P d with hleft | hright
  · exact Or.inl ⟨d, hleft, hd⟩
  · exact Or.inr ⟨d, hright, hd⟩

/-- A base-map vertex is represented by darts in both closed halves exactly
when it lies on the cut path. The forward direction uses one-sidedness off the
path and the seam characterization; the reverse direction uses an incident
path dart, with the incoming case at the sink. Helper toward `lem-lr-ind` -/
theorem pathCut_vertex_meets_both_closed_halves_iff
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (v : MapVertex B.map) :
    ((∃ d : D, d ∈ pathCutLeftHalfDarts B P ∧ dartTailVertex B.map d = v) ∧
      (∃ d : D, d ∈ pathCutRightHalfDarts B P ∧ dartTailVertex B.map d = v)) ↔
      v ∈ P.vertices := by
  constructor
  · rintro ⟨⟨dL, hdL, htailL⟩, ⟨dR, hdR, htailR⟩⟩
    by_contra hv
    rcases pathCut_vertex_darts_one_sided B P hv with hleft | hright
    · have hseam : dR ∈ pathCutSeamDarts B P := by
        rw [← pathCut_halves_inter_eq_seam B P]
        exact ⟨Or.inl (hleft dR htailR), hdR⟩
      exact hv (htailR ▸ pathCutSeamDarts_tailVertex_mem B P hseam)
    · have hseam : dL ∈ pathCutSeamDarts B P := by
        rw [← pathCut_halves_inter_eq_seam B P]
        exact ⟨hdL, Or.inl (hright dL htailL)⟩
      exact hv (htailL ▸ pathCutSeamDarts_tailVertex_mem B P hseam)
  · intro hv
    by_cases hvsink : v = B.sink
    · have hvsource : v ≠ B.source := by
        rw [hvsink]
        exact (pathCutVertexSum_source_ne_sink B).symm
      obtain ⟨d, hd, hhead, _, hrevLeft, _, hrevRight⟩ :=
        pathCut_vertex_incomingDart_in_both_closed_halves B P hv hvsource
      refine ⟨⟨B.map.toCombinatorialMap.edgeInv d, hrevLeft, ?_⟩,
        ⟨B.map.toCombinatorialMap.edgeInv d, hrevRight, ?_⟩⟩
      · simpa [dartTailVertex, dartHeadVertex] using hhead
      · simpa [dartTailVertex, dartHeadVertex] using hhead
    · obtain ⟨d, hd, htail, hleft, _, hright, _⟩ :=
        pathCut_vertex_outgoingDart_in_both_closed_halves B P hv hvsink
      exact ⟨⟨d, hleft, htail⟩, ⟨d, hright, htail⟩⟩

/-- The two closed-half vertex counts sum to the base-map vertex count plus
the number of vertices on the simple cut path. Helper toward `lem-lr-ind` -/
theorem pathCutHalfMaps_numVertices_sum {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [leftHalfDartsDecidable :
      DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    [rightHalfDartsDecidable :
      DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    [vertexSameCycleDecidable :
      DecidableRel (Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot)]
    [leftHalfVerticesDecidable : DecidablePred
      (fun v : CombinatorialMap.VertexQuotient B.map.toCombinatorialMap =>
        ∃ d : D, d ∈ pathCutLeftHalfDarts B P ∧
          Quotient.mk (Equiv.Perm.SameCycle.setoid
            B.map.toCombinatorialMap.rot) d = v)]
    [rightHalfVerticesDecidable : DecidablePred
      (fun v : CombinatorialMap.VertexQuotient B.map.toCombinatorialMap =>
        ∃ d : D, d ∈ pathCutRightHalfDarts B P ∧
          Quotient.mk (Equiv.Perm.SameCycle.setoid
            B.map.toCombinatorialMap.rot) d = v)] :
    (pathCutLeftHalfMap B P).numVertices +
        (pathCutRightHalfMap B P).numVertices =
      B.map.toCombinatorialMap.numVertices + (n + 1) := by
  classical
  let instQ : Fintype
      (CombinatorialMap.VertexQuotient B.map.toCombinatorialMap) := inferInstance
  let L : Finset (CombinatorialMap.VertexQuotient B.map.toCombinatorialMap) :=
    Finset.univ.filter (fun v =>
    ∃ d : D, d ∈ pathCutLeftHalfDarts B P ∧
      Quotient.mk (Equiv.Perm.SameCycle.setoid
        B.map.toCombinatorialMap.rot) d = v)
  let R : Finset (CombinatorialMap.VertexQuotient B.map.toCombinatorialMap) :=
    Finset.univ.filter (fun v =>
    ∃ d : D, d ∈ pathCutRightHalfDarts B P ∧
      Quotient.mk (Equiv.Perm.SameCycle.setoid
        B.map.toCombinatorialMap.rot) d = v)
  have hleft := pathCutLeftHalfMap_numVertices B P
  have hright := pathCutRightHalfMap_numVertices B P
  have hUnion : L ∪ R = Finset.univ := by
    ext v
    simp only [L, R, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro _
      trivial
    · intro _
      exact pathCut_vertex_meets_a_closed_half B P v
  have hInter : L ∩ R = P.vertices.toFinset := by
    ext v
    simp only [L, R, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_univ, true_and, List.mem_toFinset]
    exact pathCut_vertex_meets_both_closed_halves_iff B P v
  have hpathCard : P.vertices.toFinset.card = n + 1 := by
    rw [List.toFinset_card_of_nodup P.vertices_nodup, P.vertices_length]
  calc
    (pathCutLeftHalfMap B P).numVertices +
        (pathCutRightHalfMap B P).numVertices =
        L.card + R.card := by
      rw [hleft, hright, Fintype.card_subtype, Fintype.card_subtype]
    _ = (L ∪ R).card + (L ∩ R).card := by
      rw [Finset.card_union_add_card_inter]
    _ = Fintype.card (CombinatorialMap.VertexQuotient
      B.map.toCombinatorialMap) + (n + 1) := by
      rw [hUnion, hInter, Finset.card_univ, hpathCard]
    _ = B.map.toCombinatorialMap.numVertices + (n + 1) := by
      unfold CombinatorialMap.numVertices
      let classicalDecRel : DecidableRel
          (Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot) :=
        fun a b => Classical.propDecidable _
      let instClassical : Fintype
          (CombinatorialMap.VertexQuotient B.map.toCombinatorialMap) :=
        @Quotient.fintype D (inferInstance : Fintype D)
          (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.rot)
          classicalDecRel
      change @Fintype.card
          (CombinatorialMap.VertexQuotient B.map.toCombinatorialMap) instQ +
          (n + 1) =
          @Fintype.card
            (CombinatorialMap.VertexQuotient B.map.toCombinatorialMap)
            instClassical + (n + 1)
      exact congrArg (fun k : ℕ => k + (n + 1))
        (@Fintype.card_congr
          (CombinatorialMap.VertexQuotient B.map.toCombinatorialMap)
          (CombinatorialMap.VertexQuotient B.map.toCombinatorialMap)
          instQ instClassical (Equiv.refl _))

end DirectedDistances.PlanarMap
