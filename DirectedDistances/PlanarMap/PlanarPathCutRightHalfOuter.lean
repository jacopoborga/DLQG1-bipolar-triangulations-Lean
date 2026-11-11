/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlanarPathCutRightHalfFaces
public import DirectedDistances.PlanarMap.PlanarPathCutRightBase

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

/-! # Marked outer face of the right path-cut half

paper result. -/

public section
namespace DirectedDistances.PlanarMap

open Equiv

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r n : ℕ}

/-- The right half map marked at the first dart of the lifted cut path.
paper result. -/
@[expose] noncomputable def pathCutRightHalfMarkedMap
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    DirectedMapWithMissing {d : D // d ∈ pathCutRightHalfDarts B P} := by
  classical
  let i : Fin (cutPathRightHalf B P).darts.length :=
    ⟨0, by
      rw [(cutPathRightHalf B P).darts_length]
      exact pathCutRightHalf_path_length_pos B P⟩
  let d : {d : D // d ∈ pathCutRightHalfDarts B P} :=
    (cutPathRightHalf B P).darts.get i
  exact { pathCutRightHalfDirectedMap B P with
    outer := d
    missing_outer := by intro e he; exact False.elim he }

/-- The marked map has the same combinatorial map as the unmarked half.
paper result. -/
theorem pathCutRightHalfMarkedMap_toCombinatorialMap
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    (pathCutRightHalfMarkedMap B P).toCombinatorialMap =
      (pathCutRightHalfDirectedMap B P).toCombinatorialMap := rfl

/-- The marked map carries the combinatorial half map from the face
construction. Helper toward `lem-lr-ind` -/
theorem pathCutRightHalfMarkedMap_toHalfMap
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    (pathCutRightHalfMarkedMap B P).toCombinatorialMap =
      pathCutRightHalfMap B P := rfl

/-- The marked map has no missing darts, as does the unmarked half.
paper result. -/
theorem pathCutRightHalfMarkedMap_missing
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (d : {d : D // d ∈ pathCutRightHalfDarts B P}) :
    (pathCutRightHalfMarkedMap B P).missing d =
      (pathCutRightHalfDirectedMap B P).missing d := rfl

/-- The marked map inherits the unmarked half's tail predicate.
paper result. -/
theorem pathCutRightHalfMarkedMap_tail
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (d : {d : D // d ∈ pathCutRightHalfDarts B P}) :
    (pathCutRightHalfMarkedMap B P).tail d =
      (pathCutRightHalfDirectedMap B P).tail d := rfl

/-- The marked and unmarked half maps have the same directed-step relation.
paper result. -/
theorem pathCutRightHalfMarkedMap_directedStep
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (v w : MapVertex (pathCutRightHalfDirectedMap B P)) :
    (pathCutRightHalfMarkedMap B P).directedStep v w ↔
      (pathCutRightHalfDirectedMap B P).directedStep v w := Iff.rfl

/-- The source and sink vertex types agree for the marked and unmarked maps.
paper result. -/
theorem pathCutRightHalfMarkedMap_vertexType
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    MapVertex (pathCutRightHalfMarkedMap B P) =
      MapVertex (pathCutRightHalfDirectedMap B P) := rfl

/-- The marked and unmarked maps give the same tail vertex to every dart.
paper result. -/
theorem pathCutRightHalfMarkedMap_dartTailVertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (d : {d : D // d ∈ pathCutRightHalfDarts B P}) :
    dartTailVertex (pathCutRightHalfMarkedMap B P) d =
      dartTailVertex (pathCutRightHalfDirectedMap B P) d := rfl

/-- The marked and unmarked maps give the same head vertex to every dart.
paper result. -/
theorem pathCutRightHalfMarkedMap_dartHeadVertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (d : {d : D // d ∈ pathCutRightHalfDarts B P}) :
    dartHeadVertex (pathCutRightHalfMarkedMap B P) d =
      dartHeadVertex (pathCutRightHalfDirectedMap B P) d := rfl

/-- Rebuild a half-map path with the marked map, preserving its data and
rechecking the edge-step fields. Helper toward `lem-lr-ind` -/
private noncomputable def pathCutRightHalfMarked_transportPath
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {k : ℕ}
    (Q : SimpleDirectedDartPath (pathCutRightHalfDirectedMap B P)
      (pathCutRightHalfSource B P) (pathCutRightHalfSink B P) k) :
    SimpleDirectedDartPath (pathCutRightHalfMarkedMap B P)
      (pathCutRightHalfSource B P) (pathCutRightHalfSink B P) k := by
  refine {
    darts := Q.darts
    vertices := Q.vertices
    darts_length := Q.darts_length
    vertices_length := Q.vertices_length
    vertices_nodup := Q.vertices_nodup
    start_vertex := Q.start_vertex
    end_vertex := Q.end_vertex
    edge_step := ?_ }
  intro i
  have hs := Q.edge_step i
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [pathCutRightHalfMarkedMap_missing] using hs.1
  · simpa only [pathCutRightHalfMarkedMap_tail] using hs.2.1
  · simpa only [pathCutRightHalfMarkedMap_vertexType,
      pathCutRightHalfMarkedMap_dartTailVertex] using hs.2.2.1
  · simpa only [pathCutRightHalfMarkedMap_vertexType,
      pathCutRightHalfMarkedMap_dartHeadVertex] using hs.2.2.2

/-- The cut path is also a path in the marked half map. The map change affects
only its outer-face marker. Helper toward `lem-lr-ind` -/
noncomputable def pathCutRightHalfMarked_leftPath
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    SimpleDirectedDartPath (pathCutRightHalfMarkedMap B P)
      (pathCutRightHalfSource B P) (pathCutRightHalfSink B P) n := by
  exact pathCutRightHalfMarked_transportPath B P (cutPathRightHalf B P)

/-- The right boundary path is also a path in the marked half map. The map
affects only its outer-face marker. Helper toward `lem-lr-ind` -/
noncomputable def pathCutRightHalfMarked_rightPath
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    SimpleDirectedDartPath (pathCutRightHalfMarkedMap B P)
      (pathCutRightHalfSource B P) (pathCutRightHalfSink B P) r := by
  exact pathCutRightHalfMarked_transportPath B P (rightPathHalf B P)

/-- The marked half map is acyclic. Helper toward `lem-lr-ind` -/
theorem pathCutRightHalfMarked_acyclic
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    (pathCutRightHalfMarkedMap B P).IsAcyclic := pathCutRightHalf_acyclic B P

/-- The marked half source has no incoming directed step. Helper toward -/
theorem pathCutRightHalfMarkedSource_isSource
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    ¬ ∃ u, (pathCutRightHalfMarkedMap B P).directedStep u
      (pathCutRightHalfSource B P) := by
  rintro ⟨u, hu⟩
  have hbase := pathCutRightHalf_directedStep_to_base B P hu
  rw [pathCutRightHalfSource_map] at hbase
  exact B.isSource ⟨pathCutRightHalfVertexMap B P u, hbase⟩

/-- The marked half sink has no outgoing directed step. Helper toward -/
theorem pathCutRightHalfMarkedSink_isSink
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    ¬ ∃ w, (pathCutRightHalfMarkedMap B P).directedStep
      (pathCutRightHalfSink B P) w := by
  rintro ⟨w, hw⟩
  have hbase := pathCutRightHalf_directedStep_to_base B P hw
  rw [pathCutRightHalfSink_map] at hbase
  exact B.isSink ⟨pathCutRightHalfVertexMap B P w, hbase⟩

/-- The chosen outer dart lies in the proposed boundary set of the half.
paper result. -/
theorem pathCutRightHalfMarked_outer_mem_boundary
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    (pathCutRightHalfMarkedMap B P).outer.1 ∈
      pathCutRightHalfBoundaryDarts B P := by
  classical
  let Q := cutPathRightHalf B P
  let i : Fin Q.darts.length :=
    ⟨0, by
      rw [Q.darts_length]
      exact pathCutRightHalf_path_length_pos B P⟩
  have hpath : (Q.darts.get i).1 ∈ P.darts := by
    have hmem : (Q.darts.get i).1 ∈ Q.darts.unattach := by
      change (Q.darts.get i).1 ∈ Q.darts.map Subtype.val
      exact List.mem_map.mpr ⟨Q.darts.get i, List.get_mem _ _, rfl⟩
    rw [← cutPathRightHalf_darts B P]
    exact hmem
  change (Q.darts.get i).1 ∈ pathCutRightHalfBoundaryDarts B P
  exact Or.inr hpath

/-- Outer membership in the marked map is exactly membership in the proposed
boundary set. Helper toward `lem-lr-ind` -/
theorem pathCutRightHalfMarked_isOuter_iff
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (d : {d : D // d ∈ pathCutRightHalfDarts B P}) :
    (pathCutRightHalfMarkedMap B P).IsOuter d ↔
      d.1 ∈ pathCutRightHalfBoundaryDarts B P := by
  classical
  obtain ⟨z, hz, hzc⟩ := pathCutRightHalf_boundary_single_orbit B P
  let m := (pathCutRightHalfMarkedMap B P).outer
  have hm : m.1 ∈ pathCutRightHalfBoundaryDarts B P :=
    pathCutRightHalfMarked_outer_mem_boundary B P
  have hzm : (pathCutRightHalfMap B P).faceSucc.SameCycle z m :=
    (hzc m).2 hm
  unfold DirectedMapWithMissing.IsOuter CombinatorialMap.IsOuter
  rw [pathCutRightHalfMarkedMap_toHalfMap]
  change (pathCutRightHalfMap B P).faceSucc.SameCycle m d ↔
    d.1 ∈ pathCutRightHalfBoundaryDarts B P
  constructor
  · intro h
    exact (hzc d).1 (hzm.trans h)
  · intro h
    exact hzm.symm.trans ((hzc d).2 h)

/-- Inner faces of the marked half map have degree three. Helper toward -/
theorem pathCutRightHalfMarked_innerFacesDegreeThree
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (d : {d : D // d ∈ pathCutRightHalfDarts B P})
    (houter : ¬ (pathCutRightHalfMarkedMap B P).IsOuter d) :
    (pathCutRightHalfMarkedMap B P).toCombinatorialMap.faceSucc
        ((pathCutRightHalfMarkedMap B P).toCombinatorialMap.faceSucc
          ((pathCutRightHalfMarkedMap B P).toCombinatorialMap.faceSucc d)) = d ∧
      (pathCutRightHalfMarkedMap B P).toCombinatorialMap.faceSucc d ≠ d ∧
      (pathCutRightHalfMarkedMap B P).toCombinatorialMap.faceSucc
          ((pathCutRightHalfMarkedMap B P).toCombinatorialMap.faceSucc d) ≠ d := by
  have hboundary : d.1 ∉ pathCutRightHalfBoundaryDarts B P :=
    fun hb => houter ((pathCutRightHalfMarked_isOuter_iff B P d).2 hb)
  simpa only [pathCutRightHalfMarkedMap_toHalfMap] using
    pathCutRightHalf_innerFacesDegreeThree B P d hboundary

private theorem pathCutRightHalfOuter_simplePath_darts_nodup
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (Q : SimpleDirectedDartPath M s t k) : Q.darts.Nodup := by
  apply List.nodup_iff_injective_get.mpr
  intro i j hij
  have hv := (Q.edge_step i).2.2.1.trans
    ((congrArg (dartTailVertex M) hij).trans (Q.edge_step j).2.2.1.symm)
  exact Fin.ext (congrArg (fun q : Fin Q.vertices.length => q.val)
    (Q.vertices_nodup.get_inj_iff.mp hv))

private theorem pathCutRightHalfOuter_simplePath_tail_of_mem
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (Q : SimpleDirectedDartPath M s t k) {d : D} (hd : d ∈ Q.darts) :
    M.tail d := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
  exact (Q.edge_step i).2.1

/-- The proposed outer word, traversing the cut path and then the reversed
opposite darts of the right path. Helper toward `lem-lr-ind` -/
@[expose] noncomputable def pathCutRightHalfOuterWord
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    NonemptyWord {d : D // d ∈ pathCutRightHalfDarts B P} where
  letters := (cutPathRightHalf B P).darts ++
    ((rightPathHalf B P).darts.reverse.map
      (pathCutRightHalfMap B P).edgeInv)
  nonempty := by
    intro h
    obtain ⟨hcut, _⟩ := List.append_eq_nil_iff.mp h
    have hzero : n = 0 := by
      rw [← (cutPathRightHalf B P).darts_length, hcut]
      rfl
    have hn : 0 < n := pathCutRightHalf_path_length_pos B P
    omega
  nodup := by
    apply List.nodup_append'.mpr
    refine ⟨pathCutRightHalfOuter_simplePath_darts_nodup (cutPathRightHalf B P), ?_, ?_⟩
    · apply List.Nodup.map (pathCutRightHalfMap B P).edgeInv.injective
      exact List.nodup_reverse.mpr
        (pathCutRightHalfOuter_simplePath_darts_nodup (rightPathHalf B P))
    · intro d hdCut hdRight
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hdRight
      have htail : (pathCutRightHalfDirectedMap B P).tail
          ((pathCutRightHalfMap B P).edgeInv e) :=
        pathCutRightHalfOuter_simplePath_tail_of_mem (cutPathRightHalf B P) hdCut
      have htailE : (pathCutRightHalfDirectedMap B P).tail e :=
        pathCutRightHalfOuter_simplePath_tail_of_mem (rightPathHalf B P)
          (List.mem_reverse.mp he)
      have hpresent : ¬ (pathCutRightHalfDirectedMap B P).missing e := by
        change ¬ False
        simp
      have hnot : ¬ (pathCutRightHalfDirectedMap B P).tail
          ((pathCutRightHalfDirectedMap B P).edgeInv e) :=
        ((pathCutRightHalfDirectedMap B P).tail_iff e hpresent).mp htailE
      exact hnot (by simpa only [pathCutRightHalfDirectedMap, closedHalfDirectedMap,
        pathCutRightHalfMap, closedHalfCombinatorialMap] using htail)

private theorem pathCutRightHalfOuter_rightArc_flip
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {p : D}
    (hp : p ∈ B.rightPath.darts) :
    B.map.edgeInv p ∈ pathCutRightOuterArc B := by
  apply (mem_pathCutRightOuterArc_iff B _).mpr
  exact List.mem_map.mpr ⟨p, List.mem_reverse.mpr hp, rfl⟩

private theorem pathCutRightHalfOuter_leftRightDarts_disjoint
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    Disjoint (pathCutLeftDarts B P) (pathCutRightDarts B P) := by
  obtain ⟨side, hl, hr, hf, he⟩ := pathCut_exists_side_coloring B P
  have hleft (d : D) (hd : d ∈ pathCutLeftDarts B P) : side d = true := by
    obtain ⟨a, ha, hreach⟩ := hd
    induction hreach with
    | refl => exact hl a ha
    | @tail b c _ hstep ih =>
        rcases hstep with ⟨rfl, hinner | ⟨_, hnext⟩⟩ | ⟨rfl, hseam⟩
        · exact (hf b hinner).trans ih
        · exact hl _ (.inl hnext)
        · exact (he b hseam).trans ih
  have hright (d : D) (hd : d ∈ pathCutRightDarts B P) : side d = false := by
    obtain ⟨a, ha, hreach⟩ := hd
    induction hreach with
    | refl => exact hr a ha
    | @tail b c _ hstep ih =>
        rcases hstep with ⟨rfl, hinner | ⟨_, hnext⟩⟩ | ⟨rfl, hseam⟩
        · exact (hf b hinner).trans ih
        · exact hr _ (.inl hnext)
        · exact (he b hseam).trans ih
  apply Set.disjoint_left.mpr
  intro d hd hd'
  have h := (hleft d hd).symm.trans (hright d hd')
  cases h

private theorem pathCutRightHalfOuter_boundary_iff_right_or_path
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) (d : D) :
    d ∈ pathCutRightHalfBoundaryDarts B P ↔
      (∃ p ∈ B.rightPath.darts, d = B.map.edgeInv p) ∨ d ∈ P.darts := by
  constructor
  · rintro (⟨hd, ho⟩ | hp)
    · rcases (isOuter_iff_mem_outerArcs B d).mp ho with hl | hr
      · have hdl : d ∈ pathCutLeftDarts B P :=
          ⟨d, Or.inl hl, Relation.ReflTransGen.refl⟩
        rcases hd with hd | (hp | hp)
        · exact (Set.disjoint_left.mp
            (pathCutRightHalfOuter_leftRightDarts_disjoint B P) hdl hd).elim
        · exact Or.inr hp
        · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
          have hn := (B.map.tail_iff _ (B.noMissingDarts _)).mp
            (P.edge_step i).2.1
          rw [hi, B.map.edgeInv_invol] at hn
          exact (hn hl.2.1).elim
      · obtain ⟨p, hp, hpd⟩ := List.mem_map.mp
          ((mem_pathCutRightOuterArc_iff B d).mp hr)
        exact Or.inl ⟨p, List.mem_reverse.mp hp, hpd.symm⟩
    · exact Or.inr hp
  · rintro (⟨p, hp, rfl⟩ | hp)
    · have ha := pathCutRightHalfOuter_rightArc_flip B hp
      exact Or.inl ⟨Or.inl ⟨_, Or.inl ha, Relation.ReflTransGen.refl⟩, ha.2.2⟩
    · exact Or.inr hp

private theorem pathCutRightHalfOuter_faceSucc_vertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (d : {d : D // d ∈ pathCutRightHalfDarts B P}) :
    dartTailVertex B.map ((pathCutRightHalfMap B P).faceSucc d).1 =
      dartHeadVertex B.map d.1 := by
  rw [pathCutRightHalf_faceSucc_eq_firstReturn]
  apply Quotient.sound
  change Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot
    ((B.map.toCombinatorialMap.rot.symm : D → D)^[firstReturnTime
      B.map.toCombinatorialMap.rot.symm (pathCutRightHalfDarts B P)
      ⟨B.map.toCombinatorialMap.edgeInv d.1,
        pathCutRightHalf_edgeInv_mem B P d.2⟩]
      (B.map.toCombinatorialMap.edgeInv d.1))
    (B.map.toCombinatorialMap.edgeInv d.1)
  rw [perm_iterate_eq_pow]
  have hsc : Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot.symm
      (B.map.toCombinatorialMap.edgeInv d.1)
      (B.map.toCombinatorialMap.edgeInv d.1) := Equiv.Perm.SameCycle.rfl
  exact (Equiv.Perm.SameCycle.pow_left hsc).of_inv

private theorem pathCutRightHalfOuter_right_boundary_faceSucc_get
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (i : ℕ) (hi : i + 1 < r) :
    B.map.toCombinatorialMap.faceSucc
        (B.map.edgeInv (B.rightPath.darts.get
          ⟨i + 1, by rw [B.rightPath.darts_length]; exact hi⟩)) =
      B.map.edgeInv (B.rightPath.darts.get
        ⟨i, by rw [B.rightPath.darts_length]; omega⟩) := by
  let xs := B.leftPath.darts ++ B.rightPath.darts.reverse.map B.map.edgeInv
  have hnodup : xs.Nodup := by
    simpa [xs] using B.outerSplit.2.1.perm.nodup_iff.mp B.outerWord.nodup
  have hlen : xs.length = ℓ + r := by
    simp [xs, B.leftPath.darts_length, B.rightPath.darts_length]
  have hget (k : ℕ) (hk : k < r) :
      xs[ℓ + (r - 1 - k)]'(by rw [hlen]; omega) =
        B.map.edgeInv (B.rightPath.darts.get
          ⟨k, by rw [B.rightPath.darts_length]; exact hk⟩) := by
    dsimp [xs]
    rw [List.getElem_append_right (by rw [B.leftPath.darts_length]; omega)]
    simp only [B.leftPath.darts_length, Nat.add_sub_cancel_left,
      List.getElem_map, List.getElem_reverse, B.rightPath.darts_length]
    apply congrArg B.map.edgeInv
    apply congrArg B.rightPath.darts.get
    apply Fin.ext
    change r - 1 - (r - 1 - k) = k
    omega
  let d := B.map.edgeInv (B.rightPath.darts.get
    ⟨i + 1, by rw [B.rightPath.darts_length]; exact hi⟩)
  have hdOuter : B.map.IsOuter d :=
    (pathCutRightHalfOuter_rightArc_flip B (List.get_mem _ _)).2.2
  have hdWord : d ∈ B.outerWord.letters :=
    (mem_iff_isOuter B.map B.outerWord B.outerSplit.1 d).mpr hdOuter
  have hface : B.map.toCombinatorialMap.faceSucc d = xs.formPerm d := by
    rw [B.outerSplit.1.2.2 d hdWord]
    simpa [xs] using congrArg (fun p : Perm D => p d)
      (List.formPerm_eq_of_isRotated B.outerWord.nodup B.outerSplit.2.1)
  let j := ℓ + (r - 1 - (i + 1))
  have hj : j < xs.length := by rw [hlen]; dsimp [j]; omega
  have hjnext : j + 1 = ℓ + (r - 1 - i) := by dsimp [j]; omega
  have hmod : (j + 1) % xs.length = j + 1 :=
    Nat.mod_eq_of_lt (by rw [hlen]; dsimp [j]; omega)
  change B.map.toCombinatorialMap.faceSucc d = _
  rw [hface]
  dsimp only [d]
  rw [← hget (i + 1) hi]
  change xs.formPerm (xs[j]'hj) = _
  rw [List.formPerm_apply_getElem xs hnodup j hj]
  simp only [hmod]
  simpa only [hjnext] using hget i (by omega)

private theorem pathCutRightHalfOuter_cut_get_val
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (i : ℕ) (hi : i < n) :
    ((cutPathRightHalf B P).darts.get
      ⟨i, by rw [(cutPathRightHalf B P).darts_length]; exact hi⟩).1 =
      P.darts.get ⟨i, by rw [P.darts_length]; exact hi⟩ := by
  let Q := cutPathRightHalf B P
  let d := Q.darts.get ⟨i, by rw [Q.darts_length]; exact hi⟩
  have hU : i < Q.darts.unattach.length := by
    simp only [List.length_unattach, Q.darts_length]
    exact hi
  have hP : i < P.darts.length := by rw [P.darts_length]; exact hi
  have hlist : Q.darts.unattach[i]'hU = P.darts[i]'hP := by
    have hopt : Q.darts.unattach[i]? = P.darts[i]? :=
      congrArg (fun xs : List D => xs[i]?) (cutPathRightHalf_darts B P)
    have hoptU : Q.darts.unattach[i]? = some (Q.darts.unattach[i]'hU) :=
      (List.getElem?_eq_some_iff).2 ⟨hU, rfl⟩
    have hoptP : P.darts[i]? = some (P.darts[i]'hP) :=
      (List.getElem?_eq_some_iff).2 ⟨hP, rfl⟩
    exact Option.some.inj (hoptU.symm.trans (hopt.trans hoptP))
  have hget := List.getElem_unattach (l := Q.darts) i hU
  simpa [d, List.get_eq_getElem] using hget.symm.trans hlist

private theorem pathCutRightHalfOuter_cut_faceSucc_get_of_next
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (i : ℕ) (hi : i < n) (hinext : i + 1 < n) :
    ((pathCutRightHalfMap B P).faceSucc
      ((cutPathRightHalf B P).darts.get
        ⟨i, by rw [(cutPathRightHalf B P).darts_length]; exact hi⟩)).1 =
      ((cutPathRightHalf B P).darts.get
        ⟨i + 1, by rw [(cutPathRightHalf B P).darts_length]; exact hinext⟩).1 := by
  let a : Fin P.darts.length := ⟨i, by rw [P.darts_length]; exact hi⟩
  let d : {d : D // d ∈ pathCutRightHalfDarts B P} :=
    (cutPathRightHalf B P).darts.get
      ⟨i, by rw [(cutPathRightHalf B P).darts_length]; exact hi⟩
  let e := (pathCutRightHalfMap B P).faceSucc d
  have hdval : d.1 = P.darts.get a := pathCutRightHalfOuter_cut_get_val B P i hi
  have hdB : d.1 ∈ pathCutRightHalfBoundaryDarts B P :=
    Or.inr (hdval ▸ List.get_mem _ a)
  have hr : 0 < r := B.right_length_pos
  obtain ⟨z, hz, hzc⟩ := pathCutRightHalf_boundary_single_orbit B P
  have hzd : (pathCutRightHalfMap B P).faceSucc.SameCycle z d :=
    (hzc d).2 hdB
  have hde : (pathCutRightHalfMap B P).faceSucc.SameCycle d e :=
    Equiv.Perm.SameCycle.rfl.apply_right
  have heB : e.1 ∈ pathCutRightHalfBoundaryDarts B P :=
    (hzc e).1 (hzd.trans hde)
  have hv : dartTailVertex B.map e.1 =
      dartHeadVertex B.map (P.darts.get a) := by
    calc
      dartTailVertex B.map e.1 = dartHeadVertex B.map d.1 :=
        pathCutRightHalfOuter_faceSucc_vertex B P d
      _ = dartHeadVertex B.map (P.darts.get a) := by rw [hdval]
  rcases (pathCutRightHalfOuter_boundary_iff_right_or_path B P e.1).mp heB
      with ⟨p, hp, hpe⟩ | hpath
  · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hp
    have hjlt : j.val < r := by
      simpa only [B.rightPath.darts_length] using j.isLt
    by_cases hjlast : j.val + 1 = r
    · have hverts : P.vertices.get ⟨i + 1, by
          rw [P.vertices_length]; omega⟩ =
        B.rightPath.vertices.get ⟨r, by
          rw [B.rightPath.vertices_length]; omega⟩ := by
        calc
          P.vertices.get ⟨i + 1, by rw [P.vertices_length]; omega⟩ =
              dartHeadVertex B.map (P.darts.get a) := (P.edge_step a).2.2.2
          _ = dartTailVertex B.map e.1 := hv.symm
          _ = dartTailVertex B.map (B.map.edgeInv p) := by rw [hpe]
          _ = dartHeadVertex B.map p := rfl
          _ = B.rightPath.vertices.get ⟨j.val + 1, by
              have hlenv : B.rightPath.vertices.length = r + 1 := by
                exact B.rightPath.vertices_length
              rw [hlenv]
              omega⟩ :=
            by simpa only [hj] using (B.rightPath.edge_step j).2.2.2.symm
          _ = B.rightPath.vertices.get ⟨r, by
            rw [B.rightPath.vertices_length]; omega⟩ := by
            exact congrArg B.rightPath.vertices.get
              (Fin.ext hjlast)
      have hsink : P.vertices.get ⟨i + 1, by
          rw [P.vertices_length]; omega⟩ = P.vertices.get ⟨n, by
          rw [P.vertices_length]; omega⟩ := by
        rw [P.end_vertex]
        calc
          P.vertices.get ⟨i + 1, by rw [P.vertices_length]; omega⟩ =
              B.rightPath.vertices.get ⟨r, by
                rw [B.rightPath.vertices_length]; omega⟩ := hverts
          _ = B.sink := B.rightPath.end_vertex
      have hfin := P.vertices_nodup.get_inj_iff.mp hsink
      have hiend : i + 1 = n := congrArg Fin.val hfin
      omega
    · have hji : j.val + 1 < r := by omega
      let k : Fin B.rightPath.darts.length := ⟨j.val + 1, by
        simpa only [B.rightPath.darts_length] using hji⟩
      let dp : {d : D // d ∈ pathCutRightHalfDarts B P} :=
        ⟨B.map.edgeInv (B.rightPath.darts.get k),
          Or.inl ⟨_, Or.inl (pathCutRightHalfOuter_rightArc_flip B
            (List.get_mem _ k)), Relation.ReflTransGen.refl⟩⟩
      have hnextArc :
          B.map.toCombinatorialMap.faceSucc
            (B.map.edgeInv (B.rightPath.darts.get k)) ∈ pathCutRightOuterArc B := by
        have hs := pathCutRightHalfOuter_right_boundary_faceSucc_get B j.val hji
        have hsucc : B.map.toCombinatorialMap.faceSucc
            (B.map.edgeInv (B.rightPath.darts.get k)) = B.map.edgeInv p := by
          simpa only [k, hj] using hs
        rw [hsucc]
        exact pathCutRightHalfOuter_rightArc_flip B hp
      have hdpval : ((pathCutRightHalfMap B P).faceSucc dp).1 = e.1 := by
        change ((pathCutRightHalfMap B P).faceSucc
          ⟨dp.1, dp.2⟩).1 = e.1
        rw [pathCutRightHalf_faceSucc_eq_base_of_rightOuterArc B P
          (pathCutRightHalfOuter_rightArc_flip B (List.get_mem _ k)) hnextArc]
        rw [pathCutRightHalfOuter_right_boundary_faceSucc_get B j.val (by omega)]
        rw [hj]
        exact hpe.symm
      have hpred : (pathCutRightHalfMap B P).faceSucc dp = e :=
        Subtype.ext hdpval
      have hdeq : dp = d := by
        apply (pathCutRightHalfMap B P).faceSucc.injective
        simpa [e] using hpred
      have hnot : ¬ B.map.tail dp.1 := by
        exact (B.map.tail_iff _ (B.noMissingDarts _)).mp
          (B.rightPath.edge_step k).2.1
      have htail : B.map.tail d.1 := by
        rw [hdval]
        exact (P.edge_step a).2.1
      exact (hnot (hdeq ▸ htail)).elim
  · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hpath
    have hjlt : j.val < n := by simpa only [P.darts_length] using j.isLt
    have hverts : P.vertices.get ⟨j.val, by rw [P.vertices_length]; omega⟩ =
        P.vertices.get ⟨i + 1, by rw [P.vertices_length]; omega⟩ := by
      calc
        P.vertices.get ⟨j.val, by rw [P.vertices_length]; omega⟩ =
            dartTailVertex B.map (P.darts.get j) :=
          (P.edge_step j).2.2.1
        _ = dartTailVertex B.map e.1 := by rw [hj]
        _ = dartHeadVertex B.map (P.darts.get a) := hv
        _ = P.vertices.get ⟨i + 1, by rw [P.vertices_length]; omega⟩ :=
          (P.edge_step a).2.2.2.symm
    have hidx := P.vertices_nodup.get_inj_iff.mp hverts
    have hjval : j.val = i + 1 := congrArg Fin.val hidx
    have hres : e.1 =
        ((cutPathRightHalf B P).darts.get
          ⟨i + 1, by rw [(cutPathRightHalf B P).darts_length]; exact hinext⟩).1 := by
      calc
        e.1 = P.darts.get j := hj.symm
        _ = P.darts.get ⟨i + 1, by rw [P.darts_length]; omega⟩ :=
          congrArg P.darts.get (Fin.ext hjval)
        _ = ((cutPathRightHalf B P).darts.get
            ⟨i + 1, by rw [(cutPathRightHalf B P).darts_length]; exact hinext⟩).1 :=
          (pathCutRightHalfOuter_cut_get_val B P (i + 1) hinext).symm
    exact hres

private theorem pathCutRightHalfOuter_cut_faceSucc_get_last
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (i : ℕ) (hi : i < n) (hilast : i + 1 = n) :
    ((pathCutRightHalfMap B P).faceSucc
      ((cutPathRightHalf B P).darts.get
        ⟨i, by rw [(cutPathRightHalf B P).darts_length]; exact hi⟩)).1 =
      B.map.edgeInv (B.rightPath.darts.get
        ⟨r - 1, by
          rw [B.rightPath.darts_length]
          have hr : 0 < r := B.right_length_pos
          omega⟩) := by
  let a : Fin P.darts.length := ⟨i, by rw [P.darts_length]; exact hi⟩
  let d : {d : D // d ∈ pathCutRightHalfDarts B P} :=
    (cutPathRightHalf B P).darts.get
      ⟨i, by rw [(cutPathRightHalf B P).darts_length]; exact hi⟩
  let e := (pathCutRightHalfMap B P).faceSucc d
  have hdval : d.1 = P.darts.get a := pathCutRightHalfOuter_cut_get_val B P i hi
  have hdB : d.1 ∈ pathCutRightHalfBoundaryDarts B P :=
    Or.inr (hdval ▸ List.get_mem _ a)
  have hr : 0 < r := B.right_length_pos
  obtain ⟨z, hz, hzc⟩ := pathCutRightHalf_boundary_single_orbit B P
  have hzd : (pathCutRightHalfMap B P).faceSucc.SameCycle z d :=
    (hzc d).2 hdB
  have heB : e.1 ∈ pathCutRightHalfBoundaryDarts B P :=
    (hzc e).1 (hzd.trans Equiv.Perm.SameCycle.rfl.apply_right)
  have hv : dartTailVertex B.map e.1 = B.sink := by
    calc
      dartTailVertex B.map e.1 = dartHeadVertex B.map d.1 :=
        pathCutRightHalfOuter_faceSucc_vertex B P d
      _ = dartHeadVertex B.map (P.darts.get a) := by rw [hdval]
      _ = P.vertices.get ⟨n, by rw [P.vertices_length]; omega⟩ := by
        calc
          dartHeadVertex B.map (P.darts.get a) =
              P.vertices.get ⟨a.val + 1, by
                rw [P.vertices_length]
                have ha : a.val = i := rfl
                omega⟩ :=
            (P.edge_step a).2.2.2.symm
          _ = P.vertices.get ⟨n, by rw [P.vertices_length]; omega⟩ := by
            congr 1
            exact Fin.ext (by simpa only [a] using hilast)
      _ = B.sink := P.end_vertex
  rcases (pathCutRightHalfOuter_boundary_iff_right_or_path B P e.1).mp heB
      with ⟨p, hp, hpe⟩ | hpath
  · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hp
    have hjlt : j.val < r := by
      simpa only [B.rightPath.darts_length] using j.isLt
    have hverts : B.rightPath.vertices.get ⟨j.val + 1, by
        have hlenv : B.rightPath.vertices.length = r + 1 :=
          B.rightPath.vertices_length
        rw [hlenv]
        omega⟩ = B.rightPath.vertices.get ⟨r, by
        rw [B.rightPath.vertices_length]; omega⟩ := by
      calc
        B.rightPath.vertices.get ⟨j.val + 1, by
            have hlenv : B.rightPath.vertices.length = r + 1 :=
              B.rightPath.vertices_length
            rw [hlenv]
            omega⟩ = dartHeadVertex B.map p :=
          by simpa only [hj] using (B.rightPath.edge_step j).2.2.2
        _ = dartTailVertex B.map e.1 := by rw [hpe]; rfl
        _ = B.sink := hv
        _ = B.rightPath.vertices.get ⟨r, by
            rw [B.rightPath.vertices_length]; omega⟩ := B.rightPath.end_vertex.symm
    have hfin := B.rightPath.vertices_nodup.get_inj_iff.mp hverts
    have hjend : j.val + 1 = r := congrArg Fin.val hfin
    have hjpred : j.val = r - 1 := by omega
    have hval : e.1 = B.map.edgeInv (B.rightPath.darts.get
        ⟨r - 1, by rw [B.rightPath.darts_length]; omega⟩) := by
      calc
        e.1 = B.map.edgeInv p := hpe
        _ = B.map.edgeInv (B.rightPath.darts.get j) :=
          congrArg B.map.edgeInv hj.symm
        _ = B.map.edgeInv (B.rightPath.darts.get
            ⟨r - 1, by rw [B.rightPath.darts_length]; omega⟩) := by
          congr 1
          exact congrArg B.rightPath.darts.get (Fin.ext hjpred)
    exact hval
  · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hpath
    have hjlt : j.val < n := by simpa only [P.darts_length] using j.isLt
    have hverts : P.vertices.get ⟨j.val, by
        rw [P.vertices_length]; omega⟩ = P.vertices.get ⟨n, by
        rw [P.vertices_length]; omega⟩ := by
      calc
        P.vertices.get ⟨j.val, by rw [P.vertices_length]; omega⟩ =
            dartTailVertex B.map (P.darts.get j) := (P.edge_step j).2.2.1
        _ = dartTailVertex B.map e.1 := by rw [hj]
        _ = B.sink := hv
        _ = P.vertices.get ⟨n, by rw [P.vertices_length]; omega⟩ := P.end_vertex.symm
    have hfin := P.vertices_nodup.get_inj_iff.mp hverts
    have hjend : j.val = n := congrArg Fin.val hfin
    omega

private theorem pathCutRightHalfOuter_reverseRight_unattach
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    ((rightPathHalf B P).darts.reverse.map
      (pathCutRightHalfMap B P).edgeInv).unattach =
      B.rightPath.darts.reverse.map B.map.edgeInv := by
  simp only [List.unattach, List.map_map, Function.comp_def,
    pathCutRightHalfMap, closedHalfCombinatorialMap, restrictedPerm_apply,
    List.map_reverse]
  rw [← rightPathHalf_darts B P]
  apply List.ext_get
  · simp
  · intro i h₁ h₂
    simp

private theorem pathCutRightHalfOuter_reverseRight_get_val
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (i : ℕ) (hi : i < r) :
    (((rightPathHalf B P).darts.reverse.map
        (pathCutRightHalfMap B P).edgeInv)[r - 1 - i]'(by
          rw [List.length_map, List.length_reverse,
            (rightPathHalf B P).darts_length]; omega)).1 =
      B.map.edgeInv
        (B.rightPath.darts[i]'(by rw [B.rightPath.darts_length]; exact hi)) := by
  have hleft : r - 1 - i <
      ((rightPathHalf B P).darts.reverse.map
        (pathCutRightHalfMap B P).edgeInv).unattach.length := by
    simp only [List.length_unattach, List.length_map, List.length_reverse,
      (rightPathHalf B P).darts_length]
    omega
  have hright : r - 1 - i <
      (B.rightPath.darts.reverse.map B.map.edgeInv).length := by
    simp only [List.length_map, List.length_reverse, B.rightPath.darts_length]
    omega
  have hopt := congrArg (fun xs : List D => xs[r - 1 - i]?)
    (pathCutRightHalfOuter_reverseRight_unattach B P)
  rw [List.getElem?_eq_getElem hleft, List.getElem?_eq_getElem hright] at hopt
  simp only [List.getElem_unattach, List.getElem_map] at hopt
  have hval := Option.some.inj hopt
  have hrev : r - 1 - i < B.rightPath.darts.reverse.length := by
    simpa only [List.length_reverse, B.rightPath.darts_length] using
      (show r - 1 - i < r by omega)
  rw [List.getElem_reverse (l := B.rightPath.darts)
    (i := r - 1 - i) hrev] at hval
  have hidx : B.rightPath.darts.length - 1 - (r - 1 - i) = i := by
    rw [B.rightPath.darts_length]
    omega
  simpa only [List.getElem_map, hidx] using hval

private theorem pathCutRightHalfOuter_right_boundary_faceSucc_get_half
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (i : ℕ) (hi : i + 1 < r)
    (d : {d : D // d ∈ pathCutRightHalfDarts B P})
    (hd : d.1 = B.map.edgeInv (B.rightPath.darts.get
      ⟨i + 1, by rw [B.rightPath.darts_length]; exact hi⟩)) :
    ((pathCutRightHalfMap B P).faceSucc d).1 =
      B.map.edgeInv (B.rightPath.darts.get
        ⟨i, by rw [B.rightPath.darts_length]; omega⟩) := by
  have hbase := pathCutRightHalfOuter_right_boundary_faceSucc_get B i hi
  have hnext : B.map.toCombinatorialMap.faceSucc d.1 ∈
      pathCutRightOuterArc B := by
    rw [hd, hbase]
    exact pathCutRightHalfOuter_rightArc_flip B (List.get_mem _ _)
  have hnext' : B.map.toCombinatorialMap.faceSucc
      (B.map.edgeInv (B.rightPath.darts.get
        ⟨i + 1, by rw [B.rightPath.darts_length]; exact hi⟩)) ∈
      pathCutRightOuterArc B := by simpa only [hd] using hnext
  let d' : {d : D // d ∈ pathCutRightHalfDarts B P} :=
    ⟨B.map.edgeInv (B.rightPath.darts.get
      ⟨i + 1, by rw [B.rightPath.darts_length]; exact hi⟩),
      Or.inl ⟨_, Or.inl (pathCutRightHalfOuter_rightArc_flip B
        (List.get_mem _ _)), Relation.ReflTransGen.refl⟩⟩
  have hdd : d = d' := Subtype.ext hd
  rw [hdd]
  rw [pathCutRightHalf_faceSucc_eq_base_of_rightOuterArc B P
    (pathCutRightHalfOuter_rightArc_flip B (List.get_mem _ _)) hnext']
  exact hbase

private theorem pathCutRightHalfOuter_source_junction
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    (pathCutRightHalfMap B P).faceSucc
        (((rightPathHalf B P).darts.reverse.map
          (pathCutRightHalfMap B P).edgeInv).get ⟨r - 1, by
            rw [List.length_map, List.length_reverse,
              (rightPathHalf B P).darts_length]
            have hr := B.right_length_pos
            omega⟩) =
      (cutPathRightHalf B P).darts.get ⟨0, by
        rw [(cutPathRightHalf B P).darts_length]
        exact pathCutRightHalf_path_length_pos B P⟩ := by
  classical
  let R := (rightPathHalf B P).darts.reverse.map
    (pathCutRightHalfMap B P).edgeInv
  have hr : 0 < r := B.right_length_pos
  let d := R.get ⟨r - 1, by
    dsimp [R]
    rw [List.length_map, List.length_reverse, (rightPathHalf B P).darts_length]
    have hr := B.right_length_pos
    omega⟩
  have hdval : d.1 = B.map.edgeInv (B.rightPath.darts.get
      ⟨0, by rw [B.rightPath.darts_length]; omega⟩) := by
    simpa [d, R, List.get_eq_getElem] using
      pathCutRightHalfOuter_reverseRight_get_val B P 0 (by omega)
  have hdB : d.1 ∈ pathCutRightHalfBoundaryDarts B P :=
    (pathCutRightHalfOuter_boundary_iff_right_or_path B P d.1).2
      (Or.inl ⟨B.rightPath.darts.get ⟨0, by
        rw [B.rightPath.darts_length]; omega⟩, List.get_mem _ _, hdval⟩)
  obtain ⟨z, hz, hzc⟩ := pathCutRightHalf_boundary_single_orbit B P
  have hzd : (pathCutRightHalfMap B P).faceSucc.SameCycle z d :=
    (hzc d).2 hdB
  let e := (pathCutRightHalfMap B P).faceSucc d
  have heB : e.1 ∈ pathCutRightHalfBoundaryDarts B P :=
    (hzc e).1 (hzd.trans Equiv.Perm.SameCycle.rfl.apply_right)
  have hv : dartTailVertex B.map e.1 = B.source := by
    calc
      dartTailVertex B.map e.1 = dartHeadVertex B.map d.1 :=
        pathCutRightHalfOuter_faceSucc_vertex B P d
      _ = dartHeadVertex B.map (B.map.edgeInv
          (B.rightPath.darts.get ⟨0, by rw [B.rightPath.darts_length]; omega⟩)) :=
        congrArg (dartHeadVertex B.map) hdval
      _ = B.source := by
        calc
          dartHeadVertex B.map (B.map.edgeInv
              (B.rightPath.darts.get ⟨0, by rw [B.rightPath.darts_length]; omega⟩)) =
              dartTailVertex B.map
                (B.rightPath.darts.get ⟨0, by rw [B.rightPath.darts_length]; omega⟩) := by
            simp [dartHeadVertex, dartTailVertex, B.map.edgeInv_invol]
          _ = B.rightPath.vertices.get ⟨0, by
              rw [B.rightPath.vertices_length]
              omega⟩ :=
            (B.rightPath.edge_step ⟨0, by
              rw [B.rightPath.darts_length]
              omega⟩).2.2.1.symm
          _ = B.source := B.rightPath.start_vertex
  rcases (pathCutRightHalfOuter_boundary_iff_right_or_path B P e.1).mp heB
      with ⟨p, hp, hpe⟩ | hp
  · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hp
    have hjlt : j.val < r := by
      simpa only [B.rightPath.darts_length] using j.isLt
    have hverts : B.rightPath.vertices.get ⟨j.val + 1, by
        rw [B.rightPath.vertices_length]
        omega⟩ = B.rightPath.vertices.get ⟨0, by
        rw [B.rightPath.vertices_length]
        omega⟩ := by
      calc
        B.rightPath.vertices.get ⟨j.val + 1, by
            rw [B.rightPath.vertices_length]
            omega⟩ = dartHeadVertex B.map p := by
          simpa only [hj] using (B.rightPath.edge_step j).2.2.2
        _ = dartTailVertex B.map e.1 := by rw [hpe]; rfl
        _ = B.source := hv
        _ = B.rightPath.vertices.get ⟨0, by
            rw [B.rightPath.vertices_length]
            omega⟩ := B.rightPath.start_vertex.symm
    have hfin := B.rightPath.vertices_nodup.get_inj_iff.mp hverts
    have hidx : j.val + 1 = 0 := congrArg Fin.val hfin
    omega
  · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hp
    have hjlt : j.val < n := by simpa only [P.darts_length] using j.isLt
    have hverts : P.vertices.get ⟨j.val, by
        rw [P.vertices_length]
        omega⟩ = P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩ := by
      calc
        P.vertices.get ⟨j.val, by rw [P.vertices_length]; omega⟩ =
            dartTailVertex B.map (P.darts.get j) := (P.edge_step j).2.2.1
        _ = dartTailVertex B.map e.1 := by rw [hj]
        _ = B.source := hv
        _ = P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩ := P.start_vertex.symm
    have hfin := P.vertices_nodup.get_inj_iff.mp hverts
    have hidx : j.val = 0 := congrArg Fin.val hfin
    have hval : e.1 = P.darts.get ⟨0, by rw [P.darts_length]; omega⟩ := by
      calc
        e.1 = P.darts.get j := hj.symm
        _ = P.darts.get ⟨0, by rw [P.darts_length]; omega⟩ :=
          congrArg P.darts.get (Fin.ext hidx)
    have hcutval : ((cutPathRightHalf B P).darts.get ⟨0, by
        rw [(cutPathRightHalf B P).darts_length]
        exact pathCutRightHalf_path_length_pos B P⟩).1 =
        P.darts.get ⟨0, by rw [P.darts_length]; omega⟩ :=
      pathCutRightHalfOuter_cut_get_val B P 0 (pathCutRightHalf_path_length_pos B P)
    apply Subtype.ext
    exact hval.trans hcutval.symm

private theorem pathCutRightHalfOuter_word_mem_boundary
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (d : {d : D // d ∈ pathCutRightHalfDarts B P}) :
    d ∈ (pathCutRightHalfOuterWord B P).letters ↔
      d.1 ∈ pathCutRightHalfBoundaryDarts B P := by
  let L := (cutPathRightHalf B P).darts
  let R := (rightPathHalf B P).darts.reverse.map
    (pathCutRightHalfMap B P).edgeInv
  change d ∈ L ++ R ↔ _
  rw [List.mem_append]
  constructor
  · rintro (hd | hd)
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
      have hi : i.val < n := by simpa only [L, (cutPathRightHalf B P).darts_length] using i.isLt
      have hval := pathCutRightHalfOuter_cut_get_val B P i.val hi
      let ip : Fin P.darts.length := ⟨i.val, by rw [P.darts_length]; exact hi⟩
      exact (pathCutRightHalfOuter_boundary_iff_right_or_path B P _).2
        (Or.inr (hval ▸ List.get_mem P.darts ip))
    · obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hd
      have hj : j.val < r := by simpa only [R, List.length_map,
        List.length_reverse, (rightPathHalf B P).darts_length] using j.isLt
      let k := r - 1 - j.val
      have hk : k < r := by dsimp [k]; omega
      have hval := pathCutRightHalfOuter_reverseRight_get_val B P k hk
      have hidx : r - 1 - k = j.val := by dsimp [k]; omega
      have hval' : (R.get j).1 = B.map.edgeInv (B.rightPath.darts.get
          ⟨k, by rw [B.rightPath.darts_length]; exact hk⟩) := by
        simpa only [R, List.get_eq_getElem, hidx] using hval
      exact (pathCutRightHalfOuter_boundary_iff_right_or_path B P _).2
        (Or.inl ⟨B.rightPath.darts.get ⟨k, by
          rw [B.rightPath.darts_length]
          exact hk⟩, List.get_mem _ _, hval'⟩)
  · intro hd
    rcases (pathCutRightHalfOuter_boundary_iff_right_or_path B P d.1).mp hd
      with ⟨p, hp, hval⟩ | hp
    · obtain ⟨k, hkp⟩ := List.mem_iff_get.mp hp
      have hk : k.val < r := by
        simpa only [B.rightPath.darts_length] using k.isLt
      have hk' : k.val < B.rightPath.darts.length := by
        simpa only [B.rightPath.darts_length] using hk
      let j : Fin R.length := ⟨r - 1 - k.val, by
        simp only [R, List.length_map, List.length_reverse,
          (rightPathHalf B P).darts_length]
        omega⟩
      have hval' : (R.get j).1 = B.map.edgeInv
          (B.rightPath.darts.get ⟨k.val, by
            exact hk'⟩) := by
        have h := pathCutRightHalfOuter_reverseRight_get_val B P k.val hk
        exact h
      have hkFin : (⟨k.val, hk'⟩ : Fin B.rightPath.darts.length) = k := by
        apply Fin.ext
        rfl
      have hval'' : (R.get j).1 = B.map.edgeInv p := by
        calc
          (R.get j).1 = B.map.edgeInv (B.rightPath.darts.get k) := by
            simpa only [hkFin] using hval'
          _ = B.map.edgeInv p := congrArg B.map.edgeInv hkp
      have heq : R.get j = d := Subtype.ext (hval''.trans hval.symm)
      exact Or.inr (List.mem_iff_get.mpr ⟨j, heq⟩)
    · obtain ⟨i, hpi⟩ := List.mem_iff_get.mp hp
      have hi : i.val < n := by simpa only [P.darts_length] using i.isLt
      let j : Fin L.length := ⟨i.val, by
        simp only [L, (cutPathRightHalf B P).darts_length]
        exact hi⟩
      have hval' : (L.get j).1 = P.darts.get i := by
        have h := pathCutRightHalfOuter_cut_get_val B P i.val hi
        simpa only [L, List.get_eq_getElem] using h
      have heq : L.get j = d := Subtype.ext (hval'.trans hpi)
      exact Or.inl (List.mem_iff_get.mpr ⟨j, heq⟩)

private theorem pathCutRightHalfOuter_rightPathHalf_faceSucc_get
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (j : ℕ) (hj : j + 1 < r) :
    (pathCutRightHalfMap B P).faceSucc
        (((rightPathHalf B P).darts.reverse.map
          (pathCutRightHalfMap B P).edgeInv).get ⟨j, by
            rw [List.length_map, List.length_reverse,
              (rightPathHalf B P).darts_length]
            omega⟩) =
      ((rightPathHalf B P).darts.reverse.map
        (pathCutRightHalfMap B P).edgeInv).get ⟨j + 1, by
          rw [List.length_map, List.length_reverse,
            (rightPathHalf B P).darts_length]
          omega⟩ := by
  let R := (rightPathHalf B P).darts.reverse.map
    (pathCutRightHalfMap B P).edgeInv
  let d := R.get ⟨j, by
    dsimp [R]
    rw [List.length_map, List.length_reverse, (rightPathHalf B P).darts_length]
    omega⟩
  have hval : d.1 = B.map.edgeInv (B.rightPath.darts.get ⟨r - 1 - j, by
      rw [B.rightPath.darts_length]
      omega⟩) := by
    have h := pathCutRightHalfOuter_reverseRight_get_val B P (r - 1 - j) (by omega)
    have hjidx : r - 1 - (r - 1 - j) = j := by omega
    simpa only [d, R, List.get_eq_getElem, hjidx] using h
  have hvalFor : d.1 = B.map.edgeInv (B.rightPath.darts.get
      ⟨r - 2 - j + 1, by rw [B.rightPath.darts_length]; omega⟩) := by
    have hidx : r - 2 - j + 1 = r - 1 - j := by omega
    simpa only [hidx] using hval
  have hface := pathCutRightHalfOuter_right_boundary_faceSucc_get_half B P
    (r - 2 - j) (by omega) d hvalFor
  have hval' : (R.get ⟨j + 1, by
      dsimp [R]
      rw [List.length_map, List.length_reverse, (rightPathHalf B P).darts_length]
      omega⟩).1 = B.map.edgeInv (B.rightPath.darts.get ⟨r - 2 - j, by
        rw [B.rightPath.darts_length]
        omega⟩) := by
    have h := pathCutRightHalfOuter_reverseRight_get_val B P (r - 2 - j) (by omega)
    have hidx : r - 1 - (r - 2 - j) = j + 1 := by omega
    simpa only [R, List.get_eq_getElem, hidx] using h
  apply Subtype.ext
  exact hface.trans hval'.symm

private theorem pathCutRightHalfOuter_word_faceSucc_get
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (i : ℕ) (hi : i < (pathCutRightHalfOuterWord B P).letters.length) :
    (pathCutRightHalfMap B P).faceSucc
        (pathCutRightHalfOuterWord B P).letters[i] =
      (pathCutRightHalfOuterWord B P).letters[(i + 1) %
        (pathCutRightHalfOuterWord B P).letters.length]'(Nat.mod_lt _ (by omega)) := by
  let L := (cutPathRightHalf B P).darts
  let R := (rightPathHalf B P).darts.reverse.map
    (pathCutRightHalfMap B P).edgeInv
  have hword : (pathCutRightHalfOuterWord B P).letters = L ++ R := rfl
  have hLlen : L.length = n := (cutPathRightHalf B P).darts_length
  have hRlen : R.length = r := by
    simp only [R, List.length_map, List.length_reverse,
      (rightPathHalf B P).darts_length]
  have hlen : (L ++ R).length = n + r := by
    simp only [List.length_append, hLlen, hRlen]
  have hnpos : 0 < n := pathCutRightHalf_path_length_pos B P
  have hrpos : 0 < r := B.right_length_pos
  have hiLC : i < (L ++ R).length := by rw [← hword]; exact hi
  change (pathCutRightHalfMap B P).faceSucc ((L ++ R)[i]'hiLC) =
    (L ++ R)[(i + 1) % (L ++ R).length]'(Nat.mod_lt _ (by omega))
  by_cases hleft : i < n
  · simp only [List.getElem_append_left (as := L) (bs := R) (i := i) (by omega)]
    by_cases hnext : i + 1 < n
    · have hmod : (i + 1) % (L ++ R).length = i + 1 := Nat.mod_eq_of_lt (by omega)
      simp only [hmod,
        List.getElem_append_left (as := L) (bs := R) (i := i + 1) (by omega)]
      apply Subtype.ext
      exact pathCutRightHalfOuter_cut_faceSucc_get_of_next B P i (by omega) hnext
    · have hlast : i + 1 = n := by omega
      have hmod : (i + 1) % (L ++ R).length = n := by
        have hlt : i + 1 < (L ++ R).length := by rw [hlen]; omega
        rw [Nat.mod_eq_of_lt hlt]
        exact hlast
      have hidx : i = n - 1 := by omega
      simp only [hmod]
      simp only [List.getElem_append_right (as := L) (bs := R) (i := n) (by omega)]
      simp only [hLlen, Nat.sub_self]
      simp only [hidx]
      apply Subtype.ext
      have hcut := pathCutRightHalfOuter_cut_faceSucc_get_last B P (n - 1)
        (by have hn := pathCutRightHalf_path_length_pos B P; omega) (by omega)
      have hR0val : (R.get ⟨0, by rw [hRlen]; omega⟩).1 =
          B.map.edgeInv (B.rightPath.darts.get ⟨r - 1, by
            rw [B.rightPath.darts_length]
            omega⟩) := by
        have h := pathCutRightHalfOuter_reverseRight_get_val B P (r - 1) (by omega)
        simpa only [R, List.get_eq_getElem, Nat.sub_self] using h
      exact hcut.trans hR0val.symm
  · simp only [List.getElem_append_right (as := L) (bs := R) (i := i) (by omega)]
    have hj : i - n < r := by omega
    by_cases hnext : i - n + 1 < r
    · have hmod : (i + 1) % (L ++ R).length = i + 1 := Nat.mod_eq_of_lt (by omega)
      simp only [hmod]
      simp only [List.getElem_append_right (as := L) (bs := R) (i := i + 1) (by omega)]
      simp only [hLlen]
      have hsucc := pathCutRightHalfOuter_rightPathHalf_faceSucc_get B P (i - n) hnext
      have hidx : i + 1 - n = i - n + 1 := by omega
      simpa only [List.get_eq_getElem, hidx] using hsucc
    · have hlast : i - n + 1 = r := by omega
      have hmod : (i + 1) % (L ++ R).length = 0 := by
        have heq : i + 1 = (L ++ R).length := by rw [hlen]; omega
        rw [heq, Nat.mod_self]
      have hidx : i - n = r - 1 := by omega
      simp only [hmod]
      simp only [List.getElem_append_left (as := L) (bs := R) (i := 0) (by omega)]
      simp only [hLlen]
      simp only [hidx]
      simpa only [List.get_eq_getElem] using pathCutRightHalfOuter_source_junction B P



theorem pathCutRightHalfMarked_isOuterCycle
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    IsOuterCycle (pathCutRightHalfMarkedMap B P) (pathCutRightHalfOuterWord B P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    exact (pathCutRightHalfMarked_isOuter_iff B P d).mpr
      ((pathCutRightHalfOuter_word_mem_boundary B P d).mp hd)
  · intro d hd
    exact (pathCutRightHalfOuter_word_mem_boundary B P d).mpr
      ((pathCutRightHalfMarked_isOuter_iff B P d).mp hd)
  · intro d hd
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
    change (pathCutRightHalfMap B P).faceSucc
        (pathCutRightHalfOuterWord B P).letters[i.val] =
      (pathCutRightHalfOuterWord B P).letters.formPerm
        (pathCutRightHalfOuterWord B P).letters[i.val]
    rw [List.formPerm_apply_getElem _ (pathCutRightHalfOuterWord B P).nodup]
    exact pathCutRightHalfOuter_word_faceSucc_get B P i.val i.isLt




theorem pathCutRightHalfMarked_outerSplit
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    FourArcsWitness (pathCutRightHalfMarkedMap B P) (pathCutRightHalfOuterWord B P)
      (pathCutRightHalfMarked_leftPath B P).darts []
      ((pathCutRightHalfMarked_rightPath B P).darts.reverse.map
        (pathCutRightHalfMarkedMap B P).toCombinatorialMap.edgeInv) [] := by
  let L := (pathCutRightHalfMarked_leftPath B P).darts
  let R := (pathCutRightHalfMarked_rightPath B P).darts.reverse.map
    (pathCutRightHalfMarkedMap B P).toCombinatorialMap.edgeInv
  have he : (pathCutRightHalfOuterWord B P).letters = L ++ R := rfl
  have hm (d : {d : D // d ∈ pathCutRightHalfDarts B P}) :
      (pathCutRightHalfMarkedMap B P).IsOuter d ↔ d ∈ L ∨ d ∈ R := by
    rw [← mem_iff_isOuter _ _ (pathCutRightHalfMarked_isOuterCycle B P)]
    rw [he, List.mem_append]
  have hmissing (d : {d : D // d ∈ pathCutRightHalfDarts B P}) :
      ¬ (pathCutRightHalfMarkedMap B P).missing d := by
    change ¬ False
    exact not_false
  have hleft (d : {d : D // d ∈ pathCutRightHalfDarts B P}) (hd : d ∈ L) :
      (pathCutRightHalfMarkedMap B P).tail d :=
    pathCutRightHalfOuter_simplePath_tail_of_mem
      (pathCutRightHalfMarked_leftPath B P) hd
  have hright (d : {d : D // d ∈ pathCutRightHalfDarts B P}) (hd : d ∈ R) :
      ¬ (pathCutRightHalfMarkedMap B P).tail d := by
    obtain ⟨e, he', rfl⟩ := List.mem_map.mp hd
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp (List.mem_reverse.mp he')
    have htail : (pathCutRightHalfDirectedMap B P).tail e :=
      pathCutRightHalfOuter_simplePath_tail_of_mem
        (pathCutRightHalfMarked_rightPath B P)
        (List.mem_iff_get.mpr ⟨i, hi⟩)
    have hpresent : ¬ (pathCutRightHalfDirectedMap B P).missing e := by
      change ¬ False
      simp
    have hnot : ¬ (pathCutRightHalfDirectedMap B P).tail
        ((pathCutRightHalfMap B P).edgeInv e) :=
      ((pathCutRightHalfDirectedMap B P).tail_iff e hpresent).mp htail
    intro ht
    have ht' : (pathCutRightHalfDirectedMap B P).tail
        ((pathCutRightHalfMap B P).edgeInv e) := by
      simpa only [pathCutRightHalfMarkedMap_tail,
        pathCutRightHalfMarkedMap_toHalfMap] using ht
    exact hnot ht'
  refine ⟨pathCutRightHalfMarked_isOuterCycle B P, ?_, ?_, ?_, ?_, ?_⟩
  · change List.IsRotated (L ++ R) (L ++ [] ++ R ++ [])
    simpa only [List.append_nil, List.nil_append] using List.IsRotated.refl (L ++ R)
  · intro d
    constructor
    · intro hd
      exact ⟨hmissing d, hleft d hd, (hm d).mpr (.inl hd)⟩
    · rintro ⟨_, ht, ho⟩
      rcases (hm d).mp ho with hd | hd
      · exact hd
      · exact (hright d hd ht).elim
  · intro d
    constructor
    · intro hd
      exact ⟨hmissing d, hright d hd, (hm d).mpr (.inr hd)⟩
    · rintro ⟨_, ht, ho⟩
      rcases (hm d).mp ho with hd | hd
      · exact (ht (hleft d hd)).elim
      · exact hd
  · intro d hd
    exact False.elim (List.not_mem_nil hd)
  · intro d hd
    exact False.elim (List.not_mem_nil hd)

end DirectedDistances.PlanarMap
