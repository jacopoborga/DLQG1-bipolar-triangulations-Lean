/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlanarPathCutHalfFaces
public import DirectedDistances.PlanarMap.PlanarPathCutLeftBase

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

/-! # Marked outer face of the left path-cut half

paper result. The outer dart is selected from the proposed boundary of the
left half. -/

public section
namespace DirectedDistances.PlanarMap

open Equiv

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r n : ℕ}

/-- The left half map marked at the first dart of its left boundary path.
paper result. -/
@[expose] noncomputable def pathCutLeftHalfMarkedMap
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    DirectedMapWithMissing {d : D // d ∈ pathCutLeftHalfDarts B P} := by
  classical
  let i : Fin B.leftPath.darts.length :=
    ⟨0, by rw [B.leftPath.darts_length]; exact Nat.lt_of_lt_of_le Nat.zero_lt_one B.left_length_pos⟩
  let d : {d : D // d ∈ pathCutLeftHalfDarts B P} :=
    ⟨B.leftPath.darts.get i,
      pathCutLeftHalf_leftPath_mem B P (List.get_mem _ _)⟩
  exact { pathCutLeftHalfDirectedMap B P with
    outer := d
    missing_outer := by intro e he; exact False.elim he }

/-- The marked map has the same combinatorial map as the unmarked half.
paper result. -/
theorem pathCutLeftHalfMarkedMap_toCombinatorialMap
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    (pathCutLeftHalfMarkedMap B P).toCombinatorialMap =
      (pathCutLeftHalfDirectedMap B P).toCombinatorialMap := rfl

/-- The marked map carries the combinatorial half map from the face
construction. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalfMarkedMap_toHalfMap
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    (pathCutLeftHalfMarkedMap B P).toCombinatorialMap =
      pathCutLeftHalfMap B P := rfl

/-- The marked map has no missing darts, as does the unmarked half.
paper result. -/
theorem pathCutLeftHalfMarkedMap_missing
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
    (pathCutLeftHalfMarkedMap B P).missing d =
      (pathCutLeftHalfDirectedMap B P).missing d := rfl

/-- The marked map inherits the unmarked half's tail predicate.
paper result. -/
theorem pathCutLeftHalfMarkedMap_tail
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
    (pathCutLeftHalfMarkedMap B P).tail d =
      (pathCutLeftHalfDirectedMap B P).tail d := rfl

/-- The marked and unmarked half maps have the same directed-step relation.
paper result. -/
theorem pathCutLeftHalfMarkedMap_directedStep
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (v w : MapVertex (pathCutLeftHalfDirectedMap B P)) :
    (pathCutLeftHalfMarkedMap B P).directedStep v w ↔
      (pathCutLeftHalfDirectedMap B P).directedStep v w := Iff.rfl

/-- The source and sink vertex types agree for the marked and unmarked maps.
paper result. -/
theorem pathCutLeftHalfMarkedMap_vertexType
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    MapVertex (pathCutLeftHalfMarkedMap B P) =
      MapVertex (pathCutLeftHalfDirectedMap B P) := rfl

/-- The marked and unmarked maps give the same tail vertex to every dart.
paper result. -/
theorem pathCutLeftHalfMarkedMap_dartTailVertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
    dartTailVertex (pathCutLeftHalfMarkedMap B P) d =
      dartTailVertex (pathCutLeftHalfDirectedMap B P) d := rfl

/-- The marked and unmarked maps give the same head vertex to every dart.
paper result. -/
theorem pathCutLeftHalfMarkedMap_dartHeadVertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
    dartHeadVertex (pathCutLeftHalfMarkedMap B P) d =
      dartHeadVertex (pathCutLeftHalfDirectedMap B P) d := rfl

/-- Rebuild a half-map path with the marked map, preserving its data and
rechecking the edge-step fields. Helper toward `lem-lr-ind` -/
private noncomputable def pathCutLeftHalfMarked_transportPath
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {k : ℕ}
    (Q : SimpleDirectedDartPath (pathCutLeftHalfDirectedMap B P)
      (pathCutLeftHalfSource B P) (pathCutLeftHalfSink B P) k) :
    SimpleDirectedDartPath (pathCutLeftHalfMarkedMap B P)
      (pathCutLeftHalfSource B P) (pathCutLeftHalfSink B P) k := by
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
  · simpa only [pathCutLeftHalfMarkedMap_missing] using hs.1
  · simpa only [pathCutLeftHalfMarkedMap_tail] using hs.2.1
  · simpa only [pathCutLeftHalfMarkedMap_vertexType,
      pathCutLeftHalfMarkedMap_dartTailVertex] using hs.2.2.1
  · simpa only [pathCutLeftHalfMarkedMap_vertexType,
      pathCutLeftHalfMarkedMap_dartHeadVertex] using hs.2.2.2

/-- The left boundary path is also a path in the marked half map. The map
change affects only its outer-face marker. Helper toward `lem-lr-ind` -/
noncomputable def pathCutLeftHalfMarked_leftPath
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    SimpleDirectedDartPath (pathCutLeftHalfMarkedMap B P)
      (pathCutLeftHalfSource B P) (pathCutLeftHalfSink B P) ℓ := by
  exact pathCutLeftHalfMarked_transportPath B P (leftPathHalf B P)

/-- The cut path is also a path in the marked half map. The map change
affects only its outer-face marker. Helper toward `lem-lr-ind` -/
noncomputable def pathCutLeftHalfMarked_cutPath
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    SimpleDirectedDartPath (pathCutLeftHalfMarkedMap B P)
      (pathCutLeftHalfSource B P) (pathCutLeftHalfSink B P) n := by
  exact pathCutLeftHalfMarked_transportPath B P (cutPathHalf B P)

/-- The marked half map is acyclic. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalfMarked_acyclic
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    (pathCutLeftHalfMarkedMap B P).IsAcyclic := pathCutLeftHalf_acyclic B P

/-- The marked half source has no incoming directed step. Helper toward -/
theorem pathCutLeftHalfMarkedSource_isSource
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    ¬ ∃ u, (pathCutLeftHalfMarkedMap B P).directedStep u
      (pathCutLeftHalfSource B P) := pathCutLeftHalfSource_isSource B P

/-- The marked half sink has no outgoing directed step. Helper toward -/
theorem pathCutLeftHalfMarkedSink_isSink
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    ¬ ∃ w, (pathCutLeftHalfMarkedMap B P).directedStep
      (pathCutLeftHalfSink B P) w := pathCutLeftHalfSink_isSink B P

/-- The chosen outer dart lies in the proposed boundary set of the half.
paper result. -/
theorem pathCutLeftHalfMarked_outer_mem_boundary
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    (pathCutLeftHalfMarkedMap B P).outer.1 ∈
      pathCutLeftHalfBoundaryDarts B P := by
  classical
  let i : Fin B.leftPath.darts.length :=
    ⟨0, by rw [B.leftPath.darts_length]; exact Nat.lt_of_lt_of_le Nat.zero_lt_one B.left_length_pos⟩
  have hleft : B.leftPath.darts.get i ∈ B.leftPath.darts := List.get_mem _ _
  have houter : B.map.IsOuter (B.leftPath.darts.get i) :=
    (B.outerSplit.2.2.1 _).mp hleft |>.2.2
  change (B.leftPath.darts.get i) ∈ pathCutLeftHalfBoundaryDarts B P
  exact Or.inl ⟨pathCutLeftHalf_leftPath_mem B P hleft, houter⟩

/-- Outer membership in the marked map is exactly membership in the proposed
boundary set. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalfMarked_isOuter_iff
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
    (pathCutLeftHalfMarkedMap B P).IsOuter d ↔
      d.1 ∈ pathCutLeftHalfBoundaryDarts B P := by
  classical
  obtain ⟨z, hz, hzc⟩ := pathCutLeftHalf_boundary_single_orbit B P
  let m := (pathCutLeftHalfMarkedMap B P).outer
  have hm : m.1 ∈ pathCutLeftHalfBoundaryDarts B P :=
    pathCutLeftHalfMarked_outer_mem_boundary B P
  have hzm : (pathCutLeftHalfMap B P).faceSucc.SameCycle z m :=
    (hzc m).2 hm
  unfold DirectedMapWithMissing.IsOuter CombinatorialMap.IsOuter
  rw [pathCutLeftHalfMarkedMap_toHalfMap]
  change (pathCutLeftHalfMap B P).faceSucc.SameCycle m d ↔
    d.1 ∈ pathCutLeftHalfBoundaryDarts B P
  constructor
  · intro h
    exact (hzc d).1 (hzm.trans h)
  · intro h
    exact hzm.symm.trans ((hzc d).2 h)

/-- Inner faces of the marked half map have degree three. Helper toward -/
theorem pathCutLeftHalfMarked_innerFacesDegreeThree
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P})
    (houter : ¬ (pathCutLeftHalfMarkedMap B P).IsOuter d) :
    (pathCutLeftHalfMarkedMap B P).toCombinatorialMap.faceSucc
        ((pathCutLeftHalfMarkedMap B P).toCombinatorialMap.faceSucc
          ((pathCutLeftHalfMarkedMap B P).toCombinatorialMap.faceSucc d)) = d ∧
      (pathCutLeftHalfMarkedMap B P).toCombinatorialMap.faceSucc d ≠ d ∧
      (pathCutLeftHalfMarkedMap B P).toCombinatorialMap.faceSucc
          ((pathCutLeftHalfMarkedMap B P).toCombinatorialMap.faceSucc d) ≠ d := by
  have hboundary : d.1 ∉ pathCutLeftHalfBoundaryDarts B P :=
    fun hb => houter ((pathCutLeftHalfMarked_isOuter_iff B P d).2 hb)
  simpa only [pathCutLeftHalfMarkedMap_toHalfMap] using
    pathCutLeftHalf_innerFacesDegreeThree B P d hboundary

private theorem pathCutLeftHalfOuter_simplePath_darts_nodup
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (Q : SimpleDirectedDartPath M s t k) : Q.darts.Nodup := by
  apply List.nodup_iff_injective_get.mpr
  intro i j hij
  have hv := (Q.edge_step i).2.2.1.trans
    ((congrArg (dartTailVertex M) hij).trans (Q.edge_step j).2.2.1.symm)
  exact Fin.ext (congrArg (fun q : Fin Q.vertices.length => q.val)
    (Q.vertices_nodup.get_inj_iff.mp hv))

private theorem pathCutLeftHalfOuter_simplePath_tail_of_mem
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (Q : SimpleDirectedDartPath M s t k) {d : D} (hd : d ∈ Q.darts) :
    M.tail d := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
  exact (Q.edge_step i).2.1

private theorem pathCutLeftHalfOuter_leftRight_disjoint
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

private theorem pathCutLeftHalfOuter_boundary_iff_left_or_reverse
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) (d : D) :
    d ∈ pathCutLeftHalfBoundaryDarts B P ↔
      d ∈ B.leftPath.darts ∨
        ∃ p ∈ P.darts, d = B.map.toCombinatorialMap.edgeInv p := by
  constructor
  · rintro (⟨hd, ho⟩ | hr)
    · rcases (isOuter_iff_mem_outerArcs B d).mp ho with hl | hright
      · exact Or.inl ((mem_pathCutLeftOuterArc_iff B d).mp hl)
      · have hdr : d ∈ pathCutRightDarts B P :=
          ⟨d, Or.inl hright, Relation.ReflTransGen.refl⟩
        rcases hd with hd | (hp | hp)
        · exact (Set.disjoint_left.mp
            (pathCutLeftHalfOuter_leftRight_disjoint B P) hd hdr).elim
        · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
          exact (hright.2.1 (P.edge_step i).2.1).elim
        · exact Or.inr ⟨B.map.toCombinatorialMap.edgeInv d, hp,
            (B.map.toCombinatorialMap.edgeInv_invol d).symm⟩
    · exact Or.inr hr
  · rintro (hl | hr)
    · have ha := (mem_pathCutLeftOuterArc_iff B d).mpr hl
      exact Or.inl ⟨Or.inl ⟨d, Or.inl ha, Relation.ReflTransGen.refl⟩,
        ha.2.2⟩
    · exact Or.inr hr

private theorem pathCutLeftHalfOuter_faceSucc_vertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
    dartTailVertex B.map ((pathCutLeftHalfMap B P).faceSucc d).1 =
      dartHeadVertex B.map d.1 := by
  rw [pathCutLeftHalf_faceSucc_eq_firstReturn]
  apply Quotient.sound
  change Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot
    ((B.map.toCombinatorialMap.rot.symm : D → D)^[firstReturnTime
      B.map.toCombinatorialMap.rot.symm (pathCutLeftHalfDarts B P)
      ⟨B.map.toCombinatorialMap.edgeInv d.1,
        pathCutLeftHalf_edgeInv_mem B P d.2⟩]
      (B.map.toCombinatorialMap.edgeInv d.1))
    (B.map.toCombinatorialMap.edgeInv d.1)
  rw [perm_iterate_eq_pow]
  have hsc : Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot.symm
      (B.map.toCombinatorialMap.edgeInv d.1)
      (B.map.toCombinatorialMap.edgeInv d.1) := Equiv.Perm.SameCycle.rfl
  exact (Equiv.Perm.SameCycle.pow_left hsc).of_inv

private theorem pathCutLeftHalfOuter_left_boundary_faceSucc_get
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (i : ℕ) (hi : i + 1 < ℓ) :
    B.map.toCombinatorialMap.faceSucc
        (B.leftPath.darts.get ⟨i, by rw [B.leftPath.darts_length]; omega⟩) =
      B.leftPath.darts.get ⟨i + 1, by rw [B.leftPath.darts_length]; omega⟩ := by
  let xs := B.leftPath.darts ++
    B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv
  have hnodup : xs.Nodup := by
    simpa [xs] using B.outerSplit.2.1.perm.nodup_iff.mp B.outerWord.nodup
  have hlen : xs.length = ℓ + r := by
    simp [xs, B.leftPath.darts_length, B.rightPath.darts_length]
  let d := B.leftPath.darts.get ⟨i,
    by rw [B.leftPath.darts_length]; omega⟩
  have hdOuter : B.map.IsOuter d :=
    ((B.outerSplit.2.2.1 d).mp (List.get_mem _ _)).2.2
  have hdWord : d ∈ B.outerWord.letters :=
    (mem_iff_isOuter B.map B.outerWord B.outerSplit.1 d).mpr hdOuter
  have hface : B.map.toCombinatorialMap.faceSucc d = xs.formPerm d := by
    rw [B.outerSplit.1.2.2 d hdWord]
    simpa [xs] using congrArg (fun p : Equiv.Perm D => p d)
      (List.formPerm_eq_of_isRotated B.outerWord.nodup B.outerSplit.2.1)
  have hidx : d = xs[i]'(by rw [hlen]; omega) := by
    dsimp [d, xs]
    rw [List.getElem_append_left (by rw [B.leftPath.darts_length]; omega)]
  have hform := List.formPerm_apply_getElem xs hnodup i
    (by rw [hlen]; omega)
  have hmod : (i + 1) % xs.length = i + 1 :=
    Nat.mod_eq_of_lt (by rw [hlen]; omega)
  change B.map.toCombinatorialMap.faceSucc d = _
  rw [hface, hidx, hform]
  simp only [hmod]
  dsimp [xs]
  rw [List.getElem_append_left (by rw [B.leftPath.darts_length]; exact hi)]

private theorem pathCutLeftHalfOuter_left_half_faceSucc_get
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (i : ℕ) (hi : i + 1 < ℓ)
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P})
    (hd : d.1 = B.leftPath.darts.get
      ⟨i, by rw [B.leftPath.darts_length]; omega⟩) :
    ((pathCutLeftHalfMap B P).faceSucc d).1 =
      B.leftPath.darts.get ⟨i + 1, by rw [B.leftPath.darts_length]; omega⟩ := by
  have hbase := pathCutLeftHalfOuter_left_boundary_faceSucc_get B i hi
  have hnext : B.map.toCombinatorialMap.faceSucc d.1 ∈
      pathCutLeftHalfDarts B P := by
    rw [hd, hbase]
    exact Or.inl ⟨_, Or.inl ((mem_pathCutLeftOuterArc_iff B _).mpr
      (List.get_mem _ _)), Relation.ReflTransGen.refl⟩
  rw [pathCutLeftHalf_faceSucc_eq_base_of_mem B P d.2 hnext, hd, hbase]

/-- The proposed outer word, traversing the left path and then the reversed
opposite darts of the cut path. Helper toward `lem-lr-ind` -/
@[expose] noncomputable def pathCutLeftHalfOuterWord
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    NonemptyWord {d : D // d ∈ pathCutLeftHalfDarts B P} where
  letters := (leftPathHalf B P).darts ++
    ((cutPathHalf B P).darts.reverse.map
      (pathCutLeftHalfMap B P).edgeInv)
  nonempty := by
    intro h
    obtain ⟨hleft, _⟩ := List.append_eq_nil_iff.mp h
    have hzero : ℓ = 0 := by
      rw [← (leftPathHalf B P).darts_length, hleft]
      rfl
    have hℓ : 0 < ℓ := Nat.lt_of_lt_of_le Nat.zero_lt_one B.left_length_pos
    omega
  nodup := by
    apply List.nodup_append'.mpr
    refine ⟨pathCutLeftHalfOuter_simplePath_darts_nodup (leftPathHalf B P), ?_, ?_⟩
    · apply List.Nodup.map (pathCutLeftHalfMap B P).edgeInv.injective
      exact List.nodup_reverse.mpr
        (pathCutLeftHalfOuter_simplePath_darts_nodup (cutPathHalf B P))
    · intro d hdL hdR
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hdR
      have htail : (pathCutLeftHalfDirectedMap B P).tail
          ((pathCutLeftHalfMap B P).edgeInv e) :=
        pathCutLeftHalfOuter_simplePath_tail_of_mem (leftPathHalf B P) hdL
      have htailE : (pathCutLeftHalfDirectedMap B P).tail e :=
        pathCutLeftHalfOuter_simplePath_tail_of_mem (cutPathHalf B P)
          (List.mem_reverse.mp he)
      have hpresent : ¬ (pathCutLeftHalfDirectedMap B P).missing e := by
        change ¬ False
        simp
      have hnot : ¬ (pathCutLeftHalfDirectedMap B P).tail
          ((pathCutLeftHalfDirectedMap B P).edgeInv e) :=
        ((pathCutLeftHalfDirectedMap B P).tail_iff e hpresent).mp htailE
      exact hnot (by simpa only [pathCutLeftHalfDirectedMap, closedHalfDirectedMap,
        pathCutLeftHalfMap, closedHalfCombinatorialMap] using htail)

private theorem pathCutLeftHalf_faceSucc_reverseCut_get
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (i : ℕ) (hi : i < n) (hi0 : 0 < i)
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P})
    (hd : d.1 = B.map.toCombinatorialMap.edgeInv
      (P.darts.get ⟨i, by rw [P.darts_length]; exact hi⟩)) :
    ((pathCutLeftHalfMap B P).faceSucc d).1 =
      B.map.toCombinatorialMap.edgeInv
        (P.darts.get ⟨i - 1, by rw [P.darts_length]; omega⟩) := by
  let a : Fin P.darts.length := ⟨i, by rw [P.darts_length]; exact hi⟩
  let e := (pathCutLeftHalfMap B P).faceSucc d
  have hdB : d.1 ∈ pathCutLeftHalfBoundaryDarts B P := by
    rw [hd]
    exact Or.inr ⟨_, List.get_mem _ a, rfl⟩
  obtain ⟨z, hz, hzc⟩ := pathCutLeftHalf_boundary_single_orbit B P
  have hzd : (pathCutLeftHalfMap B P).faceSucc.SameCycle z d :=
    (hzc d).2 hdB
  have hde : (pathCutLeftHalfMap B P).faceSucc.SameCycle d e :=
    Equiv.Perm.SameCycle.rfl.apply_right
  have heB : e.1 ∈ pathCutLeftHalfBoundaryDarts B P :=
    (hzc e).1 (hzd.trans hde)
  have hv : dartTailVertex B.map e.1 =
      dartTailVertex B.map (P.darts.get a) := by
    calc
      dartTailVertex B.map e.1 = dartHeadVertex B.map d.1 :=
        pathCutLeftHalfOuter_faceSucc_vertex B P d
      _ = dartTailVertex B.map (P.darts.get a) := by
        rw [hd]
        change dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv
          (B.map.toCombinatorialMap.edgeInv (P.darts.get a))) = _
        rw [B.map.toCombinatorialMap.edgeInv_invol]
  rcases (pathCutLeftHalfOuter_boundary_iff_left_or_reverse B P e.1).mp heB
      with heL | ⟨p, hp, hep⟩
  · obtain ⟨j, hj⟩ := List.mem_iff_get.mp heL
    by_cases hj0 : j.val = 0
    · have hindex : P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩ =
          P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩ := by
        calc
          P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩ =
              dartTailVertex B.map (P.darts.get a) := (P.edge_step a).2.2.1
          _ = dartTailVertex B.map e.1 := hv.symm
          _ = dartTailVertex B.map (B.leftPath.darts.get j) := by rw [← hj]
          _ = B.leftPath.vertices.get ⟨j.val, by
              rw [B.leftPath.vertices_length]
              simpa only [B.leftPath.darts_length] using
                Nat.lt_succ_of_lt j.isLt⟩ :=
            (B.leftPath.edge_step j).2.2.1.symm
          _ = B.leftPath.vertices.get ⟨0, by
              rw [B.leftPath.vertices_length]; omega⟩ := by
            have hjFin : (⟨j.val, by
                rw [B.leftPath.vertices_length]
                simpa only [B.leftPath.darts_length] using
                  Nat.lt_succ_of_lt j.isLt⟩ : Fin B.leftPath.vertices.length) =
                ⟨0, by rw [B.leftPath.vertices_length]; omega⟩ := Fin.ext hj0
            exact congrArg B.leftPath.vertices.get hjFin
          _ = B.source := B.leftPath.start_vertex
          _ = P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩ :=
            P.start_vertex.symm
      have hfin := P.vertices_nodup.get_inj_iff.mp hindex
      have hval := congrArg Fin.val hfin
      have : i = 0 := by simpa using hval
      omega
    · have hleftlen : B.leftPath.darts.length = ℓ := B.leftPath.darts_length
      let k : Fin B.leftPath.darts.length := ⟨j.val - 1, by omega⟩
      let Lk : {d : D // d ∈ pathCutLeftHalfDarts B P} :=
        ⟨B.leftPath.darts.get k, Or.inl ⟨_, Or.inl
          ((mem_pathCutLeftOuterArc_iff B _).mpr (List.get_mem _ _)),
          Relation.ReflTransGen.refl⟩⟩
      have hpred : (pathCutLeftHalfMap B P).faceSucc Lk = e := by
        apply Subtype.ext
        have hs := pathCutLeftHalfOuter_left_half_faceSucc_get B P
          (j.val - 1) (by omega) Lk rfl
        exact hs.trans ((congrArg B.leftPath.darts.get
          (Fin.ext (by dsimp [k]; omega))).trans hj)
      have hde' : Lk = d := (pathCutLeftHalfMap B P).faceSucc.injective hpred
      have htail : B.map.tail Lk.1 := (B.leftPath.edge_step k).2.1
      have hn : ¬ B.map.tail d.1 := by
        rw [hd]
        exact (B.map.tail_iff _ (B.noMissingDarts _)).mp (P.edge_step a).2.1
      exact False.elim (hn (hde' ▸ htail))
  · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hp
    have hhead : dartHeadVertex B.map (P.darts.get j) =
        dartTailVertex B.map (P.darts.get a) := by
      rw [← hj] at hep
      exact (congrArg (dartTailVertex B.map) hep).symm.trans hv
    have hverts := (P.edge_step j).2.2.2.trans
      (hhead.trans (P.edge_step a).2.2.1.symm)
    have hidx := congrArg Fin.val (P.vertices_nodup.get_inj_iff.mp hverts)
    have hjval : j.val + 1 = i := by
      dsimp [a] at hidx
      simpa using hidx
    have hjprev : j.val = i - 1 := by omega
    let r : Fin P.darts.length := ⟨i - 1, by rw [P.darts_length]; omega⟩
    have hjr : j = r := Fin.ext (by dsimp [r]; exact hjprev)
    have hresult : e =
        ⟨B.map.toCombinatorialMap.edgeInv (P.darts.get r),
          pathCutLeftHalfBoundaryDarts_subset B P
            (.inr ⟨_, List.get_mem _ r, rfl⟩)⟩ := by
      apply Subtype.ext
      exact hep.trans (congrArg B.map.toCombinatorialMap.edgeInv
        (hj.symm.trans (congrArg P.darts.get hjr)))
    exact congrArg Subtype.val hresult

private theorem pathCutLeftHalfOuter_leftPathHalf_mem_iff
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
    d ∈ (leftPathHalf B P).darts ↔ d.1 ∈ B.leftPath.darts := by
  rw [← leftPathHalf_darts B P]
  change d ∈ (leftPathHalf B P).darts ↔
    d.1 ∈ (leftPathHalf B P).darts.map Subtype.val
  constructor
  · intro hd
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  · intro hd
    obtain ⟨e, he, hval⟩ := List.mem_map.mp hd
    have hed : e = d := Subtype.ext hval
    simpa [hed] using he

private theorem pathCutLeftHalfOuter_cutPathHalf_mem_iff
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
    d ∈ (cutPathHalf B P).darts ↔ d.1 ∈ P.darts := by
  rw [← cutPathHalf_darts B P]
  change d ∈ (cutPathHalf B P).darts ↔
    d.1 ∈ (cutPathHalf B P).darts.map Subtype.val
  constructor
  · intro hd
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  · intro hd
    obtain ⟨e, he, hval⟩ := List.mem_map.mp hd
    have hed : e = d := Subtype.ext hval
    simpa [hed] using he

private theorem pathCutLeftHalfOuter_leftPathHalf_get_val
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (i : ℕ) (hi : i < ℓ) :
    ((leftPathHalf B P).darts[i]'(by
      rw [(leftPathHalf B P).darts_length]; exact hi)).1 =
      B.leftPath.darts[i]'(by rw [B.leftPath.darts_length]; exact hi) := by
  have hq : i < (leftPathHalf B P).darts.length := by
    rw [(leftPathHalf B P).darts_length]
    exact hi
  have hb : i < B.leftPath.darts.length := by
    rw [B.leftPath.darts_length]
    exact hi
  have hopt := congrArg (fun xs : List D => xs[i]?) (leftPathHalf_darts B P)
  simp only [List.getElem?_unattach] at hopt
  rw [List.getElem?_eq_getElem hq, List.getElem?_eq_getElem hb] at hopt
  exact Option.some.inj hopt

private theorem pathCutLeftHalfOuter_leftPathHalf_faceSucc_get
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (i : ℕ) (hi : i + 1 < ℓ) :
    (pathCutLeftHalfMap B P).faceSucc
        ((leftPathHalf B P).darts.get ⟨i, by
          rw [(leftPathHalf B P).darts_length]; omega⟩) =
      (leftPathHalf B P).darts.get ⟨i + 1, by
        rw [(leftPathHalf B P).darts_length]; omega⟩ := by
  let d := (leftPathHalf B P).darts.get ⟨i, by
    rw [(leftPathHalf B P).darts_length]; omega⟩
  have hdval : d.1 = B.leftPath.darts.get ⟨i,
      by rw [B.leftPath.darts_length]; omega⟩ := by
    simpa [d, List.get_eq_getElem] using
      pathCutLeftHalfOuter_leftPathHalf_get_val B P i (by omega)
  apply Subtype.ext
  calc
    ((pathCutLeftHalfMap B P).faceSucc d).1 =
        B.leftPath.darts.get ⟨i + 1, by rw [B.leftPath.darts_length]; omega⟩ :=
      pathCutLeftHalfOuter_left_half_faceSucc_get B P i hi d hdval
    _ = ((leftPathHalf B P).darts.get ⟨i + 1, by
        rw [(leftPathHalf B P).darts_length]; omega⟩).1 := by
      exact (pathCutLeftHalfOuter_leftPathHalf_get_val B P (i + 1) hi).symm

private theorem pathCutLeftHalfOuter_reverseCut_unattach
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    ((cutPathHalf B P).darts.reverse.map (pathCutLeftHalfMap B P).edgeInv).unattach =
      P.darts.reverse.map B.map.toCombinatorialMap.edgeInv := by
  simp only [List.unattach, List.map_map, Function.comp_def,
    pathCutLeftHalfMap, closedHalfCombinatorialMap, restrictedPerm_apply,
    List.map_reverse]
  rw [← cutPathHalf_darts B P]
  apply List.ext_get
  · simp
  · intro i h₁ h₂
    simp

private theorem pathCutLeftHalfOuter_reverseCut_get_val
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (i : ℕ) (hi : i < n) :
    (((cutPathHalf B P).darts.reverse.map
        (pathCutLeftHalfMap B P).edgeInv)[n - 1 - i]'(by
          rw [List.length_map, List.length_reverse,
            (cutPathHalf B P).darts_length]; omega)).1 =
      B.map.toCombinatorialMap.edgeInv
        (P.darts[i]'(by rw [P.darts_length]; exact hi)) := by
  have hleft : n - 1 - i <
      ((cutPathHalf B P).darts.reverse.map
        (pathCutLeftHalfMap B P).edgeInv).unattach.length := by
    simp only [List.length_unattach, List.length_map, List.length_reverse,
      (cutPathHalf B P).darts_length]
    omega
  have hright : n - 1 - i <
      (P.darts.reverse.map B.map.toCombinatorialMap.edgeInv).length := by
    simp only [List.length_map, List.length_reverse, P.darts_length]
    omega
  have hopt := congrArg (fun xs : List D => xs[n - 1 - i]?)
    (pathCutLeftHalfOuter_reverseCut_unattach B P)
  rw [List.getElem?_eq_getElem hleft, List.getElem?_eq_getElem hright] at hopt
  simp only [List.getElem_unattach, List.getElem_map] at hopt
  have hval := Option.some.inj hopt
  have hrev : n - 1 - i < P.darts.reverse.length := by
    simpa only [List.length_reverse, P.darts_length] using
      (show n - 1 - i < n by omega)
  rw [List.getElem_reverse (l := P.darts) (i := n - 1 - i) hrev] at hval
  have hidx : P.darts.length - 1 - (n - 1 - i) = i := by
    rw [P.darts_length]
    omega
  simpa only [List.getElem_map, hidx] using hval

private theorem pathCutLeftHalfOuter_reverseCut_faceSucc_get
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (i : ℕ) (hi : i < n) (hi0 : 0 < i) :
    (pathCutLeftHalfMap B P).faceSucc
        (((cutPathHalf B P).darts.reverse.map
          (pathCutLeftHalfMap B P).edgeInv).get ⟨n - 1 - i, by
            rw [List.length_map, List.length_reverse,
              (cutPathHalf B P).darts_length]; omega⟩) =
      ((cutPathHalf B P).darts.reverse.map
        (pathCutLeftHalfMap B P).edgeInv).get ⟨n - i, by
          rw [List.length_map, List.length_reverse,
            (cutPathHalf B P).darts_length]; omega⟩ := by
  let xs := (cutPathHalf B P).darts.reverse.map (pathCutLeftHalfMap B P).edgeInv
  let d := xs.get ⟨n - 1 - i, by
    rw [List.length_map, List.length_reverse, (cutPathHalf B P).darts_length]
    omega⟩
  have hdval : d.1 = B.map.toCombinatorialMap.edgeInv
      (P.darts[i]'(by rw [P.darts_length]; exact hi)) := by
    simpa [d, xs, List.get_eq_getElem] using
      pathCutLeftHalfOuter_reverseCut_get_val B P i hi
  have hval := pathCutLeftHalf_faceSucc_reverseCut_get B P i hi hi0 d hdval
  have hrevIdx : n - 1 - (i - 1) = n - i := by omega
  have hnextval : (xs.get ⟨n - i, by
      rw [List.length_map, List.length_reverse,
        (cutPathHalf B P).darts_length]; omega⟩).1 =
      B.map.toCombinatorialMap.edgeInv
        (P.darts[i - 1]'(by rw [P.darts_length]; omega)) := by
    have hget := pathCutLeftHalfOuter_reverseCut_get_val B P (i - 1) (by omega)
    simpa [xs, hrevIdx, List.get_eq_getElem] using hget
  apply Subtype.ext
  calc
    ((pathCutLeftHalfMap B P).faceSucc d).1 =
        B.map.toCombinatorialMap.edgeInv
          (P.darts[i - 1]'(by rw [P.darts_length]; omega)) := hval
    _ = (xs.get ⟨n - i, by
        rw [List.length_map, List.length_reverse,
          (cutPathHalf B P).darts_length]; omega⟩).1 := hnextval.symm

private theorem pathCutLeftHalfOuter_word_mem_boundary
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
    d ∈ (pathCutLeftHalfOuterWord B P).letters ↔
      d.1 ∈ pathCutLeftHalfBoundaryDarts B P := by
  change d ∈ (leftPathHalf B P).darts ++
      ((cutPathHalf B P).darts.reverse.map (pathCutLeftHalfMap B P).edgeInv) ↔ _
  rw [List.mem_append]
  constructor
  · rintro (hd | hd)
    · have hleft := (pathCutLeftHalfOuter_leftPathHalf_mem_iff B P d).mp hd
      have hul := (B.outerSplit.2.2.1 d.1).mp hleft
      change ¬ B.map.missing d.1 ∧ B.map.tail d.1 ∧ B.map.IsOuter d.1 at hul
      exact Or.inl ⟨d.2, hul.2.2⟩
    · obtain ⟨e, he, hde⟩ := List.mem_map.mp hd
      have he' := List.mem_reverse.mp he
      have hp := (pathCutLeftHalfOuter_cutPathHalf_mem_iff B P e).mp he'
      have heval : ((pathCutLeftHalfMap B P).edgeInv e).1 =
          B.map.toCombinatorialMap.edgeInv e.1 := by
        simp [pathCutLeftHalfMap, closedHalfCombinatorialMap,
          restrictedPerm_apply]
      exact Or.inr ⟨e.1, hp,
        (congrArg Subtype.val hde).symm.trans heval⟩
  · intro hd
    rcases (pathCutLeftHalfOuter_boundary_iff_left_or_reverse B P d.1).mp hd
        with hleft | ⟨p, hp, hval⟩
    · exact Or.inl ((pathCutLeftHalfOuter_leftPathHalf_mem_iff B P d).mpr hleft)
    · let e : {d : D // d ∈ pathCutLeftHalfDarts B P} :=
        ⟨p, pathCutLeftHalf_path_mem B P hp⟩
      have he : e ∈ (cutPathHalf B P).darts :=
        (pathCutLeftHalfOuter_cutPathHalf_mem_iff B P e).mpr hp
      have heval : ((pathCutLeftHalfMap B P).edgeInv e).1 =
          B.map.toCombinatorialMap.edgeInv p := by
        simp [e, pathCutLeftHalfMap, closedHalfCombinatorialMap,
          restrictedPerm_apply]
      have heq : (pathCutLeftHalfMap B P).edgeInv e = d :=
        Subtype.ext (heval.trans hval.symm)
      exact Or.inr (List.mem_map.mpr ⟨e, List.mem_reverse.mpr he, heq⟩)

private theorem pathCutLeftHalfOuter_reverseCut_nodup
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    ((cutPathHalf B P).darts.reverse.map
      (pathCutLeftHalfMap B P).edgeInv).Nodup := by
  apply List.Nodup.map (pathCutLeftHalfMap B P).edgeInv.injective
  exact List.nodup_reverse.mpr
    (pathCutLeftHalfOuter_simplePath_darts_nodup (cutPathHalf B P))

private theorem pathCutLeftHalfOuter_reverseCut_not_tail
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {d : {d : D // d ∈ pathCutLeftHalfDarts B P}}
    (hd : d ∈ (cutPathHalf B P).darts.reverse.map
      (pathCutLeftHalfMap B P).edgeInv) :
    ¬ (pathCutLeftHalfDirectedMap B P).tail d := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp (List.mem_reverse.mp he)
  have htail : (pathCutLeftHalfDirectedMap B P).tail e := by
    rw [← hi]
    exact (cutPathHalf B P).edge_step i |>.2.1
  have hpresent : ¬ (pathCutLeftHalfDirectedMap B P).missing e := by
    change ¬ False
    simp
  exact ((pathCutLeftHalfDirectedMap B P).tail_iff e hpresent).mp htail

private theorem pathCutLeftHalfOuter_sameCycle_mem_of_closed
    {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α)
    (xs : List α) {a b : α} (ha : a ∈ xs)
    (hclosed : ∀ x, x ∈ xs → σ x ∈ xs)
    (hcycle : σ.SameCycle a b) : b ∈ xs := by
  obtain ⟨k, hk, hpow⟩ := hcycle.exists_pow_eq'
  have hmem : ∀ k : ℕ, (σ : α → α)^[k] a ∈ xs := by
    intro k
    induction k with
    | zero => simpa using ha
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hclosed _ ih
  have hiter : (σ : α → α)^[k] a = b := by
    simpa only [perm_iterate_eq_pow] using hpow
  rw [← hiter]
  exact hmem k


private theorem pathCutLeftHalfOuter_endpoint_successors
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    let L := (leftPathHalf B P).darts
    let C := (cutPathHalf B P).darts.reverse.map
      (pathCutLeftHalfMap B P).edgeInv
    (pathCutLeftHalfMap B P).faceSucc
        (L.get ⟨ℓ - 1, by
          have := B.left_length_pos
          dsimp [L]
          rw [(leftPathHalf B P).darts_length]
          omega⟩) =
      C.get ⟨0, by
        dsimp [C]
        rw [List.length_map, List.length_reverse, (cutPathHalf B P).darts_length]
        exact pathCutLeftHalf_path_length_pos B P⟩ ∧
    (pathCutLeftHalfMap B P).faceSucc
        (C.get ⟨n - 1, by
          have := pathCutLeftHalf_path_length_pos B P
          dsimp [C]
          rw [List.length_map, List.length_reverse, (cutPathHalf B P).darts_length]
          omega⟩) =
      L.get ⟨0, by
          have := B.left_length_pos
          dsimp [L]
          rw [(leftPathHalf B P).darts_length]
          omega⟩ := by
  classical
  dsimp only
  let L := (leftPathHalf B P).darts
  let C := (cutPathHalf B P).darts.reverse.map
    (pathCutLeftHalfMap B P).edgeInv
  let f := (pathCutLeftHalfMap B P).faceSucc
  have hℓpos : 0 < ℓ := Nat.lt_of_lt_of_le Nat.zero_lt_one B.left_length_pos
  have hnpos : 0 < n := pathCutLeftHalf_path_length_pos B P
  have hLlen : L.length = ℓ := (leftPathHalf B P).darts_length
  have hClen : C.length = n := by
    simp only [C, List.length_map, List.length_reverse,
      (cutPathHalf B P).darts_length]
  let l0 : {d : D // d ∈ pathCutLeftHalfDarts B P} :=
    L.get ⟨0, by omega⟩
  let llast : {d : D // d ∈ pathCutLeftHalfDarts B P} :=
    L.get ⟨ℓ - 1, by omega⟩
  let c0 : {d : D // d ∈ pathCutLeftHalfDarts B P} :=
    C.get ⟨0, by omega⟩
  let clast : {d : D // d ∈ pathCutLeftHalfDarts B P} :=
    C.get ⟨n - 1, by omega⟩
  have hLnodup : L.Nodup :=
    pathCutLeftHalfOuter_simplePath_darts_nodup (leftPathHalf B P)
  have hCnodup : C.Nodup := pathCutLeftHalfOuter_reverseCut_nodup B P
  have hL0B : l0.1 ∈ pathCutLeftHalfBoundaryDarts B P := by
    apply (pathCutLeftHalfOuter_word_mem_boundary B P l0).mp
    change l0 ∈ L ++ C
    exact List.mem_append.mpr (.inl (List.get_mem _ _))
  have hLlastB : llast.1 ∈ pathCutLeftHalfBoundaryDarts B P := by
    apply (pathCutLeftHalfOuter_word_mem_boundary B P llast).mp
    change llast ∈ L ++ C
    exact List.mem_append.mpr (.inl (List.get_mem _ _))
  have hC0B : c0.1 ∈ pathCutLeftHalfBoundaryDarts B P := by
    apply (pathCutLeftHalfOuter_word_mem_boundary B P c0).mp
    change c0 ∈ L ++ C
    exact List.mem_append.mpr (.inr (List.get_mem _ _))
  have hL0C0cycle : f.SameCycle l0 c0 := by
    obtain ⟨z, _, hzc⟩ := pathCutLeftHalf_boundary_single_orbit B P
    exact ((hzc l0).2 hL0B).symm.trans ((hzc c0).2 hC0B)
  have hnotLeftEndpoint : f llast ≠ l0 := by
    intro hend
    have hclosedLeft : ∀ x, x ∈ L → f x ∈ L := by
      intro x hx
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hx
      have hjlt : j.val < ℓ := by simpa only [hLlen] using j.isLt
      by_cases hnext : j.val + 1 < ℓ
      · have hs := pathCutLeftHalfOuter_leftPathHalf_faceSucc_get B P j.val hnext
        have hget : f (L.get j) = L.get ⟨j.val + 1, by omega⟩ := by
          simpa [L, f] using hs
        rw [← hj, hget]
        exact List.get_mem _ _
      · have hjlast : j.val = ℓ - 1 := by omega
        have hget : L.get j = llast := by
          apply congrArg L.get
          exact Fin.ext (by dsimp [llast]; omega)
        rw [← hj, hget]
        rw [hend]
        exact List.get_mem _ _
    have hc0L : c0 ∈ L :=
      pathCutLeftHalfOuter_sameCycle_mem_of_closed f L
        (a := l0) (b := c0) (List.get_mem _ _) hclosedLeft hL0C0cycle
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hc0L
    have htail := pathCutLeftHalfOuter_simplePath_tail_of_mem
      (leftPathHalf B P) (List.get_mem _ j)
    have hnot := pathCutLeftHalfOuter_reverseCut_not_tail B P (List.get_mem C ⟨0,
      by omega⟩)
    apply hnot
    change (pathCutLeftHalfDirectedMap B P).tail c0
    rw [← hj]
    exact htail
  have htargetLmem : f llast ∈ L ++ C := by
    obtain ⟨z, _, hzc⟩ := pathCutLeftHalf_boundary_single_orbit B P
    have hzlast := (hzc llast).2 hLlastB
    have hcycle : f.SameCycle llast (f llast) :=
      Equiv.Perm.SameCycle.rfl.apply_right
    have hboundary := (hzc (f llast)).1 (hzlast.trans hcycle)
    exact (pathCutLeftHalfOuter_word_mem_boundary B P (f llast)).mpr hboundary
  have hfirst : f llast = c0 := by
    have hparts : f llast ∈ L ∨ f llast ∈ C := by
      change f llast ∈ L ++ C at htargetLmem
      exact List.mem_append.mp htargetLmem
    rcases hparts with hL | hC
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hL
      have hjlt : j.val < ℓ := by simpa only [hLlen] using j.isLt
      by_cases hj0 : j.val = 0
      · have hEq : f llast = l0 := by
          calc
            f llast = L.get j := hj.symm
            _ = l0 := by
              apply congrArg L.get
              exact Fin.ext hj0
        exact (hnotLeftEndpoint hEq).elim
      · let k : Fin L.length := ⟨j.val - 1, by omega⟩
        have hsucc := pathCutLeftHalfOuter_leftPathHalf_faceSucc_get
          B P (j.val - 1) (by omega)
        have hs : f (L.get k) = L.get j := by
          simpa [L, f, k, Nat.sub_add_cancel (show 1 ≤ j.val by omega)] using hsucc
        have heq : L.get k = llast :=
          f.injective (hs.trans hj)
        have hidx := congrArg Fin.val (hLnodup.get_inj_iff.mp
          heq)
        have : j.val - 1 = ℓ - 1 := by simpa only [k, llast] using hidx
        omega
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hC
      have hjlt : j.val < n := by simpa only [hClen] using j.isLt
      by_cases hj0 : j.val = 0
      · calc
          f llast = C.get j := hj.symm
          _ = c0 := by
            apply congrArg C.get
            exact Fin.ext hj0
      · let k : Fin C.length := ⟨j.val - 1, by omega⟩
        let i : ℕ := n - j.val
        have hi : i < n := by dsimp [i]; omega
        have hi0 : 0 < i := by dsimp [i]; omega
        have hsucc := pathCutLeftHalfOuter_reverseCut_faceSucc_get B P i hi hi0
        have hidx₁ : n - 1 - i = j.val - 1 := by dsimp [i]; omega
        have hidx₂ : n - i = j.val := by dsimp [i]; omega
        have hs : f (C.get k) = C.get j := by
          simpa [C, f, k, hidx₁, hidx₂] using hsucc
        have heq : L.get ⟨ℓ - 1, by omega⟩ = C.get k :=
          (f.injective (hs.trans hj)).symm
        have htail := pathCutLeftHalfOuter_simplePath_tail_of_mem
          (leftPathHalf B P) (List.get_mem L ⟨ℓ - 1, by omega⟩)
        have hnot := pathCutLeftHalfOuter_reverseCut_not_tail B P
          (List.get_mem C k)
        exfalso
        apply hnot
        rw [← heq]
        exact htail
  have hlastCutNotTail := pathCutLeftHalfOuter_reverseCut_not_tail B P
    (List.get_mem C ⟨n - 1, by omega⟩)
  have hlastLeftTail := pathCutLeftHalfOuter_simplePath_tail_of_mem
    (leftPathHalf B P) (List.get_mem L ⟨ℓ - 1, by omega⟩)
  have hlastInputsNe : clast ≠ llast := by
    intro h
    apply hlastCutNotTail
    change (pathCutLeftHalfDirectedMap B P).tail clast
    rw [h]
    exact hlastLeftTail
  have hnotLastCutC0 : f clast ≠ c0 := by
    intro h
    apply hlastInputsNe
    exact (f.injective (hfirst.trans h.symm)).symm
  have htargetCmem : f clast ∈ L ++ C := by
    obtain ⟨z, _, hzc⟩ := pathCutLeftHalf_boundary_single_orbit B P
    have hc := (hzc clast).2 ((pathCutLeftHalfOuter_word_mem_boundary B P clast).mp
      (List.mem_append.mpr (.inr (List.get_mem _ _))))
    have hcycle : f.SameCycle clast (f clast) :=
      Equiv.Perm.SameCycle.rfl.apply_right
    have hb := (hzc (f clast)).1 (hc.trans hcycle)
    exact (pathCutLeftHalfOuter_word_mem_boundary B P (f clast)).mpr hb
  have hsecond : f clast = l0 := by
    have hparts : f clast ∈ L ∨ f clast ∈ C := by
      change f clast ∈ L ++ C at htargetCmem
      exact List.mem_append.mp htargetCmem
    rcases hparts with hL | hC
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hL
      have hjlt : j.val < ℓ := by simpa only [hLlen] using j.isLt
      by_cases hj0 : j.val = 0
      · calc
          f clast = L.get j := hj.symm
          _ = l0 := by
            apply congrArg L.get
            exact Fin.ext hj0
      · let k : Fin L.length := ⟨j.val - 1, by omega⟩
        have hsucc := pathCutLeftHalfOuter_leftPathHalf_faceSucc_get
          B P (j.val - 1) (by omega)
        have hs : f (L.get k) = L.get j := by
          simpa [L, f, k, Nat.sub_add_cancel (show 1 ≤ j.val by omega)] using hsucc
        have heq : L.get k = clast := f.injective (hs.trans hj)
        have htail := pathCutLeftHalfOuter_simplePath_tail_of_mem
          (leftPathHalf B P) (List.get_mem L k)
        exfalso
        apply hlastCutNotTail
        change (pathCutLeftHalfDirectedMap B P).tail clast
        rw [← heq]
        exact htail
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hC
      have hjlt : j.val < n := by simpa only [hClen] using j.isLt
      by_cases hj0 : j.val = 0
      · exact (hnotLastCutC0 (hj.symm.trans (by
          apply congrArg C.get
          exact Fin.ext hj0))).elim
      · let k : Fin C.length := ⟨j.val - 1, by omega⟩
        let i : ℕ := n - j.val
        have hi : i < n := by dsimp [i]; omega
        have hi0 : 0 < i := by dsimp [i]; omega
        have hsucc := pathCutLeftHalfOuter_reverseCut_faceSucc_get B P i hi hi0
        have hidx₁ : n - 1 - i = j.val - 1 := by dsimp [i]; omega
        have hidx₂ : n - i = j.val := by dsimp [i]; omega
        have hs : f (C.get k) = C.get j := by
          simpa [C, f, k, hidx₁, hidx₂] using hsucc
        have heq : C.get k = clast := f.injective (hs.trans hj)
        have hidx := congrArg Fin.val (hCnodup.get_inj_iff.mp
          heq)
        have : j.val - 1 = n - 1 := by simpa only [k, clast] using hidx
        omega
  exact ⟨by simpa [L, C, f, llast, c0] using hfirst,
    by simpa [L, C, f, clast, l0] using hsecond⟩


private theorem pathCutLeftHalfOuter_word_faceSucc_get
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (i : ℕ) (hi : i < (pathCutLeftHalfOuterWord B P).letters.length) :
    (pathCutLeftHalfMap B P).faceSucc (pathCutLeftHalfOuterWord B P).letters[i] =
      (pathCutLeftHalfOuterWord B P).letters[(i + 1) %
        (pathCutLeftHalfOuterWord B P).letters.length]'(Nat.mod_lt _ (by omega)) := by
  let L := (leftPathHalf B P).darts
  let C := (cutPathHalf B P).darts.reverse.map (pathCutLeftHalfMap B P).edgeInv
  have hLlen : L.length = ℓ := (leftPathHalf B P).darts_length
  have hClen : C.length = n := by
    simp only [C, List.length_map, List.length_reverse, (cutPathHalf B P).darts_length]
  have hℓpos : 0 < ℓ := B.left_length_pos
  have hnpos : 0 < n := pathCutLeftHalf_path_length_pos B P
  have hlen : (L ++ C).length = ℓ + n := by
    simp only [List.length_append, hLlen, hClen]
  have hi' : i < ℓ + n := by
    change i < (L ++ C).length at hi
    omega
  have hiLC : i < (L ++ C).length := by omega
  change (pathCutLeftHalfMap B P).faceSucc ((L ++ C)[i]'hiLC) =
    (L ++ C)[(i + 1) % (L ++ C).length]'(Nat.mod_lt _ (by omega))
  by_cases hleft : i < ℓ
  · simp only [List.getElem_append_left (as := L) (bs := C) (i := i) (by omega)]
    by_cases hnext : i + 1 < ℓ
    · have hmod : (i + 1) % (L ++ C).length = i + 1 :=
        Nat.mod_eq_of_lt (by omega)
      simp only [hmod]
      simp only [List.getElem_append_left (as := L) (bs := C) (i := i + 1) (by omega)]
      exact pathCutLeftHalfOuter_leftPathHalf_faceSucc_get B P i hnext
    · have hiend : i = ℓ - 1 := by omega
      have hmod : (i + 1) % (L ++ C).length = ℓ := by
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      simp only [hmod]
      simp only [List.getElem_append_right (as := L) (bs := C) (i := ℓ) (by omega),
        hLlen, Nat.sub_self, hiend]
      exact (pathCutLeftHalfOuter_endpoint_successors B P).1
  · simp only [List.getElem_append_right (as := L) (bs := C) (i := i) (by omega)]
    by_cases hnext : i + 1 < ℓ + n
    · have hmod : (i + 1) % (L ++ C).length = i + 1 :=
        Nat.mod_eq_of_lt (by omega)
      simp only [hmod]
      simp only [List.getElem_append_right (as := L) (bs := C) (i := i + 1) (by omega)]
      have hsucc := pathCutLeftHalfOuter_reverseCut_faceSucc_get B P
        (n - 1 - (i - ℓ)) (by omega) (by omega)
      have hidx₁ : n - 1 - (n - 1 - (i - ℓ)) = i - ℓ := by omega
      have hidx₂ : n - (n - 1 - (i - ℓ)) = i + 1 - ℓ := by omega
      simpa only [List.get_eq_getElem, hidx₁, hidx₂, hLlen] using hsucc
    · have hmod : (i + 1) % (L ++ C).length = 0 := by
        have heq : i + 1 = (L ++ C).length := by omega
        rw [heq, Nat.mod_self]
      have hidx : i - L.length = n - 1 := by omega
      simp only [hmod]
      simp only [List.getElem_append_left (as := L) (bs := C) (i := 0) (by omega), hidx]
      exact (pathCutLeftHalfOuter_endpoint_successors B P).2



theorem pathCutLeftHalfMarked_isOuterCycle
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    IsOuterCycle (pathCutLeftHalfMarkedMap B P) (pathCutLeftHalfOuterWord B P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    exact (pathCutLeftHalfMarked_isOuter_iff B P d).mpr
      ((pathCutLeftHalfOuter_word_mem_boundary B P d).mp hd)
  · intro d hd
    exact (pathCutLeftHalfOuter_word_mem_boundary B P d).mpr
      ((pathCutLeftHalfMarked_isOuter_iff B P d).mp hd)
  · intro d hd
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
    change (pathCutLeftHalfMap B P).faceSucc
        (pathCutLeftHalfOuterWord B P).letters[i.val] =
      (pathCutLeftHalfOuterWord B P).letters.formPerm
        (pathCutLeftHalfOuterWord B P).letters[i.val]
    rw [List.formPerm_apply_getElem _ (pathCutLeftHalfOuterWord B P).nodup]
    exact pathCutLeftHalfOuter_word_faceSucc_get B P i.val i.isLt




theorem pathCutLeftHalfMarked_outerSplit
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    FourArcsWitness (pathCutLeftHalfMarkedMap B P) (pathCutLeftHalfOuterWord B P)
      (leftPathHalf B P).darts []
      ((cutPathHalf B P).darts.reverse.map (pathCutLeftHalfMap B P).edgeInv) [] := by
  let L := (leftPathHalf B P).darts
  let C := (cutPathHalf B P).darts.reverse.map (pathCutLeftHalfMap B P).edgeInv
  have hm (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
      (pathCutLeftHalfMarkedMap B P).IsOuter d ↔ d ∈ L ∨ d ∈ C := by
    rw [← mem_iff_isOuter _ _ (pathCutLeftHalfMarked_isOuterCycle B P)]
    exact List.mem_append
  have hmissing (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
      ¬ (pathCutLeftHalfMarkedMap B P).missing d := by
    change ¬ False
    exact not_false
  have hleft (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) (hd : d ∈ L) :
      (pathCutLeftHalfMarkedMap B P).tail d :=
    pathCutLeftHalfOuter_simplePath_tail_of_mem (leftPathHalf B P) hd
  have hright (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) (hd : d ∈ C) :
      ¬ (pathCutLeftHalfMarkedMap B P).tail d :=
    pathCutLeftHalfOuter_reverseCut_not_tail B P hd
  refine ⟨pathCutLeftHalfMarked_isOuterCycle B P, ?_, ?_, ?_, ?_, ?_⟩
  · change List.IsRotated (L ++ C) (L ++ [] ++ C ++ [])
    simpa only [List.append_nil, List.nil_append] using List.IsRotated.refl (L ++ C)
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
    exact (List.not_mem_nil hd).elim
  · intro d hd
    exact (List.not_mem_nil hd).elim

/-- Internal unfolding fact for `pathCutLeftHalfMarked_leftPath_darts`. -/
private theorem pathCutLeftHalfMarked_leftPath_darts_internal
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    (pathCutLeftHalfMarked_leftPath B P).darts = (leftPathHalf B P).darts := rfl

/-- Internal unfolding fact for `pathCutLeftHalfMarked_cutPath_darts`. -/
private theorem pathCutLeftHalfMarked_cutPath_darts_internal
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    (pathCutLeftHalfMarked_cutPath B P).darts = (cutPathHalf B P).darts := rfl



theorem pathCutLeftHalfMarked_leftPath_darts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    (pathCutLeftHalfMarked_leftPath B P).darts = (leftPathHalf B P).darts :=
  pathCutLeftHalfMarked_leftPath_darts_internal B P



theorem pathCutLeftHalfMarked_cutPath_darts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    (pathCutLeftHalfMarked_cutPath B P).darts = (cutPathHalf B P).darts :=
  pathCutLeftHalfMarked_cutPath_darts_internal B P





theorem pathCutLeftHalfMarked_outerSplit_base
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    FourArcsWitness (pathCutLeftHalfMarkedMap B P) (pathCutLeftHalfOuterWord B P)
      (pathCutLeftHalfMarked_leftPath B P).darts []
      ((pathCutLeftHalfMarked_cutPath B P).darts.reverse.map
        (pathCutLeftHalfMarkedMap B P).toCombinatorialMap.edgeInv) [] := by
  rw [pathCutLeftHalfMarked_leftPath_darts, pathCutLeftHalfMarked_cutPath_darts,
    pathCutLeftHalfMarkedMap_toHalfMap]
  exact pathCutLeftHalfMarked_outerSplit B P

end DirectedDistances.PlanarMap
