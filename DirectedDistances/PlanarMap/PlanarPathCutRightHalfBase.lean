module

public import DirectedDistances.PlanarMap.PlanarPathCutRightHalfOuter
public import DirectedDistances.PlanarMap.PlanarPathCutHalvesPlanar
public import DirectedDistances.PlanarMap.PlanarPathCutOneSided
public import DirectedDistances.PlanarMap.PlanarPathCutHalfGeodesic

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

 

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r n : ℕ}
variable (B : BipolarTriangulationWithBoundaryBase D ℓ r)
variable (P : SimpleDirectedDartPath B.map B.source B.sink n)
variable [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]



@[expose] noncomputable def pathCutRightHalfBase :
    BipolarTriangulationWithBoundaryBase
      {d : D // d ∈ pathCutRightHalfDarts B P} n r := by
  classical
  exact {
    map := pathCutRightHalfMarkedMap B P
    noMissingDarts := fun _ h => h
    planar := by
      rw [pathCutRightHalfMarkedMap_toCombinatorialMap]
      exact pathCutRightHalfDirectedMap_toCombinatorialMap_isPlanar B P
    innerFacesDegreeThree := pathCutRightHalfMarked_innerFacesDegreeThree B P
    acyclic := pathCutRightHalfMarked_acyclic B P
    source := pathCutRightHalfSource B P
    sink := pathCutRightHalfSink B P
    isSource := pathCutRightHalfMarkedSource_isSource B P
    source_unique := by
      intro v hv
      apply pathCutRightHalfSource_unique B P v
      rintro ⟨u, hu⟩
      exact hv ⟨u, (pathCutRightHalfMarkedMap_directedStep B P u v).2 hu⟩
    isSink := pathCutRightHalfMarkedSink_isSink B P
    sink_unique := by
      intro v hv
      apply pathCutRightHalfSink_unique B P v
      rintro ⟨w, hw⟩
      exact hv ⟨w, (pathCutRightHalfMarkedMap_directedStep B P v w).2 hw⟩
    left_length_pos := pathCutRightHalf_path_length_pos B P
    right_length_pos := B.right_length_pos
    outerWord := pathCutRightHalfOuterWord B P
    leftPath := pathCutRightHalfMarked_leftPath B P
    rightPath := pathCutRightHalfMarked_rightPath B P
    outerSplit := pathCutRightHalfMarked_outerSplit B P }

 
@[simp] theorem pathCutRightHalfBase_map :
    (pathCutRightHalfBase B P).map = pathCutRightHalfMarkedMap B P := rfl

 
@[simp] theorem pathCutRightHalfBase_source :
    (pathCutRightHalfBase B P).source = pathCutRightHalfSource B P := rfl

 
@[simp] theorem pathCutRightHalfBase_sink :
    (pathCutRightHalfBase B P).sink = pathCutRightHalfSink B P := rfl

 
@[simp] theorem pathCutRightHalfBase_numEdges :
    (pathCutRightHalfBase B P).map.toCombinatorialMap.numEdges =
      (pathCutRightHalfMap B P).numEdges := rfl



private def unmarkRightHalfBasePath {k : ℕ}
    (Q : SimpleDirectedDartPath (pathCutRightHalfBase B P).map
      (pathCutRightHalfBase B P).source (pathCutRightHalfBase B P).sink k) :
    SimpleDirectedDartPath (pathCutRightHalfDirectedMap B P)
      (pathCutRightHalfSource B P) (pathCutRightHalfSink B P) k :=
  { darts := Q.darts
    vertices := Q.vertices
    darts_length := Q.darts_length
    vertices_length := Q.vertices_length
    vertices_nodup := Q.vertices_nodup
    start_vertex := Q.start_vertex
    end_vertex := Q.end_vertex
    edge_step := Q.edge_step }



theorem pathCutRightHalfBase_leftPath_isXDPGeodesic
    (x : XDP) (hP : IsXDPGeodesicBase B x P) :
    IsXDPGeodesicBase (pathCutRightHalfBase B P) x
      (pathCutRightHalfBase B P).leftPath := by
  cases x with
  | ldp =>
    intro k Q
    simpa only [(cutPathRightHalf B P).darts_length] using
      cutPathRightHalf_isXDPGeodesic B P .ldp hP (unmarkRightHalfBasePath B P Q)
  | sdp =>
    intro k Q
    simpa only [(cutPathRightHalf B P).darts_length] using
      cutPathRightHalf_isXDPGeodesic B P .sdp hP (unmarkRightHalfBasePath B P Q)

private def markRightHalfBasePath {k : ℕ}
    (Q : SimpleDirectedDartPath (pathCutRightHalfDirectedMap B P)
      (pathCutRightHalfSource B P) (pathCutRightHalfSink B P) k) :
    SimpleDirectedDartPath (pathCutRightHalfBase B P).map
      (pathCutRightHalfBase B P).source (pathCutRightHalfBase B P).sink k :=
  { darts := Q.darts
    vertices := Q.vertices
    darts_length := Q.darts_length
    vertices_length := Q.vertices_length
    vertices_nodup := Q.vertices_nodup
    start_vertex := Q.start_vertex
    end_vertex := Q.end_vertex
    edge_step := Q.edge_step }

section PathEquality

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}

private theorem rightHalfBase_dart_eq_of_tail_eq_vertex
    (C : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath C.map C.source C.sink n)
    (i : Fin n) {d : D} (hd : d ∈ P.darts)
    (htail : dartTailVertex C.map d = P.vertices.get
      ⟨i.val, by rw [P.vertices_length]; omega⟩) :
    d = P.darts.get ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩ := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hd
  have hjlt : j.val < n := by simpa [P.darts_length] using j.isLt
  have hstep := P.edge_step j
  have hvertices : P.vertices.get
      ⟨j.val, by rw [P.vertices_length]; omega⟩ = P.vertices.get
      ⟨i.val, by rw [P.vertices_length]; omega⟩ := by
    calc
      P.vertices.get ⟨j.val, by rw [P.vertices_length]; omega⟩ =
          dartTailVertex C.map (P.darts.get j) := hstep.2.2.1
      _ = dartTailVertex C.map d := congrArg (dartTailVertex C.map) hj
      _ = P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ := htail
  have hidx := P.vertices_nodup.get_inj_iff.mp hvertices
  have hval : j.val = i.val := congrArg Fin.val hidx
  calc
    d = P.darts.get j := hj.symm
    _ = P.darts.get ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩ := by
      congr 1
      exact Fin.ext hval

private theorem rightHalfBase_darts_eq_of_mem
    (C : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P Q : SimpleDirectedDartPath C.map C.source C.sink n)
    (hmem : ∀ d, d ∈ Q.darts → d ∈ P.darts) : Q.darts = P.darts := by
  have hvertices : ∀ j : ℕ, ∀ hj : j ≤ n,
      Q.vertices.get ⟨j, by rw [Q.vertices_length]; omega⟩ =
        P.vertices.get ⟨j, by rw [P.vertices_length]; omega⟩ := by
    intro j
    induction j with
    | zero =>
        intro hj
        calc
          Q.vertices.get ⟨0, by rw [Q.vertices_length]; omega⟩ = C.source := Q.start_vertex
          _ = P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩ := P.start_vertex.symm
    | succ j ih =>
        intro hj
        have hjlt : j < n := by omega
        have hprev := ih (by omega)
        let iQ : Fin Q.darts.length := ⟨j, by rw [Q.darts_length]; exact hjlt⟩
        let iP : Fin n := ⟨j, hjlt⟩
        have hstepQ := Q.edge_step iQ
        have htail : dartTailVertex C.map (Q.darts.get iQ) = P.vertices.get
            ⟨j, by rw [P.vertices_length]; omega⟩ := by
          calc
            dartTailVertex C.map (Q.darts.get iQ) = Q.vertices.get
                ⟨j, by rw [Q.vertices_length]; omega⟩ := hstepQ.2.2.1.symm
            _ = P.vertices.get ⟨j, by rw [P.vertices_length]; omega⟩ := hprev
        have hdart := rightHalfBase_dart_eq_of_tail_eq_vertex C P iP
          (hmem _ (List.get_mem _ _)) htail
        have hstepP := P.edge_step ⟨j, by rw [P.darts_length]; exact hjlt⟩
        calc
          Q.vertices.get ⟨j + 1, by rw [Q.vertices_length]; omega⟩ =
              dartHeadVertex C.map (Q.darts.get iQ) := hstepQ.2.2.2
          _ = dartHeadVertex C.map
              (P.darts.get ⟨j, by rw [P.darts_length]; exact hjlt⟩) :=
                congrArg (dartHeadVertex C.map) hdart
          _ = P.vertices.get ⟨j + 1, by rw [P.vertices_length]; omega⟩ :=
                hstepP.2.2.2.symm
  apply List.ext_get
  · rw [Q.darts_length, P.darts_length]
  · intro i hiQ hiP
    have hi : i < n := by simpa [Q.darts_length] using hiQ
    let iQ : Fin Q.darts.length := ⟨i, hiQ⟩
    let iP : Fin n := ⟨i, hi⟩
    have hvi := hvertices i (by omega)
    have htail : dartTailVertex C.map (Q.darts.get iQ) = P.vertices.get
        ⟨i, by rw [P.vertices_length]; omega⟩ := by
      calc
        dartTailVertex C.map (Q.darts.get iQ) = Q.vertices.get
            ⟨i, by rw [Q.vertices_length]; omega⟩ := (Q.edge_step iQ).2.2.1.symm
        _ = P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩ := hvi
    exact rightHalfBase_dart_eq_of_tail_eq_vertex C P iP
      (hmem _ (List.get_mem _ _)) htail

end PathEquality

 
@[simp] theorem pathCutRightHalfBase_leftPath_darts :
    (pathCutRightHalfBase B P).leftPath.darts = (cutPathRightHalf B P).darts := by
  let C := pathCutRightHalfBase B P
  let Q := markRightHalfBasePath B P (cutPathRightHalf B P)
  change C.leftPath.darts = Q.darts
  symm
  apply rightHalfBase_darts_eq_of_mem C C.leftPath Q
  intro d hd
  have htail : C.map.tail d := by
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
    exact (Q.edge_step i).2.1
  have hword : d ∈ (pathCutRightHalfOuterWord B P).letters := by
    change d ∈ (cutPathRightHalf B P).darts ++ _
    exact List.mem_append.mpr (.inl hd)
  have houter : C.map.IsOuter d :=
    (pathCutRightHalfMarked_isOuterCycle B P).1 d hword
  exact (C.outerSplit.2.2.1 d).mpr ⟨C.noMissingDarts d, htail, houter⟩

 
@[simp] theorem pathCutRightHalfBase_rightPath_darts :
    (pathCutRightHalfBase B P).rightPath.darts = (rightPathHalf B P).darts := by
  let C := pathCutRightHalfBase B P
  let Q := markRightHalfBasePath B P (rightPathHalf B P)
  change C.rightPath.darts = Q.darts
  symm
  apply rightHalfBase_darts_eq_of_mem C C.rightPath Q
  intro d hd
  have htail : C.map.tail d := by
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
    exact (Q.edge_step i).2.1
  have hword : C.map.edgeInv d ∈ (pathCutRightHalfOuterWord B P).letters := by
    change C.map.edgeInv d ∈ (cutPathRightHalf B P).darts ++ _
    exact List.mem_append.mpr (.inr
      (List.mem_map.mpr ⟨d, List.mem_reverse.mpr hd, rfl⟩))
  have houter : C.map.IsOuter (C.map.edgeInv d) :=
    (pathCutRightHalfMarked_isOuterCycle B P).1 _ hword
  have hnot : ¬ C.map.tail (C.map.edgeInv d) :=
    (C.map.tail_iff d (C.noMissingDarts d)).mp htail
  have hm := (C.outerSplit.2.2.2.1 (C.map.edgeInv d)).mpr
    ⟨C.noMissingDarts _, hnot, houter⟩
  obtain ⟨e, he, hed⟩ := List.mem_map.mp hm
  have heq : e = d := C.map.edgeInv.injective hed
  exact heq ▸ List.mem_reverse.mp he

 
@[simp] theorem pathCutRightHalfBase_leftPath_darts_unattach :
    (pathCutRightHalfBase B P).leftPath.darts.unattach = P.darts := by
  rw [pathCutRightHalfBase_leftPath_darts, cutPathRightHalf_darts]

 
@[simp] theorem pathCutRightHalfBase_rightPath_darts_unattach :
    (pathCutRightHalfBase B P).rightPath.darts.unattach = B.rightPath.darts := by
  rw [pathCutRightHalfBase_rightPath_darts, rightPathHalf_darts]

 
@[simp] theorem pathCutRightHalfMarked_leftPath_darts :
    (pathCutRightHalfMarked_leftPath B P).darts = (cutPathRightHalf B P).darts :=
  pathCutRightHalfBase_leftPath_darts B P

 
@[simp] theorem pathCutRightHalfMarked_rightPath_darts :
    (pathCutRightHalfMarked_rightPath B P).darts = (rightPathHalf B P).darts :=
  pathCutRightHalfBase_rightPath_darts B P

end DirectedDistances.PlanarMap
