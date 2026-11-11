module

public import DirectedDistances.PlanarMap.PlanarPathCutHalfOuter
public import DirectedDistances.PlanarMap.PlanarPathCutHalvesPlanar
public import DirectedDistances.PlanarMap.PlanarPathCutOneSided
public import DirectedDistances.PlanarMap.PlanarPathCutHalfGeodesic
public import DirectedDistances.PlanarMap.PlanarPathCutNoStrictLeft
public import DirectedDistances.PlanarMap.LRIndClassPredicates

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

 

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r n : ℕ}
variable (B : BipolarTriangulationWithBoundaryBase D ℓ r)
variable (P : SimpleDirectedDartPath B.map B.source B.sink n)
variable [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]



@[expose] noncomputable def pathCutLeftHalfBase :
    BipolarTriangulationWithBoundaryBase
      {d : D // d ∈ pathCutLeftHalfDarts B P} ℓ n := by
  classical
  exact {
    map := pathCutLeftHalfMarkedMap B P
    noMissingDarts := fun _ h => h
    planar := by
      rw [pathCutLeftHalfMarkedMap_toCombinatorialMap]
      exact pathCutLeftHalfDirectedMap_toCombinatorialMap_isPlanar B P
    innerFacesDegreeThree := pathCutLeftHalfMarked_innerFacesDegreeThree B P
    acyclic := pathCutLeftHalfMarked_acyclic B P
    source := pathCutLeftHalfSource B P
    sink := pathCutLeftHalfSink B P
    isSource := pathCutLeftHalfMarkedSource_isSource B P
    source_unique := by
      intro v hv
      apply pathCutLeftHalfSource_unique B P v
      rintro ⟨u, hu⟩
      exact hv ⟨u, (pathCutLeftHalfMarkedMap_directedStep B P u v).2 hu⟩
    isSink := pathCutLeftHalfMarkedSink_isSink B P
    sink_unique := by
      intro v hv
      apply pathCutLeftHalfSink_unique B P v
      rintro ⟨w, hw⟩
      exact hv ⟨w, (pathCutLeftHalfMarkedMap_directedStep B P v w).2 hw⟩
    left_length_pos := B.left_length_pos
    right_length_pos := pathCutLeftHalf_path_length_pos B P
    outerWord := pathCutLeftHalfOuterWord B P
    leftPath := pathCutLeftHalfMarked_leftPath B P
    rightPath := pathCutLeftHalfMarked_cutPath B P
    outerSplit := pathCutLeftHalfMarked_outerSplit_base B P }

 
@[simp] theorem pathCutLeftHalfBase_map :
    (pathCutLeftHalfBase B P).map = pathCutLeftHalfMarkedMap B P := rfl

 
@[simp] theorem pathCutLeftHalfBase_source :
    (pathCutLeftHalfBase B P).source = pathCutLeftHalfSource B P := rfl

 
@[simp] theorem pathCutLeftHalfBase_sink :
    (pathCutLeftHalfBase B P).sink = pathCutLeftHalfSink B P := rfl

 
@[simp] theorem pathCutLeftHalfBase_leftPath_darts :
    (pathCutLeftHalfBase B P).leftPath.darts = (leftPathHalf B P).darts :=
  pathCutLeftHalfMarked_leftPath_darts B P

 
@[simp] theorem pathCutLeftHalfBase_rightPath_darts :
    (pathCutLeftHalfBase B P).rightPath.darts = (cutPathHalf B P).darts :=
  pathCutLeftHalfMarked_cutPath_darts B P

 
@[simp] theorem pathCutLeftHalfBase_leftPath_darts_unattach :
    (pathCutLeftHalfBase B P).leftPath.darts.unattach = B.leftPath.darts := by
  rw [pathCutLeftHalfBase_leftPath_darts, leftPathHalf_darts]

 
@[simp] theorem pathCutLeftHalfBase_rightPath_darts_unattach :
    (pathCutLeftHalfBase B P).rightPath.darts.unattach = P.darts := by
  rw [pathCutLeftHalfBase_rightPath_darts, cutPathHalf_darts]

 
@[simp] theorem pathCutLeftHalfBase_numEdges :
    (pathCutLeftHalfBase B P).map.toCombinatorialMap.numEdges =
      (pathCutLeftHalfMap B P).numEdges := rfl



private def unmarkLeftHalfBasePath {k : ℕ}
    (Q : SimpleDirectedDartPath (pathCutLeftHalfBase B P).map
      (pathCutLeftHalfBase B P).source (pathCutLeftHalfBase B P).sink k) :
    SimpleDirectedDartPath (pathCutLeftHalfDirectedMap B P)
      (pathCutLeftHalfSource B P) (pathCutLeftHalfSink B P) k :=
  { darts := Q.darts
    vertices := Q.vertices
    darts_length := Q.darts_length
    vertices_length := Q.vertices_length
    vertices_nodup := Q.vertices_nodup
    start_vertex := Q.start_vertex
    end_vertex := Q.end_vertex
    edge_step := Q.edge_step }




theorem pathCutLeftHalfBase_rightPath_isUniqueXDPGeodesic
    (x : XDP) (hP : IsLexLeftmostXDPGeodesic B x P) :
    IsUniqueXDPGeodesicBase (pathCutLeftHalfBase B P) x
      (pathCutLeftHalfBase B P).rightPath := by
  have hgeo : IsXDPGeodesicBase (pathCutLeftHalfBase B P) x
      (pathCutLeftHalfBase B P).rightPath := by
    cases x with
    | ldp =>
      intro k Q
      simpa only [(cutPathHalf B P).darts_length] using
        cutPathHalf_isXDPGeodesic B P .ldp hP.1 (unmarkLeftHalfBasePath B P Q)
    | sdp =>
      intro k Q
      simpa only [(cutPathHalf B P).darts_length] using
        cutPathHalf_isXDPGeodesic B P .sdp hP.1 (unmarkLeftHalfBasePath B P Q)
  refine ⟨hgeo, ?_⟩
  intro m Q hQ
  have hmn : m = n := by
    cases x with
    | ldp =>
      exact ((isLDPGeodesicBase_iff_length_eq _ Q).1 hQ).trans
        ((isLDPGeodesicBase_iff_length_eq _ (pathCutLeftHalfBase B P).rightPath).1 hgeo).symm
    | sdp =>
      exact ((isSDPGeodesicBase_iff_length_eq _ Q).1 hQ).trans
        ((isSDPGeodesicBase_iff_length_eq _ (pathCutLeftHalfBase B P).rightPath).1 hgeo).symm
  subst m
  have hdarts : Q.darts.unattach = P.darts :=
    pathCutLeftHalf_geodesic_unique B P x hP.1
      (fun R hR d hd => lexLeftmost_no_strict_left_dart B x P hP R hR d hd)
      (unmarkLeftHalfBasePath B P Q)
  apply List.map_injective_iff.2 Subtype.val_injective
  change Q.darts.unattach = (pathCutLeftHalfBase B P).rightPath.darts.unattach
  rw [pathCutLeftHalfBase_rightPath_darts_unattach]
  exact hdarts

end DirectedDistances.PlanarMap
