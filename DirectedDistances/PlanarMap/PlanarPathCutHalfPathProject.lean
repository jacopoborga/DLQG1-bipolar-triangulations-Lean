/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlanarPathCutLeftBase
public import DirectedDistances.PlanarMap.PlanarPathCutRightBase

/-! # Path projection from the cut halves

paper result. Paths in either cut half project to paths in the original base. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r n : ℕ}

/-- Project a simple directed dart path through an injective vertex map and a
dart map preserving presence, orientation, and incidence. Helper toward -/
@[expose] def projectSimpleDirectedDartPath
    {A E : Type*} [Fintype A] [DecidableEq A] [Fintype E] [DecidableEq E]
    {M : DirectedMapWithMissing A} {N : DirectedMapWithMissing E}
    {u v : MapVertex M} {k : ℕ}
    (f : MapVertex M → MapVertex N) (g : A → E)
    (hinj : Function.Injective f)
    (hmissing : ∀ d, ¬ N.missing (g d))
    (htail : ∀ d, M.tail d → N.tail (g d))
    (htailVertex : ∀ d, f (dartTailVertex M d) = dartTailVertex N (g d))
    (hheadVertex : ∀ d, f (dartHeadVertex M d) = dartHeadVertex N (g d))
    (Q : SimpleDirectedDartPath M u v k) :
    SimpleDirectedDartPath N (f u) (f v) k := by
  refine {
    darts := Q.darts.map g
    vertices := Q.vertices.map f
    darts_length := by simp [Q.darts_length]
    vertices_length := by simp [Q.vertices_length]
    vertices_nodup := Q.vertices_nodup.map hinj
    start_vertex := ?_
    end_vertex := ?_
    edge_step := ?_ }
  · simpa only [List.length_map, Q.vertices_length,
      List.get_eq_getElem, List.getElem_map] using congrArg f Q.start_vertex
  · simpa only [List.length_map, Q.vertices_length,
      List.get_eq_getElem, List.getElem_map] using congrArg f Q.end_vertex
  · intro i
    have hiMap : i.val < Q.darts.length := by
      simpa only [List.length_map] using i.isLt
    have hi : i.val < k := by simpa [Q.darts_length] using hiMap
    let j : Fin Q.darts.length := ⟨i.val, by rw [Q.darts_length]; exact hi⟩
    let jv : Fin Q.vertices.length := ⟨i.val, by
      rw [Q.vertices_length]
      omega⟩
    let jv' : Fin Q.vertices.length := ⟨i.val + 1, by
      rw [Q.vertices_length]
      omega⟩
    have hstep := Q.edge_step j
    have hgetD : (Q.darts.map g).get i = g (Q.darts.get j) := by
      simp [j]
    have hgetV : (Q.vertices.map f).get
        ⟨i.val, by simp only [List.length_map]; rw [Q.vertices_length]; omega⟩ =
          f (Q.vertices.get jv) := by
      simp [jv]
    have hgetV' : (Q.vertices.map f).get
        ⟨i.val + 1, by simp only [List.length_map]; rw [Q.vertices_length]; omega⟩ =
          f (Q.vertices.get jv') := by
      simp [jv']
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hgetD]
      exact hmissing (Q.darts.get j)
    · rw [hgetD]
      exact htail _ hstep.2.1
    · calc
        (Q.vertices.map f).get
            ⟨i.val, by simp only [List.length_map]; rw [Q.vertices_length]; omega⟩ =
            f (Q.vertices.get jv) := hgetV
        _ = f (dartTailVertex M (Q.darts.get j)) :=
              congrArg f hstep.2.2.1
        _ = dartTailVertex N (g (Q.darts.get j)) :=
              htailVertex (Q.darts.get j)
        _ = dartTailVertex N ((Q.darts.map g).get i) := by rw [hgetD]
    · calc
        (Q.vertices.map f).get
            ⟨i.val + 1, by simp only [List.length_map]; rw [Q.vertices_length]; omega⟩ =
            f (Q.vertices.get jv') := hgetV'
        _ = f (dartHeadVertex M (Q.darts.get j)) :=
              congrArg f hstep.2.2.2
        _ = dartHeadVertex N (g (Q.darts.get j)) :=
              hheadVertex (Q.darts.get j)
        _ = dartHeadVertex N ((Q.darts.map g).get i) := by rw [hgetD]

/-- Project a path in the left cut half to the original base path, with its
darts equal to the underlying base darts. Helper toward lem-lr-ind -/
@[expose] noncomputable def pathCutLeftHalf_projectPath
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {u v : MapVertex (pathCutLeftHalfDirectedMap B P)} {k : ℕ}
    (Q : SimpleDirectedDartPath (pathCutLeftHalfDirectedMap B P) u v k) :
    SimpleDirectedDartPath B.map
      (pathCutLeftHalfVertexMap B P u) (pathCutLeftHalfVertexMap B P v) k :=
  projectSimpleDirectedDartPath (u := u) (v := v)
    (pathCutLeftHalfVertexMap B P) Subtype.val
    (pathCutLeftHalfVertexMap_injective B P)
    (fun d => B.noMissingDarts d.1)
    (fun d hd => ((pathCutLeftHalf_embedding_fields B P).2.2.1 d).mp hd)
    (pathCutLeftHalfVertexMap_dartTailVertex B P)
    (pathCutLeftHalfVertexMap_dartHeadVertex B P) Q

/-- The left projection has exactly the mapped dart list. Helper toward -/
theorem pathCutLeftHalf_projectPath_darts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {u v : MapVertex (pathCutLeftHalfDirectedMap B P)} {k : ℕ}
    (Q : SimpleDirectedDartPath (pathCutLeftHalfDirectedMap B P) u v k) :
    (pathCutLeftHalf_projectPath B P Q).darts = Q.darts.map Subtype.val := rfl

/-- The left projection is injective on paths with fixed endpoints and
length, since the underlying dart list determines a simple directed path.
result. -/
theorem pathCutLeftHalf_projectPath_injective
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {u v : MapVertex (pathCutLeftHalfDirectedMap B P)} {k : ℕ}
    (Q R : SimpleDirectedDartPath (pathCutLeftHalfDirectedMap B P) u v k)
    (h : pathCutLeftHalf_projectPath B P Q =
      pathCutLeftHalf_projectPath B P R) : Q = R := by
  apply SimpleDirectedDartPath.eq_of_darts_eq
  have hd := congrArg SimpleDirectedDartPath.darts h
  rw [pathCutLeftHalf_projectPath_darts,
    pathCutLeftHalf_projectPath_darts] at hd
  exact (List.map_injective_iff.mpr (fun _ _ hval => Subtype.ext hval)) hd

/-- Every source-to-sink path length in the left half occurs in the base
source-to-sink length set. Helper toward lem-lr-ind -/
theorem pathCutLeftHalf_sourceSinkPathLength_mem
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {k : ℕ}
    (Q : SimpleDirectedDartPath (pathCutLeftHalfDirectedMap B P)
      (pathCutLeftHalfSource B P) (pathCutLeftHalfSink B P) k) :
    k ∈ sourceSinkPathLengthsBase B := by
  apply (mem_sourceSinkPathLengthsBase B k).2
  have Q' := pathCutLeftHalf_projectPath B P Q
  have Qbase : SimpleDirectedDartPath B.map B.source B.sink k := by
    simpa only [pathCutLeftHalfSource_map, pathCutLeftHalfSink_map] using Q'
  exact ⟨Qbase, trivial⟩

/-- Project a path in the right cut half to the original base path, with its
darts equal to the underlying base darts. Helper toward lem-lr-ind -/
@[expose] noncomputable def pathCutRightHalf_projectPath
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {u v : MapVertex (pathCutRightHalfDirectedMap B P)} {k : ℕ}
    (Q : SimpleDirectedDartPath (pathCutRightHalfDirectedMap B P) u v k) :
    SimpleDirectedDartPath B.map
      (pathCutRightHalfVertexMap B P u) (pathCutRightHalfVertexMap B P v) k :=
  projectSimpleDirectedDartPath (u := u) (v := v)
    (pathCutRightHalfVertexMap B P) Subtype.val
    (pathCutRightHalfVertexMap_injective B P)
    (fun d => B.noMissingDarts d.1)
    (fun d hd => ((pathCutRightHalf_embedding_fields B P).2.2.1 d).mp hd)
    (pathCutRightHalfVertexMap_dartTailVertex B P)
    (pathCutRightHalfVertexMap_dartHeadVertex B P) Q

/-- The right projection has exactly the mapped dart list. Helper toward -/
theorem pathCutRightHalf_projectPath_darts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {u v : MapVertex (pathCutRightHalfDirectedMap B P)} {k : ℕ}
    (Q : SimpleDirectedDartPath (pathCutRightHalfDirectedMap B P) u v k) :
    (pathCutRightHalf_projectPath B P Q).darts = Q.darts.map Subtype.val := rfl

/-- The right projection is injective on paths with fixed endpoints and
length, since the underlying dart list determines a simple directed path.
result. -/
theorem pathCutRightHalf_projectPath_injective
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {u v : MapVertex (pathCutRightHalfDirectedMap B P)} {k : ℕ}
    (Q R : SimpleDirectedDartPath (pathCutRightHalfDirectedMap B P) u v k)
    (h : pathCutRightHalf_projectPath B P Q =
      pathCutRightHalf_projectPath B P R) : Q = R := by
  apply SimpleDirectedDartPath.eq_of_darts_eq
  have hd := congrArg SimpleDirectedDartPath.darts h
  rw [pathCutRightHalf_projectPath_darts,
    pathCutRightHalf_projectPath_darts] at hd
  exact (List.map_injective_iff.mpr (fun _ _ hval => Subtype.ext hval)) hd

/-- Every source-to-sink path length in the right half occurs in the base
source-to-sink length set. Helper toward lem-lr-ind -/
theorem pathCutRightHalf_sourceSinkPathLength_mem
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {k : ℕ}
    (Q : SimpleDirectedDartPath (pathCutRightHalfDirectedMap B P)
      (pathCutRightHalfSource B P) (pathCutRightHalfSink B P) k) :
    k ∈ sourceSinkPathLengthsBase B := by
  apply (mem_sourceSinkPathLengthsBase B k).2
  have Q' := pathCutRightHalf_projectPath B P Q
  have Qbase : SimpleDirectedDartPath B.map B.source B.sink k := by
    simpa only [pathCutRightHalfSource_map, pathCutRightHalfSink_map] using Q'
  exact ⟨Qbase, trivial⟩

end DirectedDistances.PlanarMap

