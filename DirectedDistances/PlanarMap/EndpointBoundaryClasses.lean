/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BipolarBoundaryData

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimpleDirectedDartPath

variable {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}

/-- Index data of a listed dart. Helper toward the endpoint-class use of
in the paper inventory; not Lemma 3.18. -/
theorem exists_index (P : SimpleDirectedDartPath M s t n) (d : D) (hd : d ∈ P.darts) :
    ∃ (i : ℕ) (_ : i < n), ¬ M.missing d ∧ M.tail d ∧
      dartTailVertex M d = P.vertices.get ⟨i, by have := P.vertices_length; omega⟩ ∧
      dartHeadVertex M d = P.vertices.get ⟨i + 1, by have := P.vertices_length; omega⟩ := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
  have h := P.edge_step i
  refine ⟨i.val, by have := i.isLt; have := P.darts_length; omega, ?_⟩
  exact ⟨h.1, h.2.1, h.2.2.1.symm, h.2.2.2.symm⟩

end SimpleDirectedDartPath

/-- A one-edge simple directed path has vertex list `[s, t]`. Helper toward the
counted; not Lemma 3.18. -/
theorem singleEdge_vertices {M : DirectedMapWithMissing D} {s t : MapVertex M}
    (P : SimpleDirectedDartPath M s t 1) : P.vertices = [s, t] := by
  have hl := P.vertices_length
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl
  · simpa using P.start_vertex
  · simpa using P.end_vertex

/-- A one-edge path meets any other `s`-`t` path only in `s` and `t`. -/
theorem singleEdge_internally_vertex_disjoint {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {r : ℕ} (P : SimpleDirectedDartPath M s t 1)
    (Q : SimpleDirectedDartPath M s t r) :
    ∀ v, v ∈ P.vertices → v ∈ Q.vertices → v = s ∨ v = t := by
  intro v hP _
  rw [singleEdge_vertices P] at hP
  simpa using hP

/-- Symmetric version of `singleEdge_internally_vertex_disjoint`. Helper (simple-boundary restriction -/
theorem singleEdge_internally_vertex_disjoint_right {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {r : ℕ} (Q : SimpleDirectedDartPath M s t r)
    (P : SimpleDirectedDartPath M s t 1) :
    ∀ v, v ∈ Q.vertices → v ∈ P.vertices → v = s ∨ v = t :=
  fun v hQ hP => singleEdge_internally_vertex_disjoint P Q v hP hQ

private theorem singleEdge_core {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {r : ℕ} (hr : 2 ≤ r) (P : SimpleDirectedDartPath M s t 1)
    (Q : SimpleDirectedDartPath M s t r) (d e : D) (hd : d ∈ P.darts) (he : e ∈ Q.darts)
    (h : Equiv.Perm.SameCycle M.toCombinatorialMap.edgeInv d e) : False := by
  obtain ⟨i, hi, hm, ht, hts, hth⟩ := P.exists_index d hd
  obtain ⟨j, hj, hQm, hQt, hQts, hQth⟩ := Q.exists_index e he
  obtain rfl : i = 0 := by omega
  have hts' : dartTailVertex M d = s := hts.trans P.start_vertex
  have hth' : dartHeadVertex M d = t := hth.trans P.end_vertex
  rcases (CombinatorialMap.edgeInv_sameCycle_iff M.toCombinatorialMap d e).mp h with heq | heq
  · have e1 : Q.vertices.get ⟨j, by have := Q.vertices_length; omega⟩ =
        Q.vertices.get ⟨0, by have := Q.vertices_length; omega⟩ := by
      rw [← hQts, heq, hts']
      exact Q.start_vertex.symm
    have e2 : Q.vertices.get ⟨j + 1, by have := Q.vertices_length; omega⟩ =
        Q.vertices.get ⟨r, by have := Q.vertices_length; omega⟩ := by
      rw [← hQth, heq, hth']
      exact Q.end_vertex.symm
    have i1 := congrArg Fin.val (List.nodup_iff_injective_get.mp Q.vertices_nodup e1)
    have i2 := congrArg Fin.val (List.nodup_iff_injective_get.mp Q.vertices_nodup e2)
    simp only at i1 i2
    omega
  · exact (M.tail_iff d hm).mp ht (by rw [← heq]; exact hQt)

/-- A one-edge path and an `s`-`t` path of length `r ≥ 2` share no edge orbit. -/
theorem singleEdge_edge_disjoint {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {r : ℕ} (hr : 2 ≤ r) (P : SimpleDirectedDartPath M s t 1)
    (Q : SimpleDirectedDartPath M s t r) :
    ∀ d ∈ P.darts, ∀ e ∈ Q.darts,
      ¬ Equiv.Perm.SameCycle M.toCombinatorialMap.edgeInv d e :=
  fun d hd e he h => singleEdge_core hr P Q d e hd he h

/-- counted; not Lemma 3.18. -/
theorem singleEdge_edge_disjoint_right {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {r : ℕ} (hr : 2 ≤ r) (Q : SimpleDirectedDartPath M s t r)
    (P : SimpleDirectedDartPath M s t 1) :
    ∀ d ∈ Q.darts, ∀ e ∈ P.darts,
      ¬ Equiv.Perm.SameCycle M.toCombinatorialMap.edgeInv d e :=
  fun d hd e he h => singleEdge_core hr P Q e d he hd h.symm

namespace BipolarTriangulationWithBoundary

/-- Carrier data for left length `1`, without the two disjointness fields, which
are automatic when `2 ≤ r`. Helper toward the endpoint-class use of
not Lemma 3.18. -/
@[expose] def ofLeftSingleEdge {r : ℕ} (map : DirectedMapWithMissing D)
    (noMissingDarts : ∀ d, ¬ map.missing d)
    (planar : map.toCombinatorialMap.IsPlanar)
    (innerFacesDegreeThree : ∀ d, ¬ map.IsOuter d →
      map.toCombinatorialMap.faceSucc
          (map.toCombinatorialMap.faceSucc (map.toCombinatorialMap.faceSucc d)) = d ∧
        map.toCombinatorialMap.faceSucc d ≠ d ∧
        map.toCombinatorialMap.faceSucc (map.toCombinatorialMap.faceSucc d) ≠ d)
    (acyclic : map.IsAcyclic)
    (source sink : MapVertex map)
    (isSource : ¬ ∃ u, map.directedStep u source)
    (source_unique : ∀ v, (¬ ∃ u, map.directedStep u v) → v = source)
    (isSink : ¬ ∃ w, map.directedStep sink w)
    (sink_unique : ∀ v, (¬ ∃ w, map.directedStep v w) → v = sink)
    (left_length_pos : 1 ≤ 1) (right_length_pos : 1 ≤ r)
    (outerWord : NonemptyWord D)
    (leftPath : SimpleDirectedDartPath map source sink 1)
    (rightPath : SimpleDirectedDartPath map source sink r)
    (outerSplit : FourArcsWitness map outerWord leftPath.darts []
      (rightPath.darts.reverse.map map.toCombinatorialMap.edgeInv) [])
    (hr : 2 ≤ r) : BipolarTriangulationWithBoundary D 1 r where
  map := map
  noMissingDarts := noMissingDarts
  planar := planar
  innerFacesDegreeThree := innerFacesDegreeThree
  acyclic := acyclic
  source := source
  sink := sink
  isSource := isSource
  source_unique := source_unique
  isSink := isSink
  sink_unique := sink_unique
  left_length_pos := left_length_pos
  right_length_pos := right_length_pos
  outerWord := outerWord
  leftPath := leftPath
  rightPath := rightPath
  paths_internally_vertex_disjoint :=
    singleEdge_internally_vertex_disjoint leftPath rightPath
  paths_edge_disjoint := singleEdge_edge_disjoint hr leftPath rightPath
  outerSplit := outerSplit

/-- Carrier data for right length `1`, without the two disjointness fields,
Lemma 3.18. -/
@[expose] def ofRightSingleEdge {ℓ : ℕ} (map : DirectedMapWithMissing D)
    (noMissingDarts : ∀ d, ¬ map.missing d)
    (planar : map.toCombinatorialMap.IsPlanar)
    (innerFacesDegreeThree : ∀ d, ¬ map.IsOuter d →
      map.toCombinatorialMap.faceSucc
          (map.toCombinatorialMap.faceSucc (map.toCombinatorialMap.faceSucc d)) = d ∧
        map.toCombinatorialMap.faceSucc d ≠ d ∧
        map.toCombinatorialMap.faceSucc (map.toCombinatorialMap.faceSucc d) ≠ d)
    (acyclic : map.IsAcyclic)
    (source sink : MapVertex map)
    (isSource : ¬ ∃ u, map.directedStep u source)
    (source_unique : ∀ v, (¬ ∃ u, map.directedStep u v) → v = source)
    (isSink : ¬ ∃ w, map.directedStep sink w)
    (sink_unique : ∀ v, (¬ ∃ w, map.directedStep v w) → v = sink)
    (left_length_pos : 1 ≤ ℓ) (right_length_pos : 1 ≤ 1)
    (outerWord : NonemptyWord D)
    (leftPath : SimpleDirectedDartPath map source sink ℓ)
    (rightPath : SimpleDirectedDartPath map source sink 1)
    (outerSplit : FourArcsWitness map outerWord leftPath.darts []
      (rightPath.darts.reverse.map map.toCombinatorialMap.edgeInv) [])
    (hℓ : 2 ≤ ℓ) : BipolarTriangulationWithBoundary D ℓ 1 where
  map := map
  noMissingDarts := noMissingDarts
  planar := planar
  innerFacesDegreeThree := innerFacesDegreeThree
  acyclic := acyclic
  source := source
  sink := sink
  isSource := isSource
  source_unique := source_unique
  isSink := isSink
  sink_unique := sink_unique
  left_length_pos := left_length_pos
  right_length_pos := right_length_pos
  outerWord := outerWord
  leftPath := leftPath
  rightPath := rightPath
  paths_internally_vertex_disjoint :=
    singleEdge_internally_vertex_disjoint_right leftPath rightPath
  paths_edge_disjoint := singleEdge_edge_disjoint_right hℓ leftPath rightPath
  outerSplit := outerSplit

/-- Every carrier element with left length `1` and `2 ≤ r` is rebuilt from its
Lemma 3.18. -/
theorem ofLeftSingleEdge_eq {r : ℕ} (B : BipolarTriangulationWithBoundary D 1 r)
    (hr : 2 ≤ r) :
    ofLeftSingleEdge B.map B.noMissingDarts B.planar B.innerFacesDegreeThree B.acyclic
      B.source B.sink B.isSource B.source_unique B.isSink B.sink_unique
      B.left_length_pos B.right_length_pos B.outerWord B.leftPath B.rightPath
      B.outerSplit hr = B := by
  cases B
  rfl

/-- not counted; not Lemma 3.18. -/
theorem ofRightSingleEdge_eq {ℓ : ℕ} (B : BipolarTriangulationWithBoundary D ℓ 1)
    (hℓ : 2 ≤ ℓ) :
    ofRightSingleEdge B.map B.noMissingDarts B.planar B.innerFacesDegreeThree B.acyclic
      B.source B.sink B.isSource B.source_unique B.isSink B.sink_unique
      B.left_length_pos B.right_length_pos B.outerWord B.leftPath B.rightPath
      B.outerSplit hℓ = B := by
  cases B
  rfl

end BipolarTriangulationWithBoundary
end DirectedDistances.PlanarMap
