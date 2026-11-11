/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceFirstMeeting
public import DirectedDistances.PaperProofs.Section5.M0GeodesicSideCarrier

/-! # Geometric carrier for the geodesic slice -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hp : BoundaryHitWitnesses (kmswPastCode W)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}






@[expose] noncomputable def m0CutGeodesicSlice {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    GeometricSideSubmap where
  vertices :=
    (m0GeodesicSideVertices hp (P (k - 1)) .right ∩
      m0GeodesicSideVertices hp (P k) .left) \
      ({v | ∃ n, a < n ∧ v = ((P (k - 1)).codePath.initial n).1.id} ∪
        {v | ∃ n, b < n ∧ v = ((P k).codePath.initial n).1.id})
  edges :=
    (m0GeodesicSideEdges hp (P (k - 1)) .right ∩
      m0GeodesicSideEdges hp (P k) .left) \
      (Set.range (fun n => (P (k - 1)).codePath.edge (a + n)) ∪
        Set.range (fun n => (P k).codePath.edge (b + n)))
  west := edgeWest (shiftedStream W 0)
  east := edgeEast (shiftedStream W 0)
  present := {e | EdgePresent (shiftedStream W 0) e}
  rotation d e := ∃ n : ℕ, 0 < n ∧
    (kmswInfRot (shiftedStream W 0) (H.1 0) : (ℕ × Bool) → ℕ × Bool)^[n] d = e ∧
      ∀ j : ℕ, 0 < j → j < n →
        ((kmswInfRot (shiftedStream W 0) (H.1 0) : (ℕ × Bool) → ℕ × Bool)^[j] d).1 ∉
          ((m0GeodesicSideEdges hp (P (k - 1)) .right ∩
            m0GeodesicSideEdges hp (P k) .left) \
            (Set.range (fun i => (P (k - 1)).codePath.edge (a + i)) ∪
              Set.range (fun i => (P k).codePath.edge (b + i)))
          )
  faceNext d e :=
    (m0GeodesicSide hp (P (k - 1)) .right).faceNext d e ∧
      (m0GeodesicSide hp (P k) .left).faceNext d e
  root := boundaryVertex (shiftedStream W 0) h (k - 1)
  boundary := m0GeodesicSeam (P (k - 1))
  seam := m0GeodesicSeam (P k)




theorem m0CutGeodesicSlice_mem_vertices_iff {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) (v : ℕ) :
    v ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).vertices ↔
      (v ∈ m0GeodesicSideVertices hp (P (k - 1)) .right ∧
        v ∈ m0GeodesicSideVertices hp (P k) .left) ∧
      v ∉ ({v | ∃ n, a < n ∧ v = ((P (k - 1)).codePath.initial n).1.id} ∪
        {v | ∃ n, b < n ∧ v = ((P k).codePath.initial n).1.id}) := by
  rfl




theorem m0CutGeodesicSlice_mem_edges_iff {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) (e : ℕ) :
    e ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).edges ↔
      (e ∈ m0GeodesicSideEdges hp (P (k - 1)) .right ∧
        e ∈ m0GeodesicSideEdges hp (P k) .left) ∧
      e ∉ (Set.range (fun n => (P (k - 1)).codePath.edge (a + n)) ∪
        Set.range (fun n => (P k).codePath.edge (b + n))) := by
  rfl




theorem m0CutGeodesicSlice_faceNext_iff {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (d e : ℕ × Bool) :
    (m0CutGeodesicSlice (hp := hp) P k a b hab).faceNext d e ↔
      (m0GeodesicSide hp (P (k - 1)) .right).faceNext d e ∧
        (m0GeodesicSide hp (P k) .left).faceNext d e := Iff.rfl



theorem m0CutGeodesicSlice_boundary_darts {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    (∀ i < a,
      (m0CutGeodesicSlice (hp := hp) P k a b hab).boundary i =
        ((P (k - 1)).codePath.edge i, false)) ∧
    (∀ i < b,
      (m0CutGeodesicSlice (hp := hp) P k a b hab).seam i =
        ((P k).codePath.edge i, false)) := by
  constructor <;> intro i hi <;> rfl



theorem m0CutGeodesicSlice_boundary_paths_meet {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    ((P (k - 1)).codePath.initial a).1 = ((P k).codePath.initial b).1 :=
  m0Cut_least_edge_coalescence_initial_vertex_eq P k hab



















end DirectedDistances.PaperProofs.Section5
