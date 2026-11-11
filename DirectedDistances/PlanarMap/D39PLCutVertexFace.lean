/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39BallOrbitComponents11
public import DirectedDistances.PlanarMap.D39PolygonalConnected2

/-! # First returns in a face walk toward cut vertices

Helpers toward Proposition 5.16. A repeated point in a polygonal face walk
gives a first-return closed subwalk. The further implication from a simple
polygon to separation in the dart connectivity relation is recorded below
as an open obligation; no face-orbit identification or cut-vertex result is
claimed here. -/

public section
noncomputable section
namespace DirectedDistances.PlanarMap

open Set

namespace Polyline

/-- Helper toward Proposition 5.16: between two visits to the same point of
a polygonal walk, the first return to that point gives a closed subwalk.
Its interior vertices avoid the repeated point, its image stays in the walk,
and every segment retains its ordered source segment. -/
theorem exists_firstReturn_intervalPolyline (c : Polyline) (i j : ℕ)
    (hij : i < j) (hj : j < c.points.length)
    (hvisit : c.point i = c.point j) :
    ∃ k : ℕ, i < k ∧ k ≤ j ∧
      (c.intervalPolyline i (k - i)).start = c.point i ∧
      (c.intervalPolyline i (k - i)).finish = c.point i ∧
      (∀ r : ℕ, 0 < r → r < k - i →
        (c.intervalPolyline i (k - i)).point r ≠ c.point i) ∧
      (c.intervalPolyline i (k - i)).image ⊆ c.image ∧
      (∀ r : ℕ, r < k - i →
        (c.intervalPolyline i (k - i)).segmentAt r = c.segmentAt (i + r)) := by
  have hex : ∃ k : ℕ, i < k ∧ k ≤ j ∧ c.point i = c.point k :=
    ⟨j, hij, le_rfl, hvisit⟩
  let k := Nat.find hex
  obtain ⟨hik, hkj, hret⟩ := Nat.find_spec hex
  have hsum : i + (k - i) = k := Nat.add_sub_of_le hik.le
  have hbound : i + (k - i) < c.points.length := by omega
  have hfirst (m : ℕ) (him : i < m) (hmk : m < k) :
      c.point i ≠ c.point m := by
    intro h
    have hmin := Nat.find_min' hex
      (show i < m ∧ m ≤ j ∧ c.point i = c.point m from
        ⟨him, le_trans (Nat.le_of_lt hmk) hkj, h⟩)
    omega
  refine ⟨k, hik, hkj, ?_, ?_, ?_, ?_, ?_⟩
  · exact Polyline.start_intervalPolyline c i (k - i)
  · rw [Polyline.finish_intervalPolyline, hsum]
    exact hret.symm
  · intro r hr0 hrn
    rw [Polyline.point_intervalPolyline c i (k - i) r (Nat.le_of_lt hrn)]
    intro h
    exact hfirst (i + r) (by omega) (by omega) h.symm
  · exact c.image_intervalPolyline_subset i (k - i) hbound
  · intro r hr
    exact Polyline.segmentAt_intervalPolyline c i (k - i) r hr

end Polyline

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: if two vertices of a finite face walk
are at the same drawing point, its first return subwalk is closed and
retains the exact ordered arc segments of the face walk. -/
theorem faceWalkPolyline_firstReturn {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (d : B.D) (n i j : ℕ)
    (hij : i < j) (hj : j < (faceWalkPolyline B vert P d n).points.length)
    (hvisit : (faceWalkPolyline B vert P d n).point i =
      (faceWalkPolyline B vert P d n).point j) :
    ∃ k : ℕ, i < k ∧ k ≤ j ∧
      ((faceWalkPolyline B vert P d n).intervalPolyline i (k - i)).start =
        (faceWalkPolyline B vert P d n).point i ∧
      ((faceWalkPolyline B vert P d n).intervalPolyline i (k - i)).finish =
        (faceWalkPolyline B vert P d n).point i ∧
      (∀ r : ℕ, 0 < r → r < k - i →
        ((faceWalkPolyline B vert P d n).intervalPolyline i (k - i)).point r ≠
          (faceWalkPolyline B vert P d n).point i) ∧
      ((faceWalkPolyline B vert P d n).intervalPolyline i (k - i)).image ⊆
        (faceWalkPolyline B vert P d n).image ∧
      (∀ r : ℕ, r < k - i →
        ((faceWalkPolyline B vert P d n).intervalPolyline i (k - i)).segmentAt r =
          (faceWalkPolyline B vert P d n).segmentAt (i + r)) := by
  exact Polyline.exists_firstReturn_intervalPolyline _ i j hij hj hvisit

/-- Helper toward Proposition 5.16: a finite face walk that visits the
geometric image of a vertex twice has a closed first-return subwalk through
that vertex, with no interior visit to the same point. -/
theorem faceWalkPolyline_firstReturn_atVertex {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (d : B.D) (n i j : ℕ)
    (v : V) (hij : i < j)
    (hj : j < (faceWalkPolyline B vert P d n).points.length)
    (hvi : (faceWalkPolyline B vert P d n).point i = P.pos v)
    (hvj : (faceWalkPolyline B vert P d n).point j = P.pos v) :
    ∃ k : ℕ, i < k ∧ k ≤ j ∧
      ((faceWalkPolyline B vert P d n).intervalPolyline i (k - i)).start = P.pos v ∧
      ((faceWalkPolyline B vert P d n).intervalPolyline i (k - i)).finish = P.pos v ∧
      (∀ r : ℕ, 0 < r → r < k - i →
        ((faceWalkPolyline B vert P d n).intervalPolyline i (k - i)).point r ≠ P.pos v) ∧
      ((faceWalkPolyline B vert P d n).intervalPolyline i (k - i)).image ⊆
        (faceWalkPolyline B vert P d n).image ∧
      (∀ r : ℕ, r < k - i →
        ((faceWalkPolyline B vert P d n).intervalPolyline i (k - i)).segmentAt r =
          (faceWalkPolyline B vert P d n).segmentAt (i + r)) := by
  obtain ⟨k, hik, hkj, hs, hf, hint, himage, hsegments⟩ :=
    faceWalkPolyline_firstReturn B vert P d n i j hij hj (hvi.trans hvj.symm)
  refine ⟨k, hik, hkj, hs.trans hvi, hf.trans hvi, ?_, himage, hsegments⟩
  intro r hr0 hrk hpoint
  exact hint r hr0 hrk (hpoint.trans hvi.symm)

end D39FiniteBall

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: if an interval of a face walk has
distinct vertices before closure, its retained dart-arc segment sources
make it a cyclically simple polygon. -/
theorem intervalPolyline_isCyclicSimple_of_faceWalk {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (d : B.D) (n i m : ℕ)
    (hbound : i + m < (faceWalkPolyline B vert P d n).points.length)
    (hlen : 4 ≤ ((faceWalkPolyline B vert P d n).intervalPolyline i m).points.length)
    (hclosed : ((faceWalkPolyline B vert P d n).intervalPolyline i m).start =
      ((faceWalkPolyline B vert P d n).intervalPolyline i m).finish)
    (hinj : ∀ a b : ℕ,
      a < ((faceWalkPolyline B vert P d n).intervalPolyline i m).points.length - 1 →
      b < ((faceWalkPolyline B vert P d n).intervalPolyline i m).points.length - 1 →
      ((faceWalkPolyline B vert P d n).intervalPolyline i m).point a =
        ((faceWalkPolyline B vert P d n).intervalPolyline i m).point b → a = b) :
    ((faceWalkPolyline B vert P d n).intervalPolyline i m).IsCyclicSimple := by
  let c := faceWalkPolyline B vert P d n
  let q := c.intervalPolyline i m
  apply P.isCyclicSimple_of_arc_segment_sources q hlen hclosed hinj
  intro k hk
  have hkm : k < m := by
    rw [Polyline.length_intervalPolyline] at hk
    omega
  obtain ⟨e, a, ha, hstart, hfinish⟩ :=
    faceWalkPolyline_segment_sources B vert P d n (i + k) (by omega)
  refine ⟨e, a, ha, ?_, ?_⟩
  · rw [Polyline.point_intervalPolyline c i m k (by omega)]
    exact hstart
  · rw [Polyline.point_intervalPolyline c i m (k + 1) (by omega)]
    rw [← Nat.add_assoc]
    exact hfinish

/-- Helper toward Proposition 5.16: the polygonal Jordan theorem assigns
inside and outside complementary components to a cyclically simple return
interval from a face walk. This does not yet identify dart-connectivity
classes after deleting its base vertex. -/
theorem intervalPolyline_has_inside_outside_of_faceWalk {V : Type*}
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (d : B.D) (n i m : ℕ)
    (hbound : i + m < (faceWalkPolyline B vert P d n).points.length)
    (hlen : 4 ≤ ((faceWalkPolyline B vert P d n).intervalPolyline i m).points.length)
    (hclosed : ((faceWalkPolyline B vert P d n).intervalPolyline i m).start =
      ((faceWalkPolyline B vert P d n).intervalPolyline i m).finish)
    (hinj : ∀ a b : ℕ,
      a < ((faceWalkPolyline B vert P d n).intervalPolyline i m).points.length - 1 →
      b < ((faceWalkPolyline B vert P d n).intervalPolyline i m).points.length - 1 →
      ((faceWalkPolyline B vert P d n).intervalPolyline i m).point a =
        ((faceWalkPolyline B vert P d n).intervalPolyline i m).point b → a = b) :
    ∃ a b : ℂ,
      a ∈ ((faceWalkPolyline B vert P d n).intervalPolyline i m).inside ∧
      b ∈ ((faceWalkPolyline B vert P d n).intervalPolyline i m).outside ∧
      ((faceWalkPolyline B vert P d n).intervalPolyline i m).inside =
        connectedComponentIn ((faceWalkPolyline B vert P d n).intervalPolyline i m).imageᶜ a ∧
      ((faceWalkPolyline B vert P d n).intervalPolyline i m).outside =
        connectedComponentIn ((faceWalkPolyline B vert P d n).intervalPolyline i m).imageᶜ b ∧
      ((faceWalkPolyline B vert P d n).intervalPolyline i m).image ⊆
        closure ((faceWalkPolyline B vert P d n).intervalPolyline i m).inside ∩
          closure ((faceWalkPolyline B vert P d n).intervalPolyline i m).outside := by
  let q := (faceWalkPolyline B vert P d n).intervalPolyline i m
  exact q.exists_inside_outside_components_cyclic
    (B.intervalPolyline_isCyclicSimple_of_faceWalk vert P d n i m hbound hlen hclosed hinj)

end D39FiniteBall

namespace CombinatorialMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Helper toward Proposition 5.16: retain only rotation and reversal steps
whose two darts are outside the deleted vertex. -/
@[expose] def vertexAvoidingStep (M : CombinatorialMap D)
    (v : VertexQuotient M) (x y : D) : Prop :=
  vertexClass M x ≠ v ∧ vertexClass M y ≠ v ∧
    (M.rot x = y ∨ M.edgeInv x = y)

/-- Helper toward Proposition 5.16: a cut vertex is a vertex whose deletion
leaves at least two equivalence classes of darts under rotation and reversal.
The witnessing darts and every step in their generated connectivity relation
avoid the deleted vertex. -/
@[expose] def isCutVertex (M : CombinatorialMap D) (v : VertexQuotient M) : Prop :=
  ∃ x y : D, vertexClass M x ≠ v ∧ vertexClass M y ≠ v ∧
    ¬ Relation.EqvGen (M.vertexAvoidingStep v) x y

end CombinatorialMap





































end DirectedDistances.PlanarMap
