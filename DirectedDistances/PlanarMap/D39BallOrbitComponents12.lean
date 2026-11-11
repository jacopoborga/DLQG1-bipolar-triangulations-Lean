/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39BallOrbitComponents11
public import DirectedDistances.PlanarMap.D39PLSimpleFaceDisk
public import DirectedDistances.PlanarMap.D39PLArcGluing

/-! # Face-orbit equivalence and simple face regions

Helpers toward Proposition 5.16 (`prop-disk-bs-conv`,
belong to the sole coordinator. These are finite drawing dependencies. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set Topology

/-- Helper toward Proposition 5.16: a nonempty open subset of a connected
set fills that set if its frontier avoids that set. -/
private theorem eq_of_subset_of_frontier_disjoint {F S : Set ℂ}
    (hopen : IsOpen F) (hne : F.Nonempty) (hconn : IsPreconnected S)
    (hsub : F ⊆ S) (hdis : Disjoint (frontier F) S) : F = S := by
  apply Subset.antisymm hsub
  apply hconn.subset_of_closure_inter_subset hopen
  · obtain ⟨x, hx⟩ := hne
    exact ⟨x, hsub hx, hx⟩
  · rintro x ⟨hxcl, hxS⟩
    by_contra hxF
    have hxfront : x ∈ frontier F := by
      rw [frontier, hopen.interior_eq]
      exact ⟨hxcl, hxF⟩
    exact Set.disjoint_left.mp hdis hxfront hxS

namespace D39FiniteBall

variable {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
  (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
  (hvert : Function.Surjective vert)
  (hconn : ∀ d e : B.D, Relation.EqvGen
    (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)

include hconn



theorem plDartFace_sameCycle_of_eq (d e : B.D)
    (hface : B.plDartFace vert P hvert d = B.plDartFace vert P hvert e) :
    B.map.faceSucc.SameCycle d e :=
  (B.common_face_orbit_unique_and_eulerChar_eq_two vert P hvert hconn).1 d e hface

/-- Helper toward Proposition 5.16: distinct face-successor orbits have
distinct geometric faces in a connected drawing. -/
theorem plOrbitFace_injective :
    Function.Injective (B.plOrbitFace vert P hvert) := by
  intro O Q hface
  obtain ⟨d, hd⟩ := O.property
  obtain ⟨e, he⟩ := Q.property
  have hdmem : d ∈ O.val := hd.symm ▸ Equiv.Perm.SameCycle.rfl
  have hemem : e ∈ Q.val := he.symm ▸ Equiv.Perm.SameCycle.rfl
  have hde : B.map.faceSucc.SameCycle d e :=
    B.plDartFace_sameCycle_of_eq vert P hvert hconn d e
      ((B.plOrbitFace_eq_plDartFace_of_mem vert P hvert O d hdmem).symm.trans
        (hface.trans (B.plOrbitFace_eq_plDartFace_of_mem vert P hvert Q e hemem)))
  apply Subtype.ext
  rw [hd, he]
  ext x
  exact ⟨fun hx => hde.symm.trans hx, fun hx => hde.trans hx⟩

/-- Helper toward Proposition 5.16: U2, the equivalence between actual
face-successor orbits and geometric complementary faces. -/
def plFaceOrbitEquiv [Finite V]
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e) :
    D39BallFaceCycleOrbit B ≃ P.toPlaneGraphDrawing.Face :=
  (Equiv.ofBijective (B.plOrbitFace vert P hvert)
    ⟨B.plOrbitFace_injective vert P hvert hconn,
      B.plOrbitFace_surjective vert P hvert⟩).trans
    P.toPlaneGraphDrawingFaceEquiv.symm



theorem dartBorders_plOrbitFace_iff (O : D39BallFaceCycleOrbit B) (d : B.D) :
    P.dartBorders d (B.plOrbitFace vert P hvert O) ↔ d ∈ O.val := by
  constructor
  · intro hd
    obtain ⟨e, he⟩ := O.property
    have hemem : e ∈ O.val := he.symm ▸ Equiv.Perm.SameCycle.rfl
    have hface : B.plDartFace vert P hvert e = B.plDartFace vert P hvert d :=
      (B.plOrbitFace_eq_plDartFace_of_mem vert P hvert O e hemem).symm.trans
        ((B.plDartFace_eq_iff vert P hvert d _).mpr hd).symm
    rw [he]
    exact B.plDartFace_sameCycle_of_eq vert P hvert hconn e d hface
  · intro hd
    exact (B.plOrbitFace_eq_iff vert P hvert O d hd _).mp rfl

/-- Helper toward Proposition 5.16: the complete frontier of an orbit's
geometric face is exactly the union of that orbit's closed dart arcs. -/
theorem frontier_plOrbitFace_eq_plOrbitBoundary (O : D39BallFaceCycleOrbit B) :
    frontier (B.plOrbitFace vert P hvert O).val = B.plOrbitBoundary vert P O := by
  rw [P.frontier_face_eq_iUnion_dartBorders_arcs hvert]
  simp only [plOrbitBoundary, B.dartBorders_plOrbitFace_iff vert P hvert hconn]





theorem plOrbitFace_eq_inside_or_outside_of_cyclicSimple_boundary
    (O : D39BallFaceCycleOrbit B) (q : Polyline)
    (hclosed : q.start = q.finish) (hc : q.IsCyclicSimple)
    (hboundaryEq : q.image = B.plOrbitBoundary vert P O) :
    (B.plOrbitFace vert P hvert O).val = q.inside ∨
      (B.plOrbitFace vert P hvert O).val = q.outside := by
  have hfront : frontier (B.plOrbitFace vert P hvert O).val = q.image :=
    (B.frontier_plOrbitFace_eq_plOrbitBoundary vert P hvert hconn O).trans
      hboundaryEq.symm
  obtain ⟨_, hfaceConn, hside, _, _⟩ :=
    B.plOrbitFace_windingSide_of_cyclicSimple_boundary vert P hvert O q hclosed hc
      hboundaryEq.subset
  have hopen := (P.face_open_frontier_subset_image hvert
    (B.plOrbitFace vert P hvert O)).1
  obtain ⟨hinConn, houtConn⟩ := Polyline.isConnected_inside_outside_cyclic q hc
  rcases hside with hin | hout
  · left
    apply eq_of_subset_of_frontier_disjoint hopen hfaceConn.nonempty
      hinConn.isPreconnected hin
    rw [hfront]
    exact Set.disjoint_left.mpr (fun _ hxq hxin => hxin.1 hxq)
  · right
    apply eq_of_subset_of_frontier_disjoint hopen hfaceConn.nonempty
      houtConn.isPreconnected hout
    rw [hfront]
    exact Set.disjoint_left.mpr (fun _ hxq hxout => hxout.1 hxq)

/-- Helper toward Proposition 5.16: boundedness selects the inside for
a face whose whole orbit boundary is a cyclically simple closed polygon. -/
theorem plOrbitFace_eq_inside_of_isBounded_cyclicSimple_boundary
    (O : D39BallFaceCycleOrbit B) (q : Polyline)
    (hclosed : q.start = q.finish) (hc : q.IsCyclicSimple)
    (hboundaryEq : q.image = B.plOrbitBoundary vert P O)
    (hbounded : Bornology.IsBounded (B.plOrbitFace vert P hvert O).val) :
    (B.plOrbitFace vert P hvert O).val = q.inside := by
  rcases B.plOrbitFace_eq_inside_or_outside_of_cyclicSimple_boundary
      vert P hvert hconn O q hclosed hc hboundaryEq with hin | hout
  · exact hin
  · rw [hout] at hbounded
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hbounded
    obtain ⟨z, hz, hRz⟩ := q.outside_unbounded hclosed R
    exact False.elim ((not_le_of_gt hRz) (hR z hz))

/-- Helper toward Proposition 5.16: the closure of a bounded face with
a cyclically simple whole orbit boundary has a closed-disk chart, taking
the model unit circle exactly onto that polygon; its frontier is the same
polygon image. The chart uses the proved polygonal arc-gluing theorem. -/
theorem exists_plOrbitFace_disk_chart_of_isBounded_cyclicSimple_boundary
    (O : D39BallFaceCycleOrbit B) (q : Polyline)
    (hclosed : q.start = q.finish) (hc : q.IsCyclicSimple)
    (hboundaryEq : q.image = B.plOrbitBoundary vert P O)
    (hbounded : Bornology.IsBounded (B.plOrbitFace vert P hvert O).val) :
    frontier (B.plOrbitFace vert P hvert O).val = q.image ∧
      ∃ h : Metric.closedBall (0 : ℂ) 1 ≃ₜ closure (B.plOrbitFace vert P hvert O).val,
        ∀ z : Metric.closedBall (0 : ℂ) 1,
          (h z : ℂ) ∈ q.image ↔ ‖(z : ℂ)‖ = 1 := by
  refine ⟨(B.frontier_plOrbitFace_eq_plOrbitBoundary vert P hvert hconn O).trans
    hboundaryEq.symm, ?_⟩
  rw [B.plOrbitFace_eq_inside_of_isBounded_cyclicSimple_boundary
    vert P hvert hconn O q hclosed hc hboundaryEq hbounded]
  exact q.exists_polygon_disk_chart hc

end D39FiniteBall
end DirectedDistances.PlanarMap
end
