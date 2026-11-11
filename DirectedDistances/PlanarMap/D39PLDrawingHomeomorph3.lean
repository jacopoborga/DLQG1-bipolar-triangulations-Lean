/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLDrawingHomeomorph2
public import DirectedDistances.PlanarMap.D39BallOrbitComponents12

/-! # Exterior extensions from polygon boundaries

Helpers toward Proposition 5.16. The outside extension property is an explicit
premise here; its general proof is a separate obligation. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set Topology

/-- Helper toward Proposition 5.16: every homeomorphism of cyclically simple
polygon boundaries has an extension to the corresponding closed outsides. -/
@[expose] def PolygonOutsideExtension : Prop :=
  ∀ (c c' : Polyline) (hc : c.IsCyclicSimple) (_hc' : c'.IsCyclicSimple)
    (phi : c.image ≃ₜ c'.image),
    ∃ H : closure c.outside ≃ₜ closure c'.outside,
      ∀ x : c.image,
        (H ⟨x, c.image_subset_closure_outside_cyclic hc x.property⟩ : ℂ) =
          (phi x : ℂ)

namespace D39FiniteBall

variable {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
  (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
  (hvert : Function.Surjective vert)
  (hconn : ∀ d e : B.D, Relation.EqvGen
    (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)

include hconn

omit [Finite V] in
/-- Helper toward Proposition 5.16: an unbounded orbit face with a closed
cyclically simple whole boundary is its polygon's outside region. -/
theorem plOrbitFace_eq_outside_of_not_isBounded_cyclicSimple_boundary
    (O_ext : D39BallFaceCycleOrbit B) (q : Polyline)
    (hclosed : q.start = q.finish) (hc : q.IsCyclicSimple)
    (hq : q.image = B.plOrbitBoundary vert P O_ext)
    (hunbounded : ¬ Bornology.IsBounded
      (B.plOrbitFace vert P hvert O_ext).val) :
    (B.plOrbitFace vert P hvert O_ext).val = q.outside := by
  rcases B.plOrbitFace_eq_inside_or_outside_of_cyclicSimple_boundary
      vert P hvert hconn O_ext q hclosed hc hq with hin | hout
  · have hbounded : Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val :=
      hin ▸ q.isBounded_inside hclosed
    exact (hunbounded hbounded).elim
  · exact hout

omit [Finite V] in
/-- Helper toward Proposition 5.16: polygon outside extensions induce the
required extension over the marked unbounded orbit face. -/
theorem exists_outer_face_extension_of_polygonOutsideExtension
    (f : B.PLImageHomeomorph vert P P')
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val))
    (q q' : Polyline)
    (hclosed : q.start = q.finish) (hc : q.IsCyclicSimple)
    (hq : q.image = B.plOrbitBoundary vert P O_ext)
    (hclosed' : q'.start = q'.finish) (hc' : q'.IsCyclicSimple)
    (hq' : q'.image = B.plOrbitBoundary vert P' O_ext)
    (hpoly : PolygonOutsideExtension) :
    ∃ H : closure (B.plOrbitFace vert P hvert O_ext).val ≃ₜ
        closure (B.plOrbitFace vert P' hvert O_ext).val,
      ∀ (x : ℂ) (hx : x ∈ frontier (B.plOrbitFace vert P hvert O_ext).val),
        (H ⟨x, frontier_subset_closure hx⟩ : ℂ) =
          (f.toHomeomorph ⟨x,
            (P.face_open_frontier_subset_image hvert _).2 hx⟩ : ℂ) := by
  have hface : (B.plOrbitFace vert P hvert O_ext).val = q.outside :=
    B.plOrbitFace_eq_outside_of_not_isBounded_cyclicSimple_boundary
      vert P hvert hconn O_ext q hclosed hc hq hext.1
  have hface' : (B.plOrbitFace vert P' hvert O_ext).val = q'.outside :=
    B.plOrbitFace_eq_outside_of_not_isBounded_cyclicSimple_boundary
      vert P' hvert hconn O_ext q' hclosed' hc' hq' hext.2
  let phi : q.image ≃ₜ q'.image :=
    (Homeomorph.setCongr hq).trans
      ((B.plOrbitBoundaryHomeomorph vert P P' f.toHomeomorph f.arc_image O_ext).trans
        (Homeomorph.setCongr hq'.symm))
  obtain ⟨Hout, hHout⟩ := hpoly q q' hc hc' phi
  let H := (Homeomorph.setCongr (congrArg closure hface)).trans
    (Hout.trans (Homeomorph.setCongr (congrArg closure hface').symm))
  refine ⟨H, ?_⟩
  intro x hx
  have hxq : x ∈ q.image := by
    rw [hq, ← B.frontier_plOrbitFace_eq_plOrbitBoundary vert P hvert hconn O_ext]
    exact hx
  have hboundary :
      (phi ⟨x, hxq⟩ : ℂ) =
        (f.toHomeomorph ⟨x,
          B.plOrbitBoundary_subset_image vert P O_ext (hq ▸ hxq)⟩ : ℂ) := by
    change (B.plOrbitBoundaryHomeomorph vert P P' f.toHomeomorph f.arc_image
      O_ext ⟨x, hq ▸ hxq⟩ : ℂ) = _
    rw [B.plOrbitBoundaryHomeomorph_apply vert P P' f.toHomeomorph
      f.arc_image O_ext ⟨x, hq ▸ hxq⟩]
  calc
    (H ⟨x, frontier_subset_closure hx⟩ : ℂ) =
        (Hout ⟨x, q.image_subset_closure_outside_cyclic hc hxq⟩ : ℂ) := by
          rfl
    _ = (phi ⟨x, hxq⟩ : ℂ) := hHout ⟨x, hxq⟩
    _ = (f.toHomeomorph ⟨x,
          (P.face_open_frontier_subset_image hvert _).2 hx⟩ : ℂ) := by
          rw [hboundary]

/-- Helper toward Proposition 5.16: simple polygon boundaries on all orbit
faces, together with the polygon outside extension property, give a plane
homeomorphism extending the drawing image homeomorphism. -/
theorem exists_plane_homeomorph_of_simple_orbit_boundaries
    (f : B.PLImageHomeomorph vert P P')
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val))
    (hsimple : ∀ O : D39BallFaceCycleOrbit B,
      ∃ q q' : Polyline,
        q.start = q.finish ∧ q.IsCyclicSimple ∧
        q.image = B.plOrbitBoundary vert P O ∧
        q'.start = q'.finish ∧ q'.IsCyclicSimple ∧
        q'.image = B.plOrbitBoundary vert P' O)
    (hpoly : PolygonOutsideExtension) :
    ∃ H : ℂ ≃ₜ ℂ,
      (∀ x : P.image, H x = (f.toHomeomorph x : ℂ)) ∧
        ∀ d : B.D, H '' (P.arc d).image = (P'.arc d).image := by
  have hsimple' : ∀ O : D39BallFaceCycleOrbit B, O ≠ O_ext →
      ∃ q q' : Polyline,
        q.start = q.finish ∧ q.IsCyclicSimple ∧
        q.image = B.plOrbitBoundary vert P O ∧
        q'.start = q'.finish ∧ q'.IsCyclicSimple ∧
        q'.image = B.plOrbitBoundary vert P' O := by
    intro O _
    exact hsimple O
  obtain ⟨q, q', hclosed, hc, hq, hclosed', hc', hq'⟩ := hsimple O_ext
  have hout := B.exists_outer_face_extension_of_polygonOutsideExtension
    vert P P' hvert hconn f O_ext hext q q' hclosed hc hq hclosed' hc' hq' hpoly
  exact B.exists_plane_homeomorph_of_outer_face_extension
    vert P P' hvert hconn f O_ext hext hsimple' hout

end D39FiniteBall
end DirectedDistances.PlanarMap
end
