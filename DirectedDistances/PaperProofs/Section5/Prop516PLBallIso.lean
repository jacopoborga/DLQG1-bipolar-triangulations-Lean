/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomBallIsoPackaging
public import DirectedDistances.PlanarMap.D39PLRestriction
public import DirectedDistances.PlanarMap.D39PLOrientedPlaneHomeomorph
public import DirectedDistances.PlanarMap.D39DrawingRepresentation3

/-! # PL restrictions to Definition 3.8 balls -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open Set Topology

/-- Helper toward Proposition 5.16: the set-based and finset-based least
positive returns define the same rotation, without finiteness of ambient darts. -/
theorem drawingFirstReturnPerm_eq_cyclicFirstReturn
    {D V : Type*} [DecidableEq D]
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (S : Finset D)
    (hper : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (rot ^ k) x.1 ∈ S) :
    drawingFirstReturnPerm P (S : Set D) = cyclicFirstReturn rot S hper := by
  classical
  ext x
  rw [drawingFirstReturnPerm, subsetFirstReturnPerm_apply, permIterateEqPow,
    (firstReturn_spec rot S hper x).1]
  congr 2
  apply Nat.le_antisymm
  · by_contra h
    apply (subsetFirstReturnTime_spec rot (S : Set D)
      (drawingPositiveReturn P (S : Set D)) x).2.2 _
      (cyclicFirstReturnTime_spec rot S hper x).1 (lt_of_not_ge h)
    rw [permIterateEqPow]
    exact (cyclicFirstReturnTime_spec rot S hper x).2.1
  · by_contra h
    apply (cyclicFirstReturnTime_spec rot S hper x).2.2 _
      (subsetFirstReturnTime_spec rot (S : Set D)
        (drawingPositiveReturn P (S : Set D)) x).1 (lt_of_not_ge h)
    have hmem := (subsetFirstReturnTime_spec rot (S : Set D)
      (drawingPositiveReturn P (S : Set D)) x).2.1
    rw [permIterateEqPow] at hmem
    exact hmem

/-- Helper toward Proposition 5.16: the combinatorial ball rotation is
exactly the geometric drawing's first-return rotation. -/
theorem d39BallMap_rot_eq_drawingFirstReturn
    (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M)) (r : ℕ) :
    letI : DecidableEq {d : M.core.D // d ∈ d39BallDarts M r} := Classical.decEq _
    (d39BallMap M r).rot =
      drawingFirstReturnPerm P (d39BallDarts M r : Set M.core.D) := by
  classical
  change cyclicFirstReturn M.core.rot (d39BallDarts M r) _ = _
  exact (drawingFirstReturnPerm_eq_cyclicFirstReturn P (d39BallDarts M r) _).symm

/-- Helper toward Proposition 5.16: restrict a PL drawing of the ambient
rotation system to the exact dart map of its positive-radius faced ball.
The ambient dart and vertex types may be infinite. Only incident vertices
are retained; at positive radius these are precisely the ball vertices. -/
@[expose] def d39FacedBallPLDrawing (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r) :
    PLDrawing (d39FacedBall M r hr).D
      (RestrictedVertex P (d39BallDarts M r : Set M.core.D))
      (d39FacedBall M r hr).map.edgeInv (d39FacedBall M r hr).map.rot
      (restrictedVertex P (d39BallDarts M r : Set M.core.D)) := by
  classical
  let S : Set M.core.D := d39BallDarts M r
  have hS : ∀ d, d ∈ S ↔ M.core.edgeInv d ∈ S :=
    flipClosed_iff P S (d39BallDarts_edgeInv_closed M r)
  have hrot : (d39FacedBall M r hr).map.rot = drawingFirstReturnPerm P S :=
    d39BallMap_rot_eq_drawingFirstReturn M P r
  let Q := restrictDrawing P S hS
  exact {
    flip_involutive := Q.flip_involutive
    flip_ne := Q.flip_ne
    vert_rotation := by intro d; rw [hrot]; exact Q.vert_rotation d
    pos := Q.pos
    pos_injective := Q.pos_injective
    arc := Q.arc
    arc_simple := Q.arc_simple
    arc_length := Q.arc_length
    arc_start := Q.arc_start
    arc_finish := Q.arc_finish
    arc_flip := Q.arc_flip
    interior_disjoint := Q.interior_disjoint
    interior_avoids_vertices := Q.interior_avoids_vertices
    locally_finite := Q.locally_finite
    initial_nonzero := Q.initial_nonzero
    initial_arg_injective := Q.initial_arg_injective
    rotation_agreement := by intro d; rw [hrot]; exact Q.rotation_agreement d
  }

/-- Helper toward Proposition 5.16: the restricted drawing retains the
entire original polyline of each retained dart. -/
theorem d39FacedBallPLDrawing_arc (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r) (d : (d39FacedBall M r hr).D) :
    (d39FacedBallPLDrawing M P r hr).arc d = P.arc d.1 := by
  unfold d39FacedBallPLDrawing
  rfl

/-- Helper toward Proposition 5.16: the restricted drawing retains the
positions of precisely its incident vertices. -/
theorem d39FacedBallPLDrawing_pos (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r)
    (v : RestrictedVertex P (d39BallDarts M r : Set M.core.D)) :
    (d39FacedBallPLDrawing M P r hr).pos v = P.pos v.1 := by
  unfold d39FacedBallPLDrawing
  rfl

/-- Helper toward Proposition 5.16: the incident vertex carrier of the
restriction agrees exactly with the source's positive-radius ball vertices. -/
theorem d39FacedBallPLDrawing_vertex_mem_iff (M : D39RootedMap)
    (r : ℕ) (hr : 0 < r)
    (v : RootedLocallyFiniteVertex M.core.D M.core.rot) :
    (∃ d, d ∈ d39BallDarts M r ∧ d39VertexClass M d = v) ↔
      v ∈ d39BallVertices M r :=
  (d39BallVertices_iff_incident_dart M r hr v).symm

/-- Helper toward Proposition 5.16: the restricted incidence map is onto
its vertex carrier; no isolated ambient vertices are retained. -/
theorem d39FacedBallPLDrawing_vertex_surjective (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r) :
    Function.Surjective
      (restrictedVertex P (d39BallDarts M r : Set M.core.D) :
        (d39FacedBall M r hr).D → _) := by
  rintro ⟨v, d, hd, hv⟩
  exact ⟨⟨d, hd⟩, Subtype.ext hv⟩

/-- Helper toward Proposition 5.16: the restricted vertex carrier is finite,
even when the ambient drawing has infinitely many vertices and darts. -/
theorem d39FacedBallPLDrawing_finite_vertices (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r) :
    Finite (RestrictedVertex P (d39BallDarts M r : Set M.core.D)) :=
  Finite.of_surjective _ (d39FacedBallPLDrawing_vertex_surjective M P r hr)

/-- Helper toward Proposition 5.16: precisely one orbit of a connected finite
PL drawing corresponds to an unbounded complementary component. Externality
means unboundedness of this geometric face, rather than failure of the
`original` tag or incidence to the root edge. -/
theorem existsUnique_plExternalOrbit {V : Type*} [Finite V]
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e) :
    ∃! O : D39BallFaceCycleOrbit B,
      ¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O).val := by
  let R : D39BallFaceCycleRealization B P.toPlaneGraphDrawing :=
    ⟨(Equiv.ofBijective (B.plOrbitFace vert P hvert)
      ⟨B.plOrbitFace_injective vert P hvert hconn,
        B.plOrbitFace_surjective vert P hvert⟩).trans
      P.toPlaneGraphDrawingFaceEquiv.symm⟩
  exact R.existsUnique_externalOrbit

/-- Helper toward Proposition 5.16: select the external orbit only after
proving existence and uniqueness in the finite PL drawing. An arbitrary
`D39FiniteBallWithExternal` marker has no unboundedness guarantee. -/
@[expose] def plExternalOrbit {V : Type*} [Finite V]
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e) :
    D39BallFaceCycleOrbit B :=
  (existsUnique_plExternalOrbit B vert P hvert hconn).exists.choose

/-- Helper toward Proposition 5.16: full characterization of the chosen
external marker, including its uniqueness among all actual face orbits. -/
theorem plExternalOrbit_eq_iff {V : Type*} [Finite V]
    (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (O : D39BallFaceCycleOrbit B) :
    O = plExternalOrbit B vert P hvert hconn ↔
      ¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O).val := by
  have hs := (existsUnique_plExternalOrbit B vert P hvert hconn).exists.choose_spec
  constructor
  · rintro rfl
    exact hs
  · intro hO
    exact (existsUnique_plExternalOrbit B vert P hvert hconn).unique hO hs

/-- Helper toward Proposition 5.16: the positive-radius ball has exactly
one external orbit in its restricted PL drawing, with no ambient finiteness
assumption and no assumption selecting an orbit in advance. -/
theorem d39FacedBallPLDrawing_existsUnique_externalOrbit (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r) :
    ∃! O : D39BallFaceCycleOrbit (d39FacedBall M r hr),
      ¬ Bornology.IsBounded
        ((d39FacedBall M r hr).plOrbitFace
          (restrictedVertex P (d39BallDarts M r : Set M.core.D))
          (d39FacedBallPLDrawing M P r hr)
          (d39FacedBallPLDrawing_vertex_surjective M P r hr) O).val := by
  let := d39FacedBallPLDrawing_finite_vertices M P r hr
  exact existsUnique_plExternalOrbit _ _ _ _ (d39FacedBall_connected M r hr)

/-- Helper toward Proposition 5.16: when all bordering darts belong to a
finite retained set, the whole frontier is covered by their retained arcs.
Local endpoint approximation handles polyline bends in infinite drawings. -/
theorem frontier_subset_retained_arcs_of_dartBorders_mem
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (S : Set D) (hS : S.Finite) (F : P.Face)
    (hkeep : ∀ d, P.dartBorders d F → d ∈ S) :
    frontier F.val ⊆ ⋃ d : S, (P.arc d.1).image := by
  classical
  let : Finite S := hS.to_subtype
  let K := ⋃ d : S, (P.arc d.1).image
  have hclosed : IsClosed K :=
    isClosed_iUnion_of_finite fun d => (P.arc d.1).isCompact_image.isClosed
  intro q hqfront
  by_contra hqK
  obtain ⟨s, hs, hsafe⟩ := Metric.mem_nhds_iff.mp
    (hclosed.isOpen_compl.mem_nhds hqK)
  have hqimage := (P.face_open_frontier_subset_image hvert F).2 hqfront
  have harc : ∃ d, q ∈ (P.arc d).image := by
    rcases hqimage with ⟨v, rfl⟩ | h
    · obtain ⟨d, rfl⟩ := hvert v
      exact ⟨d, Or.inl (P.arc_start d).symm⟩
    · exact h
  obtain ⟨d, hd⟩ := harc
  have hseg : ∃ i, i + 1 < (P.arc d).points.length ∧
      q ∈ (P.arc d).segmentAt i := by
    rcases hd with hstart | ⟨i, hi, hqi⟩
    · refine ⟨0, by have := P.arc_length d; omega, ?_⟩
      rw [hstart, Polyline.segmentAt, Polyline.point_zero_eq_start]
      exact left_mem_segment ℝ _ _
    · exact ⟨i, hi, hqi⟩
  obtain ⟨i, hi, hqi⟩ := hseg
  by_cases hqend : q = (P.arc d).point i ∨ q = (P.arc d).point (i + 1)
  · obtain ⟨x, hx, hxball, hnot⟩ := P.face_endpoint_frontier_not_vertex_mem_ball
      hvert F q d hi hqend (frontier_subset_closure hqfront) hs
    obtain ⟨e, hxe, heF⟩ :=
      P.exists_mem_arc_dartBorders_of_frontier_not_vertex hvert F hx hnot
    exact hsafe hxball (mem_iUnion.mpr ⟨⟨e, hkeep e heF⟩, hxe⟩)
  · have hqopen := mem_openSegment_of_ne_left_right
      (fun he => hqend (Or.inl he.symm)) (fun he => hqend (Or.inr he.symm)) hqi
    rcases (P.mem_closure_face_openSegment_iff_dartBorders hvert d F hi hqopen).mp
        (frontier_subset_closure hqfront) with hF | hF
    · exact hqK (mem_iUnion.mpr
        ⟨⟨d, hkeep d hF⟩, (P.arc d).segmentAt_subset_image hi hqi⟩)
    · apply hqK
      apply mem_iUnion.mpr
      refine ⟨⟨flip d, hkeep (flip d) hF⟩, ?_⟩
      rw [P.arc_image_flip]
      exact (P.arc d).segmentAt_subset_image hi hqi

/-- Helper toward Proposition 5.16: a whole face survives deletion when
its frontier survives. This is equality of components, not just inclusion
of the old face in a newly merged complementary component. -/
theorem exists_face_eq_of_image_subset_of_frontier_subset
    {D V D' V' : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    {flip' : D' → D'} {rot' : Equiv.Perm D'} {vert' : D' → V'}
    (P : PLDrawing D V flip rot vert) (Q : PLDrawing D' V' flip' rot' vert')
    (hvert : Function.Surjective vert) (F : P.Face)
    (himage : Q.image ⊆ P.image) (hfront : frontier F.val ⊆ Q.image) :
    ∃ G : Q.Face, G.val = F.val := by
  obtain ⟨z, hz, hF⟩ := F.property
  have hzF : z ∈ F.val := hF.symm ▸ mem_connectedComponentIn hz
  have hzQ : z ∈ Q.imageᶜ := fun h => hz (himage h)
  have hsub : F.val ⊆ Q.imageᶜ :=
    fun _ hx h => P.face_subset_compl F hx (himage h)
  have hpre : IsPreconnected F.val := by
    rw [hF]
    exact isPreconnected_connectedComponentIn
  have hFcomp : F.val ⊆ connectedComponentIn Q.imageᶜ z :=
    hpre.subset_connectedComponentIn hzF hsub
  have hcompF : connectedComponentIn Q.imageᶜ z ⊆ F.val := by
    apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset
      (P.face_open_frontier_subset_image hvert F).1
      ⟨z, mem_connectedComponentIn hzQ, hzF⟩
    rintro x ⟨hxcl, hxcomp⟩
    by_contra hxF
    have hxfront : x ∈ frontier F.val := by
      rw [frontier, (P.face_open_frontier_subset_image hvert F).1.interior_eq]
      exact ⟨hxcl, hxF⟩
    exact connectedComponentIn_subset Q.imageᶜ z hxcomp (hfront hxfront)
  exact ⟨⟨connectedComponentIn Q.imageᶜ z, z, hzQ, rfl⟩,
    Subset.antisymm hcompF hFcomp⟩

/-- Helper toward Proposition 5.16: the image of the finite ball drawing
is contained in the ambient drawing image. -/
theorem d39FacedBallPLDrawing_image_subset (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r) :
    (d39FacedBallPLDrawing M P r hr).image ⊆ P.image := by
  rintro z (⟨v, rfl⟩ | ⟨d, hd⟩)
  · rw [d39FacedBallPLDrawing_pos]
    exact Or.inl ⟨v.1, rfl⟩
  · rw [d39FacedBallPLDrawing_arc] at hd
    exact Or.inr ⟨d.1, hd⟩

/-- Helper toward Proposition 5.16: every ambient face whose closure
vertices lie in the ball is an actual face orbit of the restricted drawing.
The premise is the closure-of-face retention condition, including unbounded
faces; it assumes neither a face correspondence nor boundary simplicity. -/
theorem d39FacedBallPLDrawing_retained_face_is_orbit (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r) (F : P.Face)
    (hret : ∀ v, P.pos v ∈ closure F.val → v ∈ d39BallVertices M r) :
    ∃ O : D39BallFaceCycleOrbit (d39FacedBall M r hr),
      ((d39FacedBall M r hr).plOrbitFace
        (restrictedVertex P (d39BallDarts M r : Set M.core.D))
        (d39FacedBallPLDrawing M P r hr)
        (d39FacedBallPLDrawing_vertex_surjective M P r hr) O).val = F.val := by
  classical
  have hvert : Function.Surjective (d39VertexClass M) :=
    fun v => ⟨Quotient.out v, Quotient.out_eq' v⟩
  have hkeep : ∀ d, P.dartBorders d F → d ∈ d39BallDarts M r := by
    intro d hd
    apply (mem_d39BallDarts M r d).mpr
    constructor
    · apply hret
      apply P.dartBorders_arc_subset_closure hvert d F hd
      exact Or.inl (P.arc_start d).symm
    · apply hret
      apply P.dartBorders_arc_subset_closure hvert d F hd
      rw [← P.arc_finish d]
      exact (P.arc d).point_last_eq_finish ▸
        (P.arc d).point_mem_image (by have := P.arc_length d; omega)
  have hfront : frontier F.val ⊆ (d39FacedBallPLDrawing M P r hr).image := by
    intro z hz
    obtain ⟨d, hd⟩ := mem_iUnion.mp
      (frontier_subset_retained_arcs_of_dartBorders_mem P hvert
        (d39BallDarts M r : Set M.core.D) (d39BallDarts_finite M r) F hkeep hz)
    right
    exact ⟨d, (d39FacedBallPLDrawing_arc M P r hr d).symm ▸ hd⟩
  obtain ⟨G, hG⟩ := exists_face_eq_of_image_subset_of_frontier_subset P
    (d39FacedBallPLDrawing M P r hr) hvert F
    (d39FacedBallPLDrawing_image_subset M P r hr) hfront
  let := d39FacedBallPLDrawing_finite_vertices M P r hr
  obtain ⟨O, hO⟩ := (d39FacedBall M r hr).plOrbitFace_surjective
    (restrictedVertex P (d39BallDarts M r : Set M.core.D))
    (d39FacedBallPLDrawing M P r hr)
    (d39FacedBallPLDrawing_vertex_surjective M P r hr) G
  exact ⟨O, (congrArg Subtype.val hO).trans hG⟩

namespace D39DrawingRepresentationData

/-- Helper toward Proposition 5.16: a representation identifies the
combinatorial center with the first endpoint of the ordered geometric root. -/
theorem root_vertex_eq {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B) :
    x.vertexEquiv (d39VertexClass M M.rootMark.dart) =
      d39GeomRootVertex B.map B.root := by
  change x.vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot M.rootMark.dart) = _
  rw [x.dart_tail_vertex, x.root_mark]
  rfl

/-- Helper toward Proposition 5.16: adjacency through any geometric edge,
including a missing edge, lifts to an ambient combinatorial dart step. -/
theorem geometricStep_of_adj {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B) {v w : B.V}
    (h : (d39GeomGraph B.map).Adj v w) :
    rootedLocallyFiniteGeometricStep M.core.rot M.core.edgeInv
      (x.vertexEquiv.symm v) (x.vertexEquiv.symm w) := by
  rcases h with ⟨_, e, he | he⟩
  · let d := x.dartEquiv.symm (e, true)
    have hd : x.dartEquiv d = (e, true) := x.dartEquiv.apply_symm_apply _
    refine ⟨d, x.vertexEquiv.injective ?_, x.vertexEquiv.injective ?_⟩
    · rw [x.dart_tail_vertex, hd, Equiv.apply_symm_apply]
      exact he.1
    · rw [x.dart_head_vertex, hd, Equiv.apply_symm_apply]
      exact he.2
  · let d := x.dartEquiv.symm (e, false)
    have hd : x.dartEquiv d = (e, false) := x.dartEquiv.apply_symm_apply _
    refine ⟨d, x.vertexEquiv.injective ?_, x.vertexEquiv.injective ?_⟩
    · rw [x.dart_tail_vertex, hd, Equiv.apply_symm_apply]
      exact he.2
    · rw [x.dart_head_vertex, hd, Equiv.apply_symm_apply]
      exact he.1

/-- Helper toward Proposition 5.16: every combinatorial geometric step
has geometric graph distance at most one, including a loop step. -/
theorem edist_le_one_of_geometricStep
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B)
    {v w : RootedLocallyFiniteVertex M.core.D M.core.rot}
    (h : rootedLocallyFiniteGeometricStep M.core.rot M.core.edgeInv v w) :
    (d39GeomGraph B.map).edist (x.vertexEquiv v) (x.vertexEquiv w) ≤ 1 := by
  apply SimpleGraph.edist_le_one_iff_adj_or_eq.mpr
  by_cases heq : v = w
  · exact Or.inr (congrArg x.vertexEquiv heq)
  · left
    obtain ⟨d, rfl, rfl⟩ := h
    refine ⟨fun hh => heq (x.vertexEquiv.injective hh), (x.dartEquiv d).1, ?_⟩
    rw [x.dart_tail_vertex, x.dart_head_vertex]
    cases hb : (x.dartEquiv d).2
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩

/-- Helper toward Proposition 5.16: a geometric walk back to the root
gives a combinatorial radius witness of exactly its length. -/
theorem withinRadius_of_reverse_walk
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B) {v : B.V}
    (p : (d39GeomGraph B.map).Walk v (d39GeomRootVertex B.map B.root)) :
    D39WithinRadius M p.length (x.vertexEquiv.symm v) := by
  generalize hc : d39GeomRootVertex B.map B.root = c at p
  induction p with
  | nil =>
      rw [← hc, ← root_vertex_eq x, Equiv.symm_apply_apply]
      exact .root
  | cons h p ih =>
      exact .edge (ih hc) (geometricStep_of_adj x h.symm)

/-- Helper toward Proposition 5.16: the representation identifies all
combinatorial and geometric vertex balls, with the same radius and center. -/
theorem ballVertices_iff {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B) (r : ℕ)
    (v : RootedLocallyFiniteVertex M.core.D M.core.rot) :
    x.vertexEquiv v ∈ d39GeomBallVertices B.map B.root r ↔
      v ∈ d39BallVertices M r := by
  rw [mem_d39BallVertices]
  constructor
  · intro hv
    obtain ⟨p, hp⟩ := B.domain.connected (x.vertexEquiv v)
      (d39GeomRootVertex B.map B.root) |>.exists_walk_length_eq_edist
    have hlen : p.length ≤ r := by
      have hcast : (p.length : ℕ∞) ≤ (r : ℕ∞) := by
        rw [hp, SimpleGraph.edist_comm]
        exact hv
      exact_mod_cast hcast
    apply (mem_d39BallVertices M r v).mp
    apply d39BallVertices_mono M hlen
    apply (mem_d39BallVertices M p.length v).mpr
    simpa only [Equiv.symm_apply_apply] using withinRadius_of_reverse_walk x p
  · intro hv
    change (d39GeomGraph B.map).edist (d39GeomRootVertex B.map B.root)
      (x.vertexEquiv v) ≤ (r : ℕ∞)
    induction hv with
    | root => rw [root_vertex_eq x]; exact (SimpleGraph.edist_self).le
    | @stay n v h ih => exact ih.trans (by exact_mod_cast Nat.le_succ n)
    | @edge n v w h hs ih =>
        calc
          _ ≤ (d39GeomGraph B.map).edist (d39GeomRootVertex B.map B.root)
              (x.vertexEquiv v) +
              (d39GeomGraph B.map).edist (x.vertexEquiv v) (x.vertexEquiv w) :=
            SimpleGraph.edist_triangle
          _ ≤ (n : ℕ∞) + 1 := add_le_add ih (edist_le_one_of_geometricStep x hs)
          _ = ((n + 1 : ℕ) : ℕ∞) := by simp only [Nat.cast_add, Nat.cast_one]

end D39DrawingRepresentationData

/-- Helper toward Proposition 5.16: a representation identifies precisely
the induced geometric edges, counting missing and parallel edges separately. -/
theorem d39DrawingRepresentationData_ballDarts_iff
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B) (r : ℕ) (d : M.core.D) :
    d ∈ d39BallDarts M r ↔
      (x.dartEquiv d).1 ∈ d39GeomBallEdges B.map B.root r := by
  rw [mem_d39BallDarts]
  rw [← D39DrawingRepresentationData.ballVertices_iff x r (d39VertexClass M d),
    ← D39DrawingRepresentationData.ballVertices_iff x r
      (d39VertexClass M (M.core.edgeInv d))]
  change (_ ∈ _ ∧ _ ∈ _) ↔ (_ ∈ _ ∧ _ ∈ _)
  change (x.vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot d) ∈ _ ∧
    x.vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot (M.core.edgeInv d)) ∈ _) ↔ _
  rw [x.dart_tail_vertex, x.dart_head_vertex]
  cases hb : (x.dartEquiv d).2
  · exact and_comm
  · rfl

/-- Helper toward Proposition 5.16: the closure-of-face clause of the
geometric source provider is precisely the original-face tag of the faced
ball, for a v3 drawing representation. -/
theorem d39DrawingRepresentationData3_retained_iff_original
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B) (r : ℕ) (d : M.core.D) :
    x.faceOfDart d ∈ d39GeomRetainedFaces B.map B.root r ↔
      d39BallContainsOriginalFace M r d := by
  rw [d39BallContainsOriginalFace_iff]
  constructor
  · intro h e he
    apply (D39DrawingRepresentationData.ballVertices_iff
      x.toD39DrawingRepresentationData r _).mp
    apply h
    exact frontier_subset_closure ((x.vertex_frontier_incidence d _).mpr ⟨e, he, rfl⟩)
  · intro h v hv
    obtain ⟨w, rfl⟩ := x.vertexEquiv.surjective v
    have hfront : B.map.toPlaneMapWithMissing.pos (x.vertexEquiv w) ∈
        frontier (x.faceOfDart d).val := by
      refine ⟨hv, ?_⟩
      intro hi
      exact B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.face_subset_compl_image
        (x.faceOfDart d) (interior_subset hi) (Or.inl ⟨x.vertexEquiv w, rfl⟩)
    obtain ⟨e, he, hew⟩ := (x.vertex_frontier_incidence d w).mp hfront
    apply (D39DrawingRepresentationData.ballVertices_iff
      x.toD39DrawingRepresentationData r w).mpr
    exact hew ▸ h e he

/-- Helper toward Proposition 5.16: the PL realization of a represented
dart traces the stored geometric edge, independently of endpoint order.
The path equality is the explicit meaning of PL realization here. -/
theorem d39PLRepresentation_arc_image
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (harc : ∀ d t, (P.arc d).toPath t = d39DrawingDartArc B x d t)
    (d : M.core.D) :
    (P.arc d).image = Set.range (B.map.toPlaneMapWithMissing.arc (x.dartEquiv d).1) := by
  rw [← Polyline.range_toPath]
  rw [show ((P.arc d).toPath : unitInterval → ℂ) = d39DrawingDartArc B x d from
    funext (harc d)]
  unfold d39DrawingDartArc
  split
  · rfl
  · exact Path.symm_range _

/-- Helper toward Proposition 5.16: compatible PL positions and dart paths
give exactly the represented drawing image, including all geometric edges. -/
theorem d39PLRepresentation_image_eq
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (hpos : ∀ v, P.pos v = B.map.toPlaneMapWithMissing.pos (x.vertexEquiv v))
    (harc : ∀ d t, (P.arc d).toPath t = d39DrawingDartArc B x d t) :
    P.image = B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.image := by
  ext z
  constructor
  · rintro (⟨v, rfl⟩ | ⟨d, hd⟩)
    · exact Or.inl ⟨x.vertexEquiv v, (hpos v).symm⟩
    · right
      exact mem_iUnion.mpr ⟨(x.dartEquiv d).1,
        d39PLRepresentation_arc_image x P harc d ▸ hd⟩
  · rintro (⟨v, rfl⟩ | hz)
    · obtain ⟨w, rfl⟩ := x.vertexEquiv.surjective v
      exact Or.inl ⟨w, hpos w⟩
    · obtain ⟨e, he⟩ := mem_iUnion.mp hz
      let d := x.dartEquiv.symm (e, true)
      right
      refine ⟨d, ?_⟩
      rw [d39PLRepresentation_arc_image x P harc d]
      have hd : x.dartEquiv d = (e, true) := x.dartEquiv.apply_symm_apply _
      rw [hd]
      exact he

/-- Helper toward Proposition 5.16: every face retained by the exact
geometric source-provider clause (c) is an orbit face of the PL ball
restriction. Compatibility of positions and ordered dart paths states
explicitly what it means for this representation to have the PL drawing P. -/
theorem d39PLRepresentation_retained_face_is_orbit
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (hpos : ∀ v, P.pos v = B.map.toPlaneMapWithMissing.pos (x.vertexEquiv v))
    (harc : ∀ d t, (P.arc d).toPath t = d39DrawingDartArc B x d t)
    (r : ℕ) (hr : 0 < r)
    (F : B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
    (hret : F ∈ d39GeomRetainedFaces B.map B.root r) :
    ∃ O : D39BallFaceCycleOrbit (d39FacedBall M r hr),
      ((d39FacedBall M r hr).plOrbitFace
        (restrictedVertex P (d39BallDarts M r : Set M.core.D))
        (d39FacedBallPLDrawing M P r hr)
        (d39FacedBallPLDrawing_vertex_surjective M P r hr) O).val = F.val := by
  let PF : P.Face := ⟨F.val, by
    simpa only [d39PLRepresentation_image_eq x P hpos harc] using F.property⟩
  apply d39FacedBallPLDrawing_retained_face_is_orbit M P r hr PF
  intro v hv
  apply (D39DrawingRepresentationData.ballVertices_iff x r v).mp
  apply hret
  rw [hpos] at hv
  exact hv

/-- Helper toward Proposition 5.16: mark the unique unbounded orbit of
the actual PL ball restriction, retaining the original faced-ball data. -/
@[expose] def d39FacedBallPLWithExternal (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r) : D39FiniteBallWithExternal := by
  letI := d39FacedBallPLDrawing_finite_vertices M P r hr
  exact ⟨d39FacedBall M r hr,
    plExternalOrbit _ _ (d39FacedBallPLDrawing M P r hr)
      (d39FacedBallPLDrawing_vertex_surjective M P r hr)
      (d39FacedBall_connected M r hr)⟩

/-- Helper toward Proposition 5.16: the ball marker is geometrically
external exactly in the sense of being the unique unbounded orbit face. -/
theorem d39FacedBallPLWithExternal_external_iff (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r) (O : D39BallFaceCycleOrbit (d39FacedBall M r hr)) :
    O = (d39FacedBallPLWithExternal M P r hr).externalOrbit ↔
      ¬ Bornology.IsBounded
        ((d39FacedBall M r hr).plOrbitFace
          (restrictedVertex P (d39BallDarts M r : Set M.core.D))
          (d39FacedBallPLDrawing M P r hr)
          (d39FacedBallPLDrawing_vertex_surjective M P r hr) O).val := by
  let := d39FacedBallPLDrawing_finite_vertices M P r hr
  exact plExternalOrbit_eq_iff _ _ _ _ (d39FacedBall_connected M r hr) O

/-- Helper toward Proposition 5.16: the selected external marker of the
restricted ball is unbounded in that drawing. -/
theorem d39FacedBallPLWithExternal_unbounded (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r) :
    ¬ Bornology.IsBounded
      ((d39FacedBall M r hr).plOrbitFace
        (restrictedVertex P (d39BallDarts M r : Set M.core.D))
        (d39FacedBallPLDrawing M P r hr)
        (d39FacedBallPLDrawing_vertex_surjective M P r hr)
        (d39FacedBallPLWithExternal M P r hr).externalOrbit).val :=
  (d39FacedBallPLWithExternal_external_iff M P r hr _).mp rfl















































































end DirectedDistances.PaperProofs.Section5

end
