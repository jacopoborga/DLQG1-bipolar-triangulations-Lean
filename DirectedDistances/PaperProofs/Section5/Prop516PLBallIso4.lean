/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516PLBallIso3
public import DirectedDistances.PlanarMap.D39PLDrawingUniqueness4

/- # Winding incidence and exterior transport for represented PL balls

is claimed. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open Set Topology

/-- Helper toward Proposition 5.16: the representation's stored-direction
side clause gives the left winding test along the actual PL dart, including
darts that reverse the stored geometric edge. -/
theorem d39PLRepresentation_face_leftAtOn
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (harc : ∀ d t, (P.arc d).toPath t = d39DrawingDartArc B x d t)
    (d : M.core.D) (s : {t : unitInterval // t ∈ openParams}) :
    LeftAtOn (x.faceOfDart d).val (P.arc d).toPath s := by
  have hside := x.face_left_of_dart d
  cases hb : (x.dartEquiv d).2
  · rw [hb] at hside
    have hs : ∀ t : {t : unitInterval // t ∈ openParams},
        RightAtOn (x.faceOfDart d).val
          (B.map.toPlaneMapWithMissing.arc (x.dartEquiv d).1) t := hside
    have hl := (forall_leftAtOn_symm_iff (x.faceOfDart d).val
      (B.map.toPlaneMapWithMissing.arc (x.dartEquiv d).1)).mpr hs
    exact (leftAtOn_congr_fun (x.faceOfDart d).val _ _ s (fun t => by
      rw [harc, d39DrawingDartArc, hb]
      rfl)).mpr (hl s)
  · rw [hb] at hside
    exact (leftAtOn_congr_fun (x.faceOfDart d).val _ _ s (fun t => by
      rw [harc, d39DrawingDartArc, hb]
      rfl)).mpr (hside s)




theorem d39PLRepresentation_arc_subset_closure_face
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (harc : ∀ d t, (P.arc d).toPath t = d39DrawingDartArc B x d t)
    (d : M.core.D) :
    (P.arc d).image ⊆ closure (x.faceOfDart d).val := by
  have hsub : openParams ⊆
      (P.arc d).toPath ⁻¹' closure (x.faceOfDart d).val := by
    intro s hs
    obtain ⟨a, b, ha, has, hsb, hb, q, hqi, hq, hcl⟩ :=
      d39PLRepresentation_face_leftAtOn x P harc d ⟨s, hs⟩
    exact closure_mono
      (show {w : ℂ | w ∈ (x.faceOfDart d).val ∧
        HasWinding ((edgeSubarc (P.arc d).toPath a b
          (le_of_lt (lt_trans has hsb))).trans q) w 1} ⊆
            (x.faceOfDart d).val from fun _ hz => hz.1) hcl
  have hclosed : IsClosed
      ((P.arc d).toPath ⁻¹' closure (x.faceOfDart d).val) :=
    isClosed_closure.preimage (P.arc d).toPath.continuous
  have hall := closure_minimal hsub hclosed
  rw [PlaneGraphDrawing.dense_openParams.closure_eq] at hall
  intro z hz
  rw [← Polyline.range_toPath] at hz
  obtain ⟨t, rfl⟩ := hz
  exact hall (Set.mem_univ t)

/- Helper toward Proposition 5.16: a represented face borders one of
the two darts of the given edge. This records the remaining orientation -/
theorem d39PLRepresentation_dartBorders_or_flip
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (hpos : ∀ v, P.pos v = B.map.toPlaneMapWithMissing.pos (x.vertexEquiv v))
    (harc : ∀ d t, (P.arc d).toPath t = d39DrawingDartArc B x d t)
    (d : M.core.D) :
    P.dartBorders d (d39PLRepresentationFace x P hpos harc (x.faceOfDart d)) ∨
      P.dartBorders (M.core.edgeInv d)
        (d39PLRepresentationFace x P hpos harc (x.faceOfDart d)) := by
  have hi : 0 + 1 < (P.arc d).points.length := P.arc_length d
  have hq := midpoint_mem_openSegment (𝕜 := ℝ)
    ((P.arc d).point 0) ((P.arc d).point 1)
  apply (P.mem_closure_face_openSegment_iff_dartBorders
    (fun v => Quotient.exists_rep v) d
    (d39PLRepresentationFace x P hpos harc (x.faceOfDart d)) hi hq).mp
  exact d39PLRepresentation_arc_subset_closure_face x P harc d
    ((P.arc d).segmentAt_subset_image hi (openSegment_subset_segment ℝ _ _ hq))

/- Helper toward Proposition 5.16: DU1 verbatim from
`D39PLDrawingUniqueness3.lean:472`, with its complete augmentation data and
authorized for conditional helpers; defining the proposition does not prove it. -/
@[expose] def D39PLDrawingUniquenessDU1 : Prop :=
  ∀ {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val)),
  ∃ (n : ℕ) (C : D39FiniteBall) (v : C.D → V ⊕ Fin n)
    (ι : B.D ↪ C.D)
    (Q Q' : PLDrawing C.D (V ⊕ Fin n) C.map.edgeInv C.map.rot v)
    (hv : Function.Surjective v) (E : D39BallFaceCycleOrbit C)
    (I : D39BallFaceCycleOrbit B → Set (D39BallFaceCycleOrbit C)),
    (∀ d e : C.D, Relation.EqvGen
      (fun x y => C.map.rot x = y ∨ C.map.edgeInv x = y) d e) ∧
    C.rootDart = ι B.rootDart ∧
    (∀ d : B.D, C.map.edgeInv (ι d) = ι (B.map.edgeInv d)) ∧
    (∀ d : B.D, v (ι d) = Sum.inl (vert d)) ∧
    (∀ d : B.D, C.missing (ι d) ↔ B.missing d) ∧
    (∀ d : B.D, C.tail (ι d) ↔ B.tail d) ∧
    (∀ x : V, Q.pos (Sum.inl x) = P.pos x) ∧
    (∀ x : V, Q'.pos (Sum.inl x) = P'.pos x) ∧
    (∀ d : B.D, Q.arc (ι d) = P.arc d) ∧
    (∀ d : B.D, Q'.arc (ι d) = P'.arc d) ∧
    (¬ Bornology.IsBounded (C.plOrbitFace v Q hv E).val) ∧
    (¬ Bornology.IsBounded (C.plOrbitFace v Q' hv E).val) ∧
    (∀ O : D39BallFaceCycleOrbit C, ∃ d ∈ O.val,
      (O = E → Function.minimalPeriod C.map.faceSucc d = 4) ∧
      (O ≠ E → Function.minimalPeriod C.map.faceSucc d = 3) ∧
      Set.InjOn (fun k : ℕ => v ((C.map.faceSucc : C.D → C.D)^[k] d))
        (Set.Iio (Function.minimalPeriod C.map.faceSucc d))) ∧
    (∀ O : D39BallFaceCycleOrbit B,
      closure (B.plOrbitFace vert P hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace v Q hv S).val) ∧
    (∀ O : D39BallFaceCycleOrbit B,
      closure (B.plOrbitFace vert P' hvert O).val =
        ⋃ S ∈ I O, closure (C.plOrbitFace v Q' hv S).val)

/-- Helper toward Proposition 5.16: conditional only on general DU1,
preservation of the selected exterior is equivalent to existence of a plane
homeomorphism transporting every open orbit face. In particular, using the
DU1 homeomorphism to establish this exterior condition would be circular. -/
theorem d39FacedBallPLDrawing_external_iff_exists_face_homeomorph
    (hDU1 : D39PLDrawingUniquenessDU1.{0})
    {M N : D39RootedMap}
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (Q : PLDrawing N.core.D (RootedLocallyFiniteVertex N.core.D N.core.rot)
      N.core.edgeInv N.core.rot (d39VertexClass N))
    (r : ℕ) (hr : 0 < r)
    (I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr)) :
    (∀ d : (d39FacedBall M r hr).D,
      I.toEquiv d ∈ (d39FacedBallPLWithExternal N Q r hr).externalOrbit.val ↔
        d ∈ (d39FacedBallPLWithExternal M P r hr).externalOrbit.val) ↔
    ∃ H : ℂ ≃ₜ ℂ,
      ∀ O : D39BallFaceCycleOrbit (d39FacedBall M r hr),
        H '' ((d39FacedBall M r hr).plOrbitFace
          (restrictedVertex P (d39BallDarts M r : Set M.core.D))
          (d39FacedBallPLDrawing M P r hr)
          (d39FacedBallPLDrawing_vertex_surjective M P r hr) O).val =
        ((d39FacedBall N r hr).plOrbitFace
          (restrictedVertex Q (d39BallDarts N r : Set N.core.D))
          (d39FacedBallPLDrawing N Q r hr)
          (d39FacedBallPLDrawing_vertex_surjective N Q r hr)
          (plBallFaceOrbitMap I O)).val := by
  constructor
  · intro hext
    let J : D39BallIsoWithExternal
        (d39FacedBallPLWithExternal M P r hr)
        (d39FacedBallPLWithExternal N Q r hr) := ⟨I, hext⟩
    let := d39FacedBallPLDrawing_finite_vertices N Q r hr
    obtain ⟨H, _hor, _hp, _ha, hfaces⟩ := exists_plBallIso_homeomorph (@hDU1) J
      (restrictedVertex P (d39BallDarts M r : Set M.core.D))
      (restrictedVertex Q (d39BallDarts N r : Set N.core.D))
      (d39FacedBallPLDrawing M P r hr) (d39FacedBallPLDrawing N Q r hr)
      (d39FacedBallPLDrawing_vertex_surjective M P r hr)
      (d39FacedBallPLDrawing_vertex_surjective N Q r hr)
      (d39FacedBall_connected N r hr)
      ⟨d39FacedBallPLWithExternal_unbounded M P r hr,
        d39FacedBallPLWithExternal_unbounded N Q r hr⟩
    exact ⟨H, hfaces⟩
  · rintro ⟨H, hfaces⟩
    apply (d39FacedBallPLDrawing_external_iff_unbounded P Q r hr I).mpr
    rw [← hfaces (d39FacedBallPLWithExternal M P r hr).externalOrbit]
    exact fun h => d39FacedBallPLWithExternal_unbounded M P r hr
      ((isBounded_planeHomeomorph_image_iff H _).mp h)

/-- Helper toward Proposition 5.16: a retained original face is the unique
restricted orbit face adjacent to one of the two darts of its represented
edge. The orientation alternative is kept explicit. -/
theorem d39PLRepresentation_original_face_unique_adjacent_orbit
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (hpos : ∀ v, P.pos v = B.map.toPlaneMapWithMissing.pos (x.vertexEquiv v))
    (harc : ∀ d t, (P.arc d).toPath t =
      d39DrawingDartArc B x.toD39DrawingRepresentationData d t)
    (r : ℕ) (hr : 0 < r) (d : (d39FacedBall M r hr).D)
    (hd : d ∈ (d39FacedBall M r hr).original) :
    ∃! O : D39BallFaceCycleOrbit (d39FacedBall M r hr),
      ((d39FacedBall M r hr).plOrbitFace
        (restrictedVertex P (d39BallDarts M r : Set M.core.D))
        (d39FacedBallPLDrawing M P r hr)
        (d39FacedBallPLDrawing_vertex_surjective M P r hr) O).val =
          (x.faceOfDart d.1).val ∧
      (d ∈ O.val ∨ (d39FacedBall M r hr).map.edgeInv d ∈ O.val) := by
  let F := d39PLRepresentationFace x.toD39DrawingRepresentationData P hpos harc
    (x.faceOfDart d.1)
  have hret : x.faceOfDart d.1 ∈ d39GeomRetainedFaces B.map B.root r :=
    (d39DrawingRepresentationData3_retained_iff_original x r d.1).mpr hd
  have hretP : ∀ v, P.pos v ∈ closure F.val → v ∈ d39BallVertices M r := by
    intro v hv
    apply (D39DrawingRepresentationData.ballVertices_iff
      x.toD39DrawingRepresentationData r v).mp
    apply hret
    rw [← hpos]
    exact hv
  obtain ⟨O, ⟨hO, hinc⟩, _⟩ :=
    d39FacedBallPLDrawing_retained_face_unique_orbit M P r hr F hretP
  refine ⟨O, ⟨hO, ?_⟩, ?_⟩
  · rcases d39PLRepresentation_dartBorders_or_flip
      x.toD39DrawingRepresentationData P hpos harc d.1 with hleft | hright
    · exact Or.inl ((hinc d).mpr hleft)
    · exact Or.inr ((hinc ((d39FacedBall M r hr).map.edgeInv d)).mpr hright)
  · intro Q hQ
    apply (d39FacedBall M r hr).plOrbitFace_injective
      (restrictedVertex P (d39BallDarts M r : Set M.core.D))
      (d39FacedBallPLDrawing M P r hr)
      (d39FacedBallPLDrawing_vertex_surjective M P r hr)
      (d39FacedBall_connected M r hr)
    exact Subtype.ext (hQ.1.trans hO.symm)


























































































































































end DirectedDistances.PaperProofs.Section5

end
