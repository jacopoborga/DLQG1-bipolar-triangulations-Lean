/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516BallMarkerPreservation
public import DirectedDistances.PaperProofs.Section5.Prop516PLExteriorTransport
public import DirectedDistances.PaperProofs.Section5.Prop516PLDrawingAugmentation

/-! # Reverse comparison conditional on the exact DU1 construction

construction, displayed in full below as the explicitly authorized input
`hDU1`. The proved plane comparison preserves restricted orbit faces.
The retained ambient-face assembly and the unconditional exterior transport
belong to the sole coordinator; no numbered paper result is claimed. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5.ReverseComparisonFromDU1

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open Set Topology

section DU1

-- Exactly the complete DU1 target in Prop516PLDrawingAugmentation:402–438.
-- This is a carried open construction, not an axiom or a source premise.
variable
    (hDU1 :
      ∀ {V : Type} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
        (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
        (hvert : Function.Surjective vert)
        (_hconn : ∀ d e : B.D, Relation.EqvGen
          (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
        (O_ext : D39BallFaceCycleOrbit B)
        (_hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
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
            ⋃ S ∈ I O, closure (C.plOrbitFace v Q' hv S).val))

include hDU1 in
/-- Helper toward Proposition 5.16: apply simple-exterior plane uniqueness
to the common quadrilateral supplied by DU1, then restrict using its joint
closure decompositions. The original exterior need not be simple. -/
theorem exists_plane_homeomorph_of_du1
    {V : Type} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val)) :
    ∃ H : ℂ ≃ₜ ℂ, OrientationPreserving H ∧
      (∀ x : V, H (P.pos x) = P'.pos x) ∧
      (∀ d, H '' (P.arc d).image = (P'.arc d).image) ∧
      (H '' P.image = P'.image) ∧
      (∀ O : D39BallFaceCycleOrbit B,
        H '' closure (B.plOrbitFace vert P hvert O).val =
          closure (B.plOrbitFace vert P' hvert O).val) ∧
      (∀ O : D39BallFaceCycleOrbit B,
        H '' (B.plOrbitFace vert P hvert O).val =
          (B.plOrbitFace vert P' hvert O).val) := by
  obtain ⟨n, C, v, ι, Q, Q', hv, E, I, hc, _hr, _hf, _hv, _hm, _ht,
    hp, hp', ha, ha', hu, hu', hshape, hcover, hcover'⟩ :=
    hDU1 B vert P P' hvert hconn O_ext hext
  obtain ⟨a, haE, hfour, _hthree, hinj⟩ := hshape E
  have hboundary : ∃ a ∈ E.val,
      3 ≤ Function.minimalPeriod C.map.faceSucc a ∧
      Set.InjOn (fun k : ℕ => v ((C.map.faceSucc : C.D → C.D)^[k] a))
        (Set.Iio (Function.minimalPeriod C.map.faceSucc a)) := by
    refine ⟨a, haE, ?_, hinj⟩
    rw [hfour rfl]
    exact Nat.le_succ 3
  obtain ⟨H, hor, hQpos, hQarc, _hQimage, hQclosed, _hQface⟩ :=
    C.exists_plane_homeomorph_of_simple_exterior v Q Q' hv hc E ⟨hu, hu'⟩ hboundary
  obtain ⟨hpos, harc, himage⟩ :=
    P.restrict_plane_homeomorph P' Q Q' ι Sum.inl hp hp' ha ha' H hQpos hQarc
  have hclosed (O : D39BallFaceCycleOrbit B) :
      H '' closure (B.plOrbitFace vert P hvert O).val =
        closure (B.plOrbitFace vert P' hvert O).val := by
    rw [hcover O, hcover' O]
    simp only [Set.image_iUnion, hQclosed]
  refine ⟨H, hor, hpos, harc, himage, hclosed, ?_⟩
  intro O
  rw [← P.closure_face_diff_image hvert, ← P'.closure_face_diff_image hvert,
    Set.image_sdiff H.injective, hclosed O, himage]

include hDU1 in
/-- Helper toward Proposition 5.16: the DU1 plane comparison preserves
each directed dart by a strictly increasing interval homeomorphism. -/
theorem exists_plDrawing_homeomorph_of_du1
    {V : Type} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val)) :
    ∃ H : ℂ ≃ₜ ℂ, OrientationPreserving H ∧
      (∀ x : V, H (P.pos x) = P'.pos x) ∧
      (∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
        ∀ t, H ((P.arc d).toPath t) = (P'.arc d).toPath (φ t)) ∧
      (∀ O : D39BallFaceCycleOrbit B,
        H '' (B.plOrbitFace vert P hvert O).val =
          (B.plOrbitFace vert P' hvert O).val) := by
  obtain ⟨H, hor, hp, ha, _hi, _hc, hf⟩ :=
    exists_plane_homeomorph_of_du1 hDU1 B vert P P' hvert hconn O_ext hext
  refine ⟨H, hor, hp, ?_, hf⟩
  intro d
  have hstart : H (P.arc d).start = (P'.arc d).start := by
    rw [P.arc_start, P'.arc_start, hp]
  have hfinish : H (P.arc d).finish = (P'.arc d).finish := by
    rw [P.arc_finish, P'.arc_finish, hp]
  obtain ⟨φ, hm, _hanti, heq⟩ := exists_path_reparam_of_planeHomeomorph
    (P.arc d).toPath (P'.arc d).toPath
    ((P.arc d).toPath_injective (P.arc_length d) (P.arc_simple d))
    ((P'.arc d).toPath_injective (P'.arc_length d) (P'.arc_simple d))
    H false hstart hfinish (by simpa only [Polyline.range_toPath] using ha d)
  exact ⟨φ, hm rfl, heq⟩

include hDU1 in
/-- Helper toward Proposition 5.16: one common unbounded incidence lifts
a raw represented ball isomorphism to the exterior-preserving interface.
Conditional on exact DU1, the resulting plane homeomorphism transports
every vertex incidence, ordered dart path and restricted open orbit face.
This does not identify the retained ambient faces. -/
theorem exists_represented_plane_homeomorph_of_common_unbounded_incidence
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (y : PLCylinderBall.Representation N C)
    (r : ℕ) (hr : 0 < r)
    (I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr))
    (hcommon : ∃ d : (d39FacedBall M r hr).D,
      (¬ Bornology.IsBounded
        ((d39FacedBall M r hr).plDartFace
          (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D))
          (d39FacedBallPLDrawing M x.drawing r hr)
          (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr) d).val) ∧
      ¬ Bornology.IsBounded
        ((d39FacedBall N r hr).plDartFace
          (restrictedVertex y.drawing (d39BallDarts N r : Set N.core.D))
          (d39FacedBallPLDrawing N y.drawing r hr)
          (d39FacedBallPLDrawing_vertex_surjective N y.drawing r hr)
          (I.toEquiv d)).val) :
    ∃ H : ℂ ≃ₜ ℂ, OrientationPreserving H ∧
      (∀ d : (d39FacedBall M r hr).D,
        H (B.map.toPlaneMapWithMissing.pos (x.data.vertexEquiv (d39VertexClass M d.1))) =
          C.map.toPlaneMapWithMissing.pos
            (y.data.vertexEquiv (d39VertexClass N (I.toEquiv d).1))) ∧
      (∀ d : (d39FacedBall M r hr).D,
        ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
          ∀ t, H (d39DrawingDartArc B x.data.toD39DrawingRepresentationData d.1 t) =
            d39DrawingDartArc C y.data.toD39DrawingRepresentationData
              (I.toEquiv d).1 (φ t)) ∧
      (∀ O : D39BallFaceCycleOrbit (d39FacedBall M r hr),
        H '' ((d39FacedBall M r hr).plOrbitFace
          (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D))
          (d39FacedBallPLDrawing M x.drawing r hr)
          (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr) O).val =
          ((d39FacedBall N r hr).plOrbitFace
            (restrictedVertex y.drawing (d39BallDarts N r : Set N.core.D))
            (d39FacedBallPLDrawing N y.drawing r hr)
            (d39FacedBallPLDrawing_vertex_surjective N y.drawing r hr)
            (plBallFaceOrbitMap I O)).val) := by
  have hext :=
    (d39PLRepresentation_external_transport_iff_exists_unbounded_dart x y r hr I).mpr hcommon
  let J : D39BallIsoWithExternal
      (d39FacedBallPLWithExternal M x.drawing r hr)
      (d39FacedBallPLWithExternal N y.drawing r hr) :=
    ⟨I, (plBallFaceOrbitMap_eq_iff I _ _).mp hext⟩
  let := d39FacedBallPLDrawing_finite_vertices N y.drawing r hr
  obtain ⟨H, hor, hp, ha, hf⟩ := exists_plBallIso_homeomorph (@hDU1) J
    (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D))
    (restrictedVertex y.drawing (d39BallDarts N r : Set N.core.D))
    (d39FacedBallPLDrawing M x.drawing r hr)
    (d39FacedBallPLDrawing N y.drawing r hr)
    (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr)
    (d39FacedBallPLDrawing_vertex_surjective N y.drawing r hr)
    (d39FacedBall_connected N r hr)
    ⟨d39FacedBallPLWithExternal_unbounded M x.drawing r hr,
      d39FacedBallPLWithExternal_unbounded N y.drawing r hr⟩
  refine ⟨H, hor, ?_, ?_, hf⟩
  · intro d
    have hv := plBallVertexEquiv_apply J.toD39BallIso
      (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D))
      (restrictedVertex y.drawing (d39BallDarts N r : Set N.core.D))
      (d39FacedBallPLDrawing M x.drawing r hr)
      (d39FacedBallPLDrawing N y.drawing r hr)
      (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr)
      (d39FacedBallPLDrawing_vertex_surjective N y.drawing r hr) d
    have h := (hp (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D) d)).trans
      (congrArg (d39FacedBallPLDrawing N y.drawing r hr).pos hv)
    change H (x.drawing.pos (d39VertexClass M d.1)) =
      y.drawing.pos (d39VertexClass N (I.toEquiv d).1) at h
    rw [x.pos_eq, y.pos_eq] at h
    exact h
  · intro d
    obtain ⟨φ, hm, heq⟩ := ha d
    refine ⟨φ, hm, ?_⟩
    intro t
    have h := heq t
    change H ((x.drawing.arc d.1).toPath t) =
      (y.drawing.arc (I.toEquiv d).1).toPath (φ t) at h
    rw [x.arc_eq, y.arc_eq] at h
    exact h

end DU1



















































































































end DirectedDistances.PaperProofs.Section5.ReverseComparisonFromDU1

end
