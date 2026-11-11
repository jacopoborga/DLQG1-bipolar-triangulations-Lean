/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516PLBallIso2
public import DirectedDistances.PlanarMap.D39PLDrawingUniqueness3

/-! # Retained face incidence and the external-orbit obstruction

Helpers toward Proposition 5.16 (`prop-disk-bs-conv`,
belong to the sole coordinator. No numbered result is asserted here. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open Set Topology

/-- Helper toward Proposition 5.16: a retained ambient PL face has a unique
restricted orbit. Membership in that orbit is exactly the ambient geometric
left-wedge bordering relation, for every retained dart. -/
theorem d39FacedBallPLDrawing_retained_face_unique_orbit
    (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r) (F : P.Face)
    (hret : ∀ v, P.pos v ∈ closure F.val → v ∈ d39BallVertices M r) :
    ∃! O : D39BallFaceCycleOrbit (d39FacedBall M r hr),
      ((d39FacedBall M r hr).plOrbitFace
        (restrictedVertex P (d39BallDarts M r : Set M.core.D))
        (d39FacedBallPLDrawing M P r hr)
        (d39FacedBallPLDrawing_vertex_surjective M P r hr) O).val = F.val ∧
      ∀ d : (d39FacedBall M r hr).D,
        d ∈ O.val ↔ P.dartBorders d.1 F := by
  obtain ⟨O, hO⟩ := d39FacedBallPLDrawing_retained_face_is_orbit M P r hr F hret
  have hinc : ∀ d : (d39FacedBall M r hr).D,
      d ∈ O.val ↔ P.dartBorders d.1 F := by
    intro d
    have h := (d39FacedBall M r hr).dartBorders_plOrbitFace_iff
      (restrictedVertex P (d39BallDarts M r : Set M.core.D))
      (d39FacedBallPLDrawing M P r hr)
      (d39FacedBallPLDrawing_vertex_surjective M P r hr)
      (d39FacedBall_connected M r hr) O d
    simpa only [PLDrawing.dartBorders, d39FacedBallPLDrawing_arc, hO] using h.symm
  refine ⟨O, ⟨hO, hinc⟩, ?_⟩
  intro Q hQ
  apply (d39FacedBall M r hr).plOrbitFace_injective
    (restrictedVertex P (d39BallDarts M r : Set M.core.D))
    (d39FacedBallPLDrawing M P r hr)
    (d39FacedBallPLDrawing_vertex_surjective M P r hr)
    (d39FacedBall_connected M r hr)
  exact Subtype.ext (hQ.1.trans hO.symm)

/-- Helper toward Proposition 5.16: for a retained ambient face and a dart
in a specified restricted orbit, exact face identification is equivalent to
the ambient geometric left-wedge condition. No winding-side converse is
assumed in this characterization. -/
theorem d39FacedBallPLDrawing_orbitFace_eq_iff_dartBorders
    (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r) (F : P.Face)
    (hret : ∀ v, P.pos v ∈ closure F.val → v ∈ d39BallVertices M r)
    (O : D39BallFaceCycleOrbit (d39FacedBall M r hr))
    (d : (d39FacedBall M r hr).D) (hdO : d ∈ O.val) :
    ((d39FacedBall M r hr).plOrbitFace
      (restrictedVertex P (d39BallDarts M r : Set M.core.D))
      (d39FacedBallPLDrawing M P r hr)
      (d39FacedBallPLDrawing_vertex_surjective M P r hr) O).val = F.val ↔
        P.dartBorders d.1 F := by
  obtain ⟨Q, ⟨hQ, hinc⟩, _⟩ :=
    d39FacedBallPLDrawing_retained_face_unique_orbit M P r hr F hret
  constructor
  · intro hO
    have hOQ : O = Q := by
      apply (d39FacedBall M r hr).plOrbitFace_injective
        (restrictedVertex P (d39BallDarts M r : Set M.core.D))
        (d39FacedBallPLDrawing M P r hr)
        (d39FacedBallPLDrawing_vertex_surjective M P r hr)
        (d39FacedBall_connected M r hr)
      exact Subtype.ext (hO.trans hQ.symm)
    exact (hinc d).mp (hOQ ▸ hdO)
  · intro hborder
    have hdQ := (hinc d).mpr hborder
    have hOQ : O = Q := by
      obtain ⟨a, ha⟩ := O.property
      obtain ⟨b, hb⟩ := Q.property
      have had : (d39FacedBall M r hr).map.faceSucc.SameCycle a d := by
        rw [ha] at hdO
        exact hdO
      have hbd : (d39FacedBall M r hr).map.faceSucc.SameCycle b d := by
        rw [hb] at hdQ
        exact hdQ
      apply Subtype.ext
      rw [ha, hb]
      ext e
      exact ⟨fun he => hbd.trans (had.symm.trans he),
        fun he => had.trans (hbd.symm.trans he)⟩
    exact hOQ.symm ▸ hQ

/-- Helper toward Proposition 5.16: regard a represented geometric face
as an ambient PL face using equality of the complete drawing images. Its
point-set is unchanged; this construction makes no dart-side identification. -/
@[expose] def d39PLRepresentationFace
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (hpos : ∀ v, P.pos v = B.map.toPlaneMapWithMissing.pos (x.vertexEquiv v))
    (harc : ∀ d t, (P.arc d).toPath t = d39DrawingDartArc B x d t)
    (F : B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) : P.Face :=
  ⟨F.val, by
    rw [d39PLRepresentation_image_eq x P hpos harc]
    exact F.property⟩

/-- Helper toward Proposition 5.16: every retained represented face is
the point-set of exactly one restricted orbit face. This strengthens the
predecessor's existential conclusion without identifying a specified dart. -/
theorem d39PLRepresentation_retained_face_unique_orbit
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (hpos : ∀ v, P.pos v = B.map.toPlaneMapWithMissing.pos (x.vertexEquiv v))
    (harc : ∀ d t, (P.arc d).toPath t = d39DrawingDartArc B x d t)
    (r : ℕ) (hr : 0 < r)
    (F : B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
    (hret : F ∈ d39GeomRetainedFaces B.map B.root r) :
    ∃! O : D39BallFaceCycleOrbit (d39FacedBall M r hr),
      ((d39FacedBall M r hr).plOrbitFace
        (restrictedVertex P (d39BallDarts M r : Set M.core.D))
        (d39FacedBallPLDrawing M P r hr)
        (d39FacedBallPLDrawing_vertex_surjective M P r hr) O).val = F.val := by
  obtain ⟨O, hO⟩ := d39PLRepresentation_retained_face_is_orbit x P hpos harc r hr F hret
  refine ⟨O, hO, ?_⟩
  intro Q hQ
  apply (d39FacedBall M r hr).plOrbitFace_injective
    (restrictedVertex P (d39BallDarts M r : Set M.core.D))
    (d39FacedBallPLDrawing M P r hr)
    (d39FacedBallPLDrawing_vertex_surjective M P r hr)
    (d39FacedBall_connected M r hr)
  exact Subtype.ext (hQ.trans hO.symm)

/-- Helper toward Proposition 5.16: the exact original-face identification
reduces to the geometric left-wedge condition for the represented dart.
The original tag supplies retention, but is not used to assert sidedness. -/
theorem d39PLRepresentation_original_orbitFace_iff_dartBorders
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (hpos : ∀ v, P.pos v = B.map.toPlaneMapWithMissing.pos (x.vertexEquiv v))
    (harc : ∀ d t, (P.arc d).toPath t =
      d39DrawingDartArc B x.toD39DrawingRepresentationData d t)
    (r : ℕ) (hr : 0 < r) (d : (d39FacedBall M r hr).D)
    (hd : d ∈ (d39FacedBall M r hr).original)
    (O : D39BallFaceCycleOrbit (d39FacedBall M r hr)) (hdO : d ∈ O.val) :
    ((d39FacedBall M r hr).plOrbitFace
      (restrictedVertex P (d39BallDarts M r : Set M.core.D))
      (d39FacedBallPLDrawing M P r hr)
      (d39FacedBallPLDrawing_vertex_surjective M P r hr) O).val =
        (x.faceOfDart d.1).val ↔
      P.dartBorders d.1
        (d39PLRepresentationFace x.toD39DrawingRepresentationData P hpos harc
          (x.faceOfDart d.1)) := by
  have hret : x.faceOfDart d.1 ∈ d39GeomRetainedFaces B.map B.root r :=
    (d39DrawingRepresentationData3_retained_iff_original x r d.1).mpr hd
  apply d39FacedBallPLDrawing_orbitFace_eq_iff_dartBorders M P r hr
    (d39PLRepresentationFace x.toD39DrawingRepresentationData P hpos harc
      (x.faceOfDart d.1)) _ O d hdO
  intro v hv
  apply (D39DrawingRepresentationData.ballVertices_iff
    x.toD39DrawingRepresentationData r v).mp
  apply hret
  rw [← hpos]
  change P.pos v ∈ closure (x.faceOfDart d.1).val at hv
  exact hv

/-- Helper toward Proposition 5.16: membership in an image face orbit is
preserved and reflected, without any external-marker premise. -/
theorem plBallFaceOrbitMap_mem_iff
    {A B : D39FiniteBall} (I : D39BallIso A B)
    (O : D39BallFaceCycleOrbit A) (d : A.D) :
    I.toEquiv d ∈ (plBallFaceOrbitMap I O).val ↔ d ∈ O.val := by
  change I.toEquiv d ∈ I.toEquiv '' O.val ↔ d ∈ O.val
  exact I.toEquiv.injective.mem_set_image

/-- Helper toward Proposition 5.16: exact transport of a chosen orbit is
equivalent to the dartwise condition required by `external_iff`. -/
theorem plBallFaceOrbitMap_eq_iff
    {A B : D39FiniteBall} (I : D39BallIso A B)
    (O : D39BallFaceCycleOrbit A) (Q : D39BallFaceCycleOrbit B) :
    plBallFaceOrbitMap I O = Q ↔
      ∀ d : A.D, I.toEquiv d ∈ Q.val ↔ d ∈ O.val := by
  constructor
  · rintro rfl d
    exact plBallFaceOrbitMap_mem_iff I O d
  · intro h
    apply Subtype.ext
    ext e
    obtain ⟨d, rfl⟩ := I.toEquiv.surjective e
    exact (plBallFaceOrbitMap_mem_iff I O d).trans (h d).symm

/-- Helper toward Proposition 5.16: the missing external-marker field is
exactly unboundedness of the transported selected orbit. This equivalence
isolates the geometric obligation; it does not assert that obligation. -/
theorem d39FacedBallPLDrawing_external_iff_unbounded
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
      ¬ Bornology.IsBounded
        ((d39FacedBall N r hr).plOrbitFace
          (restrictedVertex Q (d39BallDarts N r : Set N.core.D))
          (d39FacedBallPLDrawing N Q r hr)
          (d39FacedBallPLDrawing_vertex_surjective N Q r hr)
          (plBallFaceOrbitMap I
            (d39FacedBallPLWithExternal M P r hr).externalOrbit)).val := by
  exact (plBallFaceOrbitMap_eq_iff I
    (d39FacedBallPLWithExternal M P r hr).externalOrbit
    (d39FacedBallPLWithExternal N Q r hr).externalOrbit).symm.trans
      (d39FacedBallPLWithExternal_external_iff N Q r hr _)

/-- Helper toward Proposition 5.16: a plane homeomorphism preserves and
reflects boundedness of arbitrary point-sets. Compact closures supply the
properness argument, so no uniform-continuity premise is needed. -/
theorem isBounded_planeHomeomorph_image_iff (H : ℂ ≃ₜ ℂ) (S : Set ℂ) :
    Bornology.IsBounded (H '' S) ↔ Bornology.IsBounded S := by
  have hmap (G : ℂ ≃ₜ ℂ) (T : Set ℂ) (hT : Bornology.IsBounded T) :
      Bornology.IsBounded (G '' T) :=
    (hT.isCompact_closure.image G.continuous).isBounded.subset
      (Set.image_mono subset_closure)
  constructor
  · intro hS
    have h := hmap H.symm (H '' S) hS
    simpa only [Set.image_image, H.symm_apply_apply, Set.image_id'] using h
  · exact hmap H S




















































































































































































end DirectedDistances.PaperProofs.Section5

end
