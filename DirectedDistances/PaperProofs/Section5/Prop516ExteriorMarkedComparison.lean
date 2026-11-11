/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516RootExteriorEncoding
public import DirectedDistances.PaperProofs.Section5.Prop516OriginalIffDirect8
public import DirectedDistances.PaperProofs.Section5.Prop516ExteriorMarkedSample
public import DirectedDistances.PaperProofs.Section5.Prop516ExteriorMarkedCanonical

/-! The signed PL uniqueness theorem identifies the original restricted orbit
with its retained ambient face. Exterior-marked equality consequently
transports those ambient faces. The full general-carrier ball correspondence
and its source-family applications remain separate obligations. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.KMSW MeasureTheory

/-- Helper toward Proposition 5.16: endpoint-preserving dart
reparameterizations preserve the complete geometric drawing image. -/
theorem exteriorMarkedComparison_reparam_image_eq
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (hpos : ∀ v, P.pos v = B.map.toPlaneMapWithMissing.pos (x.vertexEquiv v))
    (harc : ∀ d, ∃ φ : unitInterval ≃ₜ unitInterval,
      ∀ t, d39DrawingDartArc B x d t = (P.arc d).toPath (φ t)) :
    P.image = B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.image := by
  have ha (d : M.core.D) :
      (P.arc d).image = Set.range (B.map.toPlaneMapWithMissing.arc (x.dartEquiv d).1) := by
    obtain ⟨φ, hφ⟩ := harc d
    have heq : Set.range (P.arc d).toPath = Set.range (d39DrawingDartArc B x d) := by
      ext z
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨φ.symm t, by rw [hφ, φ.apply_symm_apply]⟩
      · rintro ⟨t, rfl⟩
        exact ⟨φ t, (hφ t).symm⟩
    rw [← Polyline.range_toPath, heq]
    unfold d39DrawingDartArc
    split
    · rfl
    · exact Path.symm_range _
  ext z
  constructor
  · rintro (⟨v, rfl⟩ | ⟨d, hd⟩)
    · exact Or.inl ⟨x.vertexEquiv v, (hpos v).symm⟩
    · exact Or.inr (Set.mem_iUnion.mpr ⟨(x.dartEquiv d).1, ha d ▸ hd⟩)
  · rintro (⟨v, rfl⟩ | hz)
    · obtain ⟨w, rfl⟩ := x.vertexEquiv.surjective v
      exact Or.inl ⟨w, hpos w⟩
    · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hz
      let d := x.dartEquiv.symm (e, true)
      right
      refine ⟨d, ?_⟩
      rw [ha d, x.dartEquiv.apply_symm_apply]
      exact he

/-- Helper toward Proposition 5.16: represented left-side incidence passes
to the PL dart through endpoint-preserving reparameterization. -/
theorem exteriorMarkedComparison_reparam_face_leftAtOn
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData M B)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (d : M.core.D) (φ : unitInterval ≃ₜ unitInterval)
    (h0 : φ 0 = 0) (h1 : φ 1 = 1)
    (harc : ∀ t, d39DrawingDartArc B x d t = (P.arc d).toPath (φ t)) :
    ∀ s : {t : unitInterval // t ∈ openParams},
      LeftAtOn (x.faceOfDart d).val (P.arc d).toPath s := by
  apply (forall_leftAtOn_reparam_iff _ _ φ h0 h1).mp
  intro s
  have hside := x.face_left_of_dart d
  cases hb : (x.dartEquiv d).2
  · rw [hb] at hside
    have hs : ∀ t : {t : unitInterval // t ∈ openParams},
        RightAtOn (x.faceOfDart d).val
          (B.map.toPlaneMapWithMissing.arc (x.dartEquiv d).1) t := hside
    have hl := (forall_leftAtOn_symm_iff (x.faceOfDart d).val
      (B.map.toPlaneMapWithMissing.arc (x.dartEquiv d).1)).mpr hs
    apply (leftAtOn_congr_fun _ _ _ s (fun t => ?_)).mpr (hl s)
    change (P.arc d).toPath (φ t) = _
    rw [← harc, d39DrawingDartArc, hb]
    rfl
  · rw [hb] at hside
    apply (leftAtOn_congr_fun _ _ _ s (fun t => ?_)).mpr (hside s)
    change (P.arc d).toPath (φ t) = _
    rw [← harc, d39DrawingDartArc, hb]
    rfl

/-- Helper toward Proposition 5.16: original-face identification also holds
for reparameterized drawings, without requiring literal equality of the path
schedules used by the source geometric carrier and the PL realization. -/
theorem exteriorMarkedComparison_reparam_original_orbitFace
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (hpos : ∀ v, P.pos v = B.map.toPlaneMapWithMissing.pos (x.vertexEquiv v))
    (harc : ∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ t, d39DrawingDartArc B x.toD39DrawingRepresentationData d t =
        (P.arc d).toPath (φ t))
    (r : ℕ) (hr : 0 < r) (d : (d39FacedBall M r hr).D)
    (hd : d ∈ (d39FacedBall M r hr).original)
    (O : D39BallFaceCycleOrbit (d39FacedBall M r hr)) (hdO : d ∈ O.val) :
    ((d39FacedBall M r hr).plOrbitFace
      (restrictedVertex P (d39BallDarts M r : Set M.core.D))
      (d39FacedBallPLDrawing M P r hr)
      (d39FacedBallPLDrawing_vertex_surjective M P r hr) O).val =
        (x.faceOfDart d.1).val := by
  have himage := exteriorMarkedComparison_reparam_image_eq
    x.toD39DrawingRepresentationData P hpos (fun a => by
      obtain ⟨φ, _, _, hφ⟩ := harc a
      exact ⟨φ, hφ⟩)
  let F : P.Face := ⟨(x.faceOfDart d.1).val, by
    rw [himage]
    exact (x.faceOfDart d.1).property⟩
  have hret := (d39DrawingRepresentationData3_retained_iff_original x r d.1).mpr hd
  apply (d39FacedBallPLDrawing_orbitFace_eq_iff_dartBorders M P r hr F
    (fun v hv => (D39DrawingRepresentationData.ballVertices_iff
      x.toD39DrawingRepresentationData r v).mp (hret _ (by
        rw [← hpos]
        exact hv))) O d hdO).mpr
  obtain ⟨φ, h0, h1, hφ⟩ := harc d.1
  exact LeftSideHalfDisk.dartBorders_of_forall_leftAtOn_of_surjective
    P (fun v => Quotient.exists_rep v) d.1 F
    (exteriorMarkedComparison_reparam_face_leftAtOn
      x.toD39DrawingRepresentationData P d.1 φ h0 h1 hφ)



theorem exteriorMarkedComparison_original_orbitFace
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (r : ℕ) (hr : 0 < r)
    (d : (d39FacedBall M r hr).D)
    (hd : d ∈ (d39FacedBall M r hr).original)
    (O : D39BallFaceCycleOrbit (d39FacedBall M r hr)) (hdO : d ∈ O.val) :
    ((d39FacedBall M r hr).plOrbitFace
      (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D))
      (d39FacedBallPLDrawing M x.drawing r hr)
      (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr) O).val =
        (x.data.faceOfDart d.1).val := by
  apply (d39PLRepresentation_original_orbitFace_iff_dartBorders
    x.data x.drawing x.pos_eq x.arc_eq r hr d hd O hdO).mpr
  apply LeftSideHalfDisk.dartBorders_of_forall_leftAtOn_of_surjective
    x.drawing (fun v => Quotient.exists_rep v)
  exact d39PLRepresentation_face_leftAtOn x.data.toD39DrawingRepresentationData
    x.drawing x.arc_eq d.1

/-- Helper toward Proposition 5.16: marked equality supplies one oriented
plane homeomorphism transporting every original dart's ambient face, together
with the vertex and ordered-path comparisons from finite drawing uniqueness. -/
theorem exteriorMarkedComparison_original_face_transport
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (y : PLCylinderBall.Representation N C)
    (r : ℕ) (hr : 0 < r)
    (hxy : representedExteriorMarkedBallClass x r hr =
      representedExteriorMarkedBallClass y r hr) :
    ∃ (I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr))
      (H : ℂ ≃ₜ ℂ), OrientationPreserving H ∧
      (∀ d : (d39FacedBall M r hr).D,
        H (B.map.toPlaneMapWithMissing.pos (x.data.vertexEquiv (d39VertexClass M d.1))) =
          C.map.toPlaneMapWithMissing.pos
            (y.data.vertexEquiv (d39VertexClass N (I.toEquiv d).1))) ∧
      (∀ d : (d39FacedBall M r hr).D,
        ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
          ∀ t, H (d39DrawingDartArc B x.data.toD39DrawingRepresentationData d.1 t) =
            d39DrawingDartArc C y.data.toD39DrawingRepresentationData
              (I.toEquiv d).1 (φ t)) ∧
      ∀ d : (d39FacedBall M r hr).D,
        d ∈ (d39FacedBall M r hr).original →
          H '' (x.data.faceOfDart d.1).val =
            (y.data.faceOfDart (I.toEquiv d).1).val := by
  obtain ⟨I, H, hH, hpos, harc, hfaces⟩ :=
    exists_represented_plane_homeomorph_of_exteriorMarkedBallClass_eq x y r hr hxy
  refine ⟨I, H, hH, hpos, harc, ?_⟩
  intro d hd
  let O := plBallDartOrbit (d39FacedBall M r hr) d
  have hdO : d ∈ O.val := Equiv.Perm.SameCycle.rfl
  have hIdO : I.toEquiv d ∈ (plBallFaceOrbitMap I O).val :=
    (plBallFaceOrbitMap_mem_iff I O d).mpr hdO
  have hId : I.toEquiv d ∈ (d39FacedBall N r hr).original :=
    (I.original_iff d).mpr hd
  rw [← exteriorMarkedComparison_original_orbitFace x r hr d hd O hdO,
    ← exteriorMarkedComparison_original_orbitFace y r hr (I.toEquiv d) hId
      (plBallFaceOrbitMap I O) hIdO]
  exact hfaces O

/-- Helper toward Proposition 5.16: equality of the actual exterior-marked
classes yields an oriented plane comparison on arbitrary PL realizations.
This statement uses their polylines directly and allows reparameterization. -/
theorem exteriorMarkedComparison_planeHomeomorph
    (M N : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (Q : PLDrawing N.core.D (RootedLocallyFiniteVertex N.core.D N.core.rot)
      N.core.edgeInv N.core.rot (d39VertexClass N))
    (r : ℕ) (hr : 0 < r)
    (hxy : Quotient.mk exteriorMarkedBallSetoid (d39FacedBallPLWithExternal M P r hr) =
      Quotient.mk exteriorMarkedBallSetoid (d39FacedBallPLWithExternal N Q r hr)) :
    ∃ (I : D39BallIsoWithExternal
        (d39FacedBallPLWithExternal M P r hr) (d39FacedBallPLWithExternal N Q r hr))
      (H : ℂ ≃ₜ ℂ), OrientationPreserving H ∧
      (∀ d : (d39FacedBall M r hr).D,
        H (P.pos (d39VertexClass M d.1)) =
          Q.pos (d39VertexClass N (I.toD39BallIso.toEquiv d).1)) ∧
      (∀ d : (d39FacedBall M r hr).D,
        ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
          ∀ t, H ((P.arc d.1).toPath t) =
            (Q.arc (I.toD39BallIso.toEquiv d).1).toPath (φ t)) ∧
      ∀ O : D39BallFaceCycleOrbit (d39FacedBall M r hr),
        H '' ((d39FacedBall M r hr).plOrbitFace
          (restrictedVertex P (d39BallDarts M r : Set M.core.D))
          (d39FacedBallPLDrawing M P r hr)
          (d39FacedBallPLDrawing_vertex_surjective M P r hr) O).val =
          ((d39FacedBall N r hr).plOrbitFace
            (restrictedVertex Q (d39BallDarts N r : Set N.core.D))
            (d39FacedBallPLDrawing N Q r hr)
            (d39FacedBallPLDrawing_vertex_surjective N Q r hr)
            (plBallFaceOrbitMap I.toD39BallIso O)).val := by
  obtain ⟨I⟩ : Nonempty (D39BallIsoWithExternal
      (d39FacedBallPLWithExternal M P r hr) (d39FacedBallPLWithExternal N Q r hr)) :=
    Quotient.exact hxy
  let := d39FacedBallPLDrawing_finite_vertices N Q r hr
  obtain ⟨H, hH, hpos, harc, hfaces⟩ := exists_plBallIso_homeomorph
    ReverseComparison2.drawing_uniqueness_du1 I
    (restrictedVertex P (d39BallDarts M r : Set M.core.D))
    (restrictedVertex Q (d39BallDarts N r : Set N.core.D))
    (d39FacedBallPLDrawing M P r hr) (d39FacedBallPLDrawing N Q r hr)
    (d39FacedBallPLDrawing_vertex_surjective M P r hr)
    (d39FacedBallPLDrawing_vertex_surjective N Q r hr)
    (d39FacedBall_connected N r hr)
    ⟨d39FacedBallPLWithExternal_unbounded M P r hr,
      d39FacedBallPLWithExternal_unbounded N Q r hr⟩
  refine ⟨I, H, hH, ?_, harc, hfaces⟩
  intro d
  have hv := hpos (restrictedVertex P (d39BallDarts M r : Set M.core.D) d)
  rw [plBallVertexEquiv_apply I.toD39BallIso
    (restrictedVertex P (d39BallDarts M r : Set M.core.D))
    (restrictedVertex Q (d39BallDarts N r : Set N.core.D))
    (d39FacedBallPLDrawing M P r hr) (d39FacedBallPLDrawing N Q r hr)
    (d39FacedBallPLDrawing_vertex_surjective M P r hr)
    (d39FacedBallPLDrawing_vertex_surjective N Q r hr) d] at hv
  exact hv

/-- Helper toward Proposition 5.16: the marked plane comparison transports
original ambient faces also on the reparameterized representation carrier. -/
theorem exteriorMarkedComparison_reparam_original_face_transport
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B) (y : D39DrawingRepresentationData3 N C)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (Q : PLDrawing N.core.D (RootedLocallyFiniteVertex N.core.D N.core.rot)
      N.core.edgeInv N.core.rot (d39VertexClass N))
    (hPpos : ∀ v, P.pos v = B.map.toPlaneMapWithMissing.pos (x.vertexEquiv v))
    (hQpos : ∀ v, Q.pos v = C.map.toPlaneMapWithMissing.pos (y.vertexEquiv v))
    (hParc : ∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ t, d39DrawingDartArc B x.toD39DrawingRepresentationData d t =
        (P.arc d).toPath (φ t))
    (hQarc : ∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ t, d39DrawingDartArc C y.toD39DrawingRepresentationData d t =
        (Q.arc d).toPath (φ t))
    (r : ℕ) (hr : 0 < r)
    (hxy : Quotient.mk exteriorMarkedBallSetoid (d39FacedBallPLWithExternal M P r hr) =
      Quotient.mk exteriorMarkedBallSetoid (d39FacedBallPLWithExternal N Q r hr)) :
    ∃ (I : D39BallIsoWithExternal
        (d39FacedBallPLWithExternal M P r hr) (d39FacedBallPLWithExternal N Q r hr))
      (H : ℂ ≃ₜ ℂ), OrientationPreserving H ∧
      (∀ d : (d39FacedBall M r hr).D,
        H (P.pos (d39VertexClass M d.1)) =
          Q.pos (d39VertexClass N (I.toD39BallIso.toEquiv d).1)) ∧
      (∀ d : (d39FacedBall M r hr).D,
        ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
          ∀ t, H ((P.arc d.1).toPath t) =
            (Q.arc (I.toD39BallIso.toEquiv d).1).toPath (φ t)) ∧
      ∀ d : (d39FacedBall M r hr).D,
        d ∈ (d39FacedBall M r hr).original →
          H '' (x.faceOfDart d.1).val =
            (y.faceOfDart (I.toD39BallIso.toEquiv d).1).val := by
  obtain ⟨I, H, hH, hpos, harc, hfaces⟩ :=
    exteriorMarkedComparison_planeHomeomorph M N P Q r hr hxy
  refine ⟨I, H, hH, hpos, harc, ?_⟩
  intro d hd
  let O := plBallDartOrbit (d39FacedBall M r hr) d
  have hdO : d ∈ O.val := Equiv.Perm.SameCycle.rfl
  have hIdO : I.toD39BallIso.toEquiv d ∈
      (plBallFaceOrbitMap I.toD39BallIso O).val :=
    (plBallFaceOrbitMap_mem_iff I.toD39BallIso O d).mpr hdO
  have hId := (I.toD39BallIso.original_iff d).mpr hd
  rw [← exteriorMarkedComparison_reparam_original_orbitFace
      x P hPpos hParc r hr d hd O hdO,
    ← exteriorMarkedComparison_reparam_original_orbitFace
      y Q hQpos hQarc r hr (I.toD39BallIso.toEquiv d) hId
        (plBallFaceOrbitMap I.toD39BallIso O) hIdO]
  exact hfaces O

private theorem retainedFace_exists_original_dart
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B) (r : ℕ) (hr : 0 < r)
    (F : {F // F ∈ d39GeomRetainedFaces B.map B.root r}) :
    ∃ d : (d39FacedBall M r hr).D,
      d ∈ (d39FacedBall M r hr).original ∧ x.faceOfDart d.1 = F.1 := by
  obtain ⟨a, ha⟩ := x.face_surjective F.1
  have hret : x.faceOfDart a ∈ d39GeomRetainedFaces B.map B.root r := ha ▸ F.2
  have ho := (d39DrawingRepresentationData3_retained_iff_original x r a).mp hret
  exact ⟨⟨a, ho a Equiv.Perm.SameCycle.rfl⟩, ho, ha⟩

/-- Helper toward Proposition 5.16: marked comparison supplies a bijection
of all retained ambient faces on the reparameterized carrier, with their
actual plane images, jointly with the vertex and ordered-path comparison. -/
theorem exteriorMarkedComparison_reparam_retainedFaceEquiv
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B) (y : D39DrawingRepresentationData3 N C)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (Q : PLDrawing N.core.D (RootedLocallyFiniteVertex N.core.D N.core.rot)
      N.core.edgeInv N.core.rot (d39VertexClass N))
    (hPpos : ∀ v, P.pos v = B.map.toPlaneMapWithMissing.pos (x.vertexEquiv v))
    (hQpos : ∀ v, Q.pos v = C.map.toPlaneMapWithMissing.pos (y.vertexEquiv v))
    (hParc : ∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ t, d39DrawingDartArc B x.toD39DrawingRepresentationData d t =
        (P.arc d).toPath (φ t))
    (hQarc : ∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ t, d39DrawingDartArc C y.toD39DrawingRepresentationData d t =
        (Q.arc d).toPath (φ t))
    (r : ℕ) (hr : 0 < r)
    (hxy : Quotient.mk exteriorMarkedBallSetoid (d39FacedBallPLWithExternal M P r hr) =
      Quotient.mk exteriorMarkedBallSetoid (d39FacedBallPLWithExternal N Q r hr)) :
    ∃ (I : D39BallIsoWithExternal
        (d39FacedBallPLWithExternal M P r hr) (d39FacedBallPLWithExternal N Q r hr))
      (H : ℂ ≃ₜ ℂ)
      (E : {F // F ∈ d39GeomRetainedFaces B.map B.root r} ≃
        {F // F ∈ d39GeomRetainedFaces C.map C.root r}),
      OrientationPreserving H ∧
      (∀ d : (d39FacedBall M r hr).D,
        H (P.pos (d39VertexClass M d.1)) =
          Q.pos (d39VertexClass N (I.toD39BallIso.toEquiv d).1)) ∧
      (∀ d : (d39FacedBall M r hr).D,
        ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
          ∀ t, H ((P.arc d.1).toPath t) =
            (Q.arc (I.toD39BallIso.toEquiv d).1).toPath (φ t)) ∧
      ∀ F, H '' F.1.val = (E F).1.val := by
  obtain ⟨I, H, hH, hp, ha, hf⟩ :=
    exteriorMarkedComparison_reparam_original_face_transport
      x y P Q hPpos hQpos hParc hQarc r hr hxy
  have hex (F : {F // F ∈ d39GeomRetainedFaces B.map B.root r}) :
      ∃ G : {F // F ∈ d39GeomRetainedFaces C.map C.root r}, H '' F.1.val = G.1.val := by
    obtain ⟨d, hd, hFd⟩ := retainedFace_exists_original_dart x r hr F
    have hId := (I.toD39BallIso.original_iff d).mpr hd
    have hret := (d39DrawingRepresentationData3_retained_iff_original
      y r (I.toD39BallIso.toEquiv d).1).mpr hId
    refine ⟨⟨y.faceOfDart (I.toD39BallIso.toEquiv d).1, hret⟩, ?_⟩
    rw [← hFd]
    exact hf d hd
  have honto (G : {F // F ∈ d39GeomRetainedFaces C.map C.root r}) :
      ∃ F : {F // F ∈ d39GeomRetainedFaces B.map B.root r}, H '' F.1.val = G.1.val := by
    obtain ⟨e, he, hGe⟩ := retainedFace_exists_original_dart y r hr G
    let d := I.toD39BallIso.toEquiv.symm e
    have hId : I.toD39BallIso.toEquiv d = e := I.toD39BallIso.toEquiv.apply_symm_apply e
    have hd : d ∈ (d39FacedBall M r hr).original :=
      (I.toD39BallIso.original_iff d).mp (hId.symm ▸ he)
    have hret := (d39DrawingRepresentationData3_retained_iff_original x r d.1).mpr hd
    refine ⟨⟨x.faceOfDart d.1, hret⟩, ?_⟩
    have ht := hf d hd
    rw [hId, hGe] at ht
    exact ht
  let f := fun F => Classical.choose (hex F)
  have hval (F) : H '' F.1.val = (f F).1.val := Classical.choose_spec (hex F)
  have hinj : Function.Injective f := by
    intro F G hfg
    apply Subtype.ext
    apply Subtype.ext
    apply Set.image_injective.mpr H.injective
    exact (hval F).trans ((congrArg (fun J => J.1.val) hfg).trans (hval G).symm)
  have hsurj : Function.Surjective f := by
    intro G
    obtain ⟨F, hF⟩ := honto G
    exact ⟨F, Subtype.ext (Subtype.ext ((hval F).symm.trans hF))⟩
  exact ⟨I, H, Equiv.ofBijective f ⟨hinj, hsurj⟩, hH, hp, ha, hval⟩

/-- Helper toward Proposition 5.16: original-face identification specializes
to the actual finite sample domain and its same reindexed stage drawing. -/
theorem exteriorMarkedComparison_sample_original_orbitFace
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell p) n).IsOuter d)
    (r : ℕ) (hr : 0 < r)
    (d : (d39FacedBall (diskRootedD39MapOfSample n ell hell p) r hr).D)
    (hd : d ∈ (d39FacedBall (diskRootedD39MapOfSample n ell hell p) r hr).original)
    (O : D39BallFaceCycleOrbit (d39FacedBall (diskRootedD39MapOfSample n ell hell p) r hr))
    (hdO : d ∈ O.val) :
    let M := diskRootedD39MapOfSample n ell hell p
    let Q := diskSampleRootedStagePLDrawing ell n hell p P
    ((d39FacedBall M r hr).plOrbitFace
      (restrictedVertex Q (d39BallDarts M r : Set M.core.D))
      (d39FacedBallPLDrawing M Q r hr)
      (d39FacedBallPLDrawing_vertex_surjective M Q r hr) O).val =
        ((diskSampleExteriorData3 ell n hell p P U hU hborder).faceOfDart d.1).val := by
  apply exteriorMarkedComparison_reparam_original_orbitFace
    (diskSampleExteriorData3 ell n hell p P U hU hborder)
    (diskSampleRootedStagePLDrawing ell n hell p P) ?_ ?_ r hr d hd O hdO
  · intro v
    rfl
  · intro a
    exact diskSampleExteriorBase_dartArc_reparam ell n hell p P U hU hborder a

/-- Helper toward Proposition 5.16: on the actual finite-sample and
canonical UIBHBOT drawings, equality of reversed-root lifts gives an
isomorphism preserving the actual exterior. The certificates concern these
same drawings and are supplied by the source exterior producers. -/
theorem exteriorMarkedComparison_sample_canonical_iso
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell p) n).IsOuter d)
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0)
    (hrootAbsent : ¬ wholePlaneEdgePresent W (uibhbotRootEdge W))
    (r : ℕ) (hr : 0 < r)
    (hxy : Prop516RootExteriorEncoding.rootLift
        (d39BallClass (diskRootedD39MapOfSample n ell hell p) r hr) =
      Prop516RootExteriorEncoding.rootLift
        (d39BallClass
          (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
          r hr)) :
    Nonempty (D39BallIsoWithExternal
      (d39FacedBallPLWithExternal (diskRootedD39MapOfSample n ell hell p)
        (diskSampleRootedStagePLDrawing ell n hell p P) r hr)
      (d39FacedBallPLWithExternal
        (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
        (prop59_canonicalAssembly_reindexedDrawing W D hhit C₀) r hr)) := by
  have heq := (diskSampleExteriorMarkedBallClass_eq_rootLift
    ell n hell p P U hU hborder r hr).trans (hxy.trans
      (prop516_canonicalExteriorMarkedBallClass_eq_rootLift
        W D hhit C₀ hrootAbsent r hr).symm)
  exact Quotient.exact heq

/-- Helper toward Proposition 5.16: a single conull event supplies the
finite-sample/canonical exterior-preserving comparison at every sample size
and radius. Finite exterior realizations are produced, not assumed. -/
theorem exteriorMarkedComparison_sample_canonical_iso_ae :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (D : UIBHBOTD39CanonicalDomainWitness W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C₀ : UIBHBOTCertifiedRootCapture W 0)
        (ell n : ℕ) (hell : 0 < ell)
        (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} × Fin ell)
        (r : ℕ) (hr : 0 < r),
        Prop516RootExteriorEncoding.rootLift
            (d39BallClass (diskRootedD39MapOfSample n ell hell p) r hr) =
          Prop516RootExteriorEncoding.rootLift
            (d39BallClass
              (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
              r hr) →
        ∃ P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n,
          Nonempty (D39BallIsoWithExternal
            (d39FacedBallPLWithExternal (diskRootedD39MapOfSample n ell hell p)
              (diskSampleRootedStagePLDrawing ell n hell p P) r hr)
            (d39FacedBallPLWithExternal
              (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
              (prop59_canonicalAssembly_reindexedDrawing W D hhit C₀) r hr)) := by
  filter_upwards [prop59_uibhbotRootEdge_absent_ae_for_mirror_compat] with W hW
  intro D hhit C₀ ell n hell p r hr hxy
  obtain ⟨P, U, hU, hborder, _⟩ := diskSample_exists_exteriorData3 ell n hell p
  exact ⟨P, exteriorMarkedComparison_sample_canonical_iso
    ell n hell p P U hU hborder W D hhit C₀ hW r hr hxy⟩



















































end DirectedDistances.PaperProofs.Section5

end
