/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516ExteriorMarkedComparison2
public import DirectedDistances.PlanarMap.PLDrawingWindingSides18






public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3.D39BallBridge

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section5
open Set unitInterval
open scoped ENNReal

local instance d39BallBridgePart1DecidableDarts (M : D39RootedMap) (r : ℕ) :
    DecidableEq {d : M.core.D // d ∈ d39BallDarts M r} := Classical.decEq _

private theorem increasing_endpoints (φ : I ≃ₜ I) (hm : StrictMono φ) :
    φ 0 = 0 ∧ φ 1 = 1 := by
  constructor
  · obtain ⟨t, ht⟩ := φ.surjective 0
    apply le_antisymm _ bot_le
    exact (hm.monotone bot_le).trans ht.le
  · obtain ⟨t, ht⟩ := φ.surjective 1
    apply le_antisymm le_top
    exact ht.symm.le.trans (hm.monotone le_top)

/-- Helper toward Definition 3.8 consumers: the geometric homeomorphism
transports the restricted left face of every dart, including nonoriginal
faces. Signed-side uniqueness identifies the transported face. -/
theorem restricted_dart_face_image
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (y : PLCylinderBall.Representation N C)
    (r : ℕ) (hr : 0 < r)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (d : (d39FacedBall M r hr).D) :
    e.h '' ((d39FacedBall M r hr).plDartFace
      (restrictedVertex x.drawing (d39BallDarts M r))
      (d39FacedBallPLDrawing M x.drawing r hr)
      (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr) d).val =
      ((d39FacedBall N r hr).plDartFace
        (restrictedVertex y.drawing (d39BallDarts N r))
        (d39FacedBallPLDrawing N y.drawing r hr)
        (d39FacedBallPLDrawing_vertex_surjective N y.drawing r hr)
        (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x.data y.data e d)).val := by
  let P := d39FacedBallPLDrawing M x.drawing r hr
  let Q := d39FacedBallPLDrawing N y.drawing r hr
  let E := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x.data y.data e
  let F := (d39FacedBall M r hr).plDartFace
    (restrictedVertex x.drawing (d39BallDarts M r)) P
    (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr) d
  have himage : e.h '' P.image = Q.image :=
    geomBallIso_restricted_drawing_image x y r hr e
  let F' : Q.Face := ⟨e.h '' F.val, by
    obtain ⟨z, hz, hF⟩ := F.property
    refine ⟨e.h z, ?_, ?_⟩
    · rw [← himage]
      rintro ⟨w, hw, heq⟩
      exact hz (e.h.injective heq ▸ hw)
    · rw [hF, ← himage]
      exact Homeomorph.image_connectedComponentIn_compl e.h P.image z⟩
  let φ := d39GeomBallIsoV2DartParam e
    ⟨(x.data.dartEquiv d.1).1,
      (d39DrawingRepresentationData3_ballDarts_iff x.data r d.1).mp d.2⟩
    (x.data.dartEquiv d.1).2
  obtain ⟨h0, h1⟩ := increasing_endpoints φ
    (d39GeomBallIsoV2DartParam_strictMono e _ _)
  have harc (t : I) : e.h ((P.arc d).toPath t) =
      (Q.arc (E d)).toPath (φ t) := by
    change e.h ((x.drawing.arc d.1).toPath t) =
      (y.drawing.arc (E d).1).toPath (φ t)
    rw [x.arc_eq, y.arc_eq]
    exact d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_arc_map
      x.data y.data e d t
  have hborder : P.dartBorders d F :=
    ((d39FacedBall M r hr).plDartFace_eq_iff _ P
      (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr) d F).mp rfl
  have hleft : ∀ s : {t : I // t ∈ openParams},
      LeftAtOn F'.val (Q.arc (E d)).toPath s := by
    apply (forall_leftAtOn_reparam_iff F'.val (Q.arc (E d)).toPath φ h0 h1).mp
    intro s
    have hs := (leftAtOn_map_iff F.val (P.arc d).toPath s
      e.h e.orientationPreserving).mp
      (P.dartBorders_toPath_leftAtOn
        (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr) d F hborder s)
    exact (leftAtOn_congr_fun F'.val _ _ s harc).mp hs
  have htarget := LeftSideHalfDisk.dartBorders_of_forall_leftAtOn_of_surjective Q
    (d39FacedBallPLDrawing_vertex_surjective N y.drawing r hr) (E d) F' hleft
  exact (congrArg Subtype.val
    (((d39FacedBall N r hr).plDartFace_eq_iff _ Q
      (d39FacedBallPLDrawing_vertex_surjective N y.drawing r hr) (E d) F').mpr
      htarget)).symm

/-- Helper toward Definition 3.8 consumers: a geometric ball isomorphism
preserves membership in the actual unbounded face orbit of the PL ball. -/
theorem external_iff
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (y : PLCylinderBall.Representation N C)
    (r : ℕ) (hr : 0 < r)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (d : (d39FacedBall M r hr).D) :
    d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x.data y.data e d ∈
        (d39FacedBallPLWithExternal N y.drawing r hr).externalOrbit.val ↔
      d ∈ (d39FacedBallPLWithExternal M x.drawing r hr).externalOrbit.val := by
  have hN := d39FacedBallPLWithExternal_mem_iff_not_isBounded_plDartFace
    N y.drawing r hr
    (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x.data y.data e d)
  have hM := d39FacedBallPLWithExternal_mem_iff_not_isBounded_plDartFace
    M x.drawing r hr d
  refine hN.trans ((not_congr ?_).trans hM.symm)
  rw [← restricted_dart_face_image x y r hr e d]
  exact isBounded_planeHomeomorph_image_iff e.h _

/-- Helper toward Definition 3.8 consumers: the induced dart equivalence
preserves rotation, reversal, tags, direction, root, original faces and the
geometrically selected exterior orbit, with no extra preservation premise. -/
@[expose] def markedIsoOfGeom
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (y : PLCylinderBall.Representation N C)
    (r : ℕ) (hr : 0 < r)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root) :
    D39BallIsoWithExternal (d39FacedBallPLWithExternal M x.drawing r hr)
      (d39FacedBallPLWithExternal N y.drawing r hr) where
  toD39BallIso := {
    toEquiv := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x.data y.data e
    rot_comm := d39DrawingRepresentationData3_geomBallIso_rotation_comm hr x.data y.data e
    edgeInv_comm := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_edgeInv
      x.data y.data e
    missing_iff := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_missing_iff
      x.data y.data e
    tail_iff := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_tail_iff
      x.data y.data e
    root_comm := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_root x.data y.data e
    original_iff := plRepresentation_geomBallIso_original_face_preservation x y e }
  external_iff := external_iff x y r hr e

/-- Helper toward Definition 3.8 consumers: matching faced balls with the
actual exterior marked gives the full geometric isomorphism on compatible
PL representations, through the proved finite PL extension theorem. -/
theorem geomIsoOfMarked
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (y : PLCylinderBall.Representation N C)
    (r : ℕ) (hr : 0 < r)
    (J : D39BallIsoWithExternal (d39FacedBallPLWithExternal M x.drawing r hr)
      (d39FacedBallPLWithExternal N y.drawing r hr)) :
    Nonempty (D39GeomBallIsoV2 r B.map B.root C.map C.root) := by
  apply exteriorMarkedComparison_reparam_geomBallIso x.data y.data
    x.drawing y.drawing x.pos_eq y.pos_eq
  · intro d
    exact ⟨Homeomorph.refl I, rfl, rfl, fun t => (x.arc_eq d t).symm⟩
  · intro d
    exact ⟨Homeomorph.refl I, rfl, rfl, fun t => (y.arc_eq d t).symm⟩
  · exact Quotient.sound ⟨J⟩

/-- Helper toward Definition 3.8 consumers: the full geometric comparison
is equivalent to equality of the exterior-marked faced-ball classes. -/
theorem geomIso_iff_markedClass_eq
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (y : PLCylinderBall.Representation N C)
    (r : ℕ) (hr : 0 < r) :
    Nonempty (D39GeomBallIsoV2 r B.map B.root C.map C.root) ↔
      representedExteriorMarkedBallClass x r hr =
        representedExteriorMarkedBallClass y r hr := by
  constructor
  · rintro ⟨e⟩
    exact Quotient.sound ⟨markedIsoOfGeom x y r hr e⟩
  · intro h
    obtain ⟨J⟩ := (representedExteriorMarkedBallClass_eq_iff x y r hr).mp h
    exact geomIsoOfMarked x y r hr J

/-- Helper toward Definition 3.8 consumers: the class pseudo-emetric on
represented maps is characterized by their exterior-marked faced balls. -/
theorem edist_le_iff_markedClass_eq
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (y : PLCylinderBall.Representation N C)
    (r : ℕ) (hr : 0 < r) :
    edist (PLCylinderBall.geometricClass B) (PLCylinderBall.geometricClass C) ≤
        (1 / 2 : ℝ≥0∞) ^ r ↔
      representedExteriorMarkedBallClass x r hr =
        representedExteriorMarkedBallClass y r hr :=
  (d39ClassDistance_le_pow_iff_nonempty hr
    (PLCylinderBall.domainMap B) (PLCylinderBall.domainMap C)).trans
    (geomIso_iff_markedClass_eq x y r hr)

end DirectedDistances.PaperProofs.Section3.D39BallBridge

end
