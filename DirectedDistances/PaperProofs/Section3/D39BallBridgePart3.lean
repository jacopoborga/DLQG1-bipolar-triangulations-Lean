/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.D39BallBridgePart1







public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3.D39BallBridge

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section5
open Set unitInterval

local instance d39BallBridgePart3DecidableDarts (M : D39RootedMap) (r : ℕ) :
    DecidableEq {d : M.core.D // d ∈ d39BallDarts M r} := Classical.decEq _



theorem reparam_signed_face_unique
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (ha : ∀ d, ∃ φ : I ≃ₜ I, φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ t, d39DrawingDartArc B x.toD39DrawingRepresentationData d t =
        (P.arc d).toPath (φ t))
    (d : M.core.D)
    (F : B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
    (hF : if (x.dartEquiv d).2 then
      B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf F (x.dartEquiv d).1
    else B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf F (x.dartEquiv d).1) :
    F = x.faceOfDart d := by
  have himage := exteriorMarkedComparison_reparam_image_eq
    x.toD39DrawingRepresentationData P
    (ExteriorMarkedComparison2.pos_eq_of_reparam x.toD39DrawingRepresentationData P ha)
    (fun a => by obtain ⟨φ, _, _, hφ⟩ := ha a; exact ⟨φ, hφ⟩)
  let F' : P.Face := ⟨F.val, by rw [himage]; exact F.property⟩
  let G' : P.Face := ⟨(x.faceOfDart d).val, by
    rw [himage]; exact (x.faceOfDart d).property⟩
  obtain ⟨φ, h0, h1, hφ⟩ := ha d
  have hleft : ∀ s : {t : I // t ∈ openParams},
      LeftAtOn F'.val (P.arc d).toPath s := by
    apply (forall_leftAtOn_reparam_iff F'.val (P.arc d).toPath φ h0 h1).mp
    intro s
    cases hb : (x.dartEquiv d).2
    · rw [hb] at hF
      have hs : ∀ t : {t : I // t ∈ openParams},
          RightAtOn F.val (B.map.toPlaneMapWithMissing.arc (x.dartEquiv d).1) t := hF
      have ht := (forall_leftAtOn_symm_iff F.val
        (B.map.toPlaneMapWithMissing.arc (x.dartEquiv d).1)).mpr hs
      apply (leftAtOn_congr_fun _ _ _ s (fun t => ?_)).mpr (ht s)
      change (P.arc d).toPath (φ t) = _
      rw [← hφ, d39DrawingDartArc, hb]
      rfl
    · rw [hb] at hF
      apply (leftAtOn_congr_fun _ _ _ s (fun t => ?_)).mpr (hF s)
      change (P.arc d).toPath (φ t) = _
      rw [← hφ, d39DrawingDartArc, hb]
      rfl
  have heq : F' = G' := LeftSideHalfDisk.face_eq_of_forall_leftAtOn_of_surjective
    P (fun v => Quotient.exists_rep v) d F' G' hleft
    (exteriorMarkedComparison_reparam_face_leftAtOn
      x.toD39DrawingRepresentationData P d φ h0 h1 hφ)
  exact Subtype.ext (congrArg (fun H : P.Face => H.val) heq)

/-- Helper toward Definition 3.8 consumers: retained geometric faces agree
with dart-face assignment on a reparameterized PL target. -/
theorem reparam_retained_face_assignment
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B) (y : D39DrawingRepresentationData3 N C)
    (Q : PLDrawing N.core.D (RootedLocallyFiniteVertex N.core.D N.core.rot)
      N.core.edgeInv N.core.rot (d39VertexClass N))
    (hb : ∀ d, ∃ φ : I ≃ₜ I, φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ t, d39DrawingDartArc C y.toD39DrawingRepresentationData d t =
        (Q.arc d).toPath (φ t))
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (d : {d : M.core.D // d ∈ d39BallDarts M r})
    (hret : x.faceOfDart d.1 ∈ d39GeomRetainedFaces B.map B.root r) :
    (e.faceEquiv ⟨x.faceOfDart d.1, hret⟩).1 =
      y.faceOfDart (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d).1 := by
  have hs := d39DrawingRepresentationData3_geomBallIso_faceEquiv_imageSide x y e d hret
  apply reparam_signed_face_unique y Q hb _ _
  rw [hs.2.1]
  exact hs.1

section Pair

variable {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
  (x : D39DrawingRepresentationData3 M B) (y : D39DrawingRepresentationData3 N C)
  (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
    M.core.edgeInv M.core.rot (d39VertexClass M))
  (Q : PLDrawing N.core.D (RootedLocallyFiniteVertex N.core.D N.core.rot)
    N.core.edgeInv N.core.rot (d39VertexClass N))
  (ha : ∀ d, ∃ φ : I ≃ₜ I, φ 0 = 0 ∧ φ 1 = 1 ∧
    ∀ t, d39DrawingDartArc B x.toD39DrawingRepresentationData d t =
      (P.arc d).toPath (φ t))
  (hb : ∀ d, ∃ φ : I ≃ₜ I, φ 0 = 0 ∧ φ 1 = 1 ∧
    ∀ t, d39DrawingDartArc C y.toD39DrawingRepresentationData d t =
      (Q.arc d).toPath (φ t))

include ha hb in
/-- Helper toward Definition 3.8 consumers: geometric isomorphisms preserve
and reflect the original-face marker on reparameterized PL representations. -/
theorem reparam_original_iff {r : ℕ}
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (d : {d : M.core.D // d ∈ d39BallDarts M r}) :
    d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d ∈
        (d39FacedBall N r e.radius_pos).original ↔
      d ∈ (d39FacedBall M r e.radius_pos).original := by
  let E := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e
  constructor
  · intro hd
    have hret := (d39DrawingRepresentationData3_original_iff_face_retained
      y r e.radius_pos (E d)).mp hd
    have heq := reparam_retained_face_assignment y x P ha e.symm (E d) hret
    have hback : d39DrawingRepresentationData3_geomBallIso_ballDartEquiv
        y x e.symm (E d) = d := by
      rw [geomBallIso_ballDartEquiv_symm_apply]
      exact E.symm_apply_apply d
    rw [hback] at heq
    apply (d39DrawingRepresentationData3_original_iff_face_retained x r e.radius_pos d).mpr
    rw [← heq]
    exact (e.symm.faceEquiv ⟨y.faceOfDart (E d).1, hret⟩).property
  · intro hd
    have hret := (d39DrawingRepresentationData3_original_iff_face_retained
      x r e.radius_pos d).mp hd
    have heq := reparam_retained_face_assignment x y Q hb e d hret
    apply (d39DrawingRepresentationData3_original_iff_face_retained y r e.radius_pos (E d)).mpr
    rw [← heq]
    exact (e.faceEquiv ⟨x.faceOfDart d.1, hret⟩).property

private theorem reparam_increasing_endpoints (φ : I ≃ₜ I) (hm : StrictMono φ) :
    φ 0 = 0 ∧ φ 1 = 1 := by
  constructor
  · obtain ⟨t, ht⟩ := φ.surjective 0
    exact le_antisymm ((hm.monotone bot_le).trans ht.le) bot_le
  · obtain ⟨t, ht⟩ := φ.surjective 1
    exact le_antisymm le_top (ht.symm.le.trans (hm.monotone le_top))

include ha hb in
/-- Helper toward Definition 3.8 consumers: the geometric ball homeomorphism
maps the represented PL dart paths with endpoint-preserving parameters. -/
theorem reparam_arc_map {r : ℕ}
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (d : {d : M.core.D // d ∈ d39BallDarts M r}) :
    ∃ ψ : I ≃ₜ I, ψ 0 = 0 ∧ ψ 1 = 1 ∧ ∀ t,
      e.h ((P.arc d.1).toPath t) =
        (Q.arc (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d).1).toPath
          (ψ t) := by
  let E := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e
  let φ := d39GeomBallIsoV2DartParam e
    ⟨(x.dartEquiv d.1).1, (d39DrawingRepresentationData3_ballDarts_iff x r d.1).mp d.2⟩
    (x.dartEquiv d.1).2
  obtain ⟨h0, h1⟩ := reparam_increasing_endpoints φ
    (d39GeomBallIsoV2DartParam_strictMono e _ _)
  obtain ⟨α, ha0, ha1, hα⟩ := ha d.1
  obtain ⟨β, hb0, hb1, hβ⟩ := hb (E d).1
  have ha0' : α.symm 0 = 0 := α.injective (by rw [α.apply_symm_apply, ha0])
  have ha1' : α.symm 1 = 1 := α.injective (by rw [α.apply_symm_apply, ha1])
  refine ⟨α.symm.trans (φ.trans β), ?_, ?_, ?_⟩
  · change β (φ (α.symm 0)) = 0
    rw [ha0', h0, hb0]
  · change β (φ (α.symm 1)) = 1
    rw [ha1', h1, hb1]
  · intro t
    have h := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_arc_map x y e d (α.symm t)
    change e.h (d39DrawingDartArc B x.toD39DrawingRepresentationData d.1 (α.symm t)) =
      d39DrawingDartArc C y.toD39DrawingRepresentationData (E d).1 (φ (α.symm t)) at h
    rw [hα, α.apply_symm_apply, hβ] at h
    exact h

include ha hb in
/-- Helper toward Definition 3.8 consumers: all restricted PL geometry,
including missing geometric edges, is carried by the ball homeomorphism. -/
theorem reparam_restricted_drawing_image (r : ℕ) (hr : 0 < r)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root) :
    e.h '' (d39FacedBallPLDrawing M P r hr).image =
      (d39FacedBallPLDrawing N Q r hr).image := by
  let E := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e
  have harc (d : (d39FacedBall M r hr).D) :
      e.h '' ((d39FacedBallPLDrawing M P r hr).arc d).image =
        ((d39FacedBallPLDrawing N Q r hr).arc (E d)).image := by
    change e.h '' (P.arc d.1).image = (Q.arc (E d).1).image
    rw [← Polyline.range_toPath, ← Polyline.range_toPath]
    obtain ⟨φ, _, _, hφ⟩ := reparam_arc_map x y P Q ha hb e d
    ext z
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨φ t, (hφ t).symm⟩
    · rintro ⟨t, rfl⟩
      refine ⟨(P.arc d.1).toPath (φ.symm t), ⟨φ.symm t, rfl⟩, ?_⟩
      simpa only [φ.apply_symm_apply] using hφ (φ.symm t)
  rw [(d39FacedBallPLDrawing M P r hr).image_eq_union_arcs
      (d39FacedBallPLDrawing_vertex_surjective M P r hr),
    (d39FacedBallPLDrawing N Q r hr).image_eq_union_arcs
      (d39FacedBallPLDrawing_vertex_surjective N Q r hr)]
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hw
    exact Set.mem_iUnion.mpr ⟨E d, (harc d) ▸ Set.mem_image_of_mem e.h hd⟩
  · intro hz
    obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hz
    obtain ⟨a, rfl⟩ := E.surjective d
    rw [← harc a] at hd
    obtain ⟨w, hw, rfl⟩ := hd
    exact ⟨w, Set.mem_iUnion.mpr ⟨a, hw⟩, rfl⟩

include ha hb in
/-- Helper toward Definition 3.8 consumers: the left restricted face of
every dart is transported, including faces that are not retained ambient faces. -/
theorem reparam_restricted_dart_face_image (r : ℕ) (hr : 0 < r)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (d : (d39FacedBall M r hr).D) :
    e.h '' ((d39FacedBall M r hr).plDartFace
      (restrictedVertex P (d39BallDarts M r)) (d39FacedBallPLDrawing M P r hr)
      (d39FacedBallPLDrawing_vertex_surjective M P r hr) d).val =
      ((d39FacedBall N r hr).plDartFace
        (restrictedVertex Q (d39BallDarts N r)) (d39FacedBallPLDrawing N Q r hr)
        (d39FacedBallPLDrawing_vertex_surjective N Q r hr)
        (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d)).val := by
  let P' := d39FacedBallPLDrawing M P r hr
  let Q' := d39FacedBallPLDrawing N Q r hr
  let E := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e
  let F := (d39FacedBall M r hr).plDartFace
    (restrictedVertex P (d39BallDarts M r)) P'
    (d39FacedBallPLDrawing_vertex_surjective M P r hr) d
  have himage : e.h '' P'.image = Q'.image :=
    reparam_restricted_drawing_image x y P Q ha hb r hr e
  let F' : Q'.Face := ⟨e.h '' F.val, by
    obtain ⟨z, hz, hF⟩ := F.property
    refine ⟨e.h z, ?_, ?_⟩
    · rw [← himage]
      rintro ⟨w, hw, heq⟩
      exact hz (e.h.injective heq ▸ hw)
    · rw [hF, ← himage]
      exact Homeomorph.image_connectedComponentIn_compl e.h P'.image z⟩
  obtain ⟨φ, h0, h1, harc⟩ := reparam_arc_map x y P Q ha hb e d
  have hborder : P'.dartBorders d F :=
    ((d39FacedBall M r hr).plDartFace_eq_iff _ P'
      (d39FacedBallPLDrawing_vertex_surjective M P r hr) d F).mp rfl
  have hleft : ∀ s : {t : I // t ∈ openParams},
      LeftAtOn F'.val (Q'.arc (E d)).toPath s := by
    apply (forall_leftAtOn_reparam_iff F'.val (Q'.arc (E d)).toPath φ h0 h1).mp
    intro s
    have hs := (leftAtOn_map_iff F.val (P'.arc d).toPath s
      e.h e.orientationPreserving).mp
      (P'.dartBorders_toPath_leftAtOn
        (d39FacedBallPLDrawing_vertex_surjective M P r hr) d F hborder s)
    exact (leftAtOn_congr_fun F'.val _ _ s harc).mp hs
  have htarget := LeftSideHalfDisk.dartBorders_of_forall_leftAtOn_of_surjective Q'
    (d39FacedBallPLDrawing_vertex_surjective N Q r hr) (E d) F' hleft
  exact (congrArg Subtype.val
    (((d39FacedBall N r hr).plDartFace_eq_iff _ Q'
      (d39FacedBallPLDrawing_vertex_surjective N Q r hr) (E d) F').mpr htarget)).symm

include ha hb in
/-- Helper toward Definition 3.8 consumers: the induced dart equivalence
preserves and reflects the actual unbounded restricted face orbit. -/
theorem reparam_external_iff (r : ℕ) (hr : 0 < r)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (d : (d39FacedBall M r hr).D) :
    d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d ∈
        (d39FacedBallPLWithExternal N Q r hr).externalOrbit.val ↔
      d ∈ (d39FacedBallPLWithExternal M P r hr).externalOrbit.val := by
  have hN := d39FacedBallPLWithExternal_mem_iff_not_isBounded_plDartFace N Q r hr
    (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d)
  have hM := d39FacedBallPLWithExternal_mem_iff_not_isBounded_plDartFace M P r hr d
  refine hN.trans ((not_congr ?_).trans hM.symm)
  rw [← reparam_restricted_dart_face_image x y P Q ha hb r hr e d]
  exact isBounded_planeHomeomorph_image_iff e.h _

end Pair
end DirectedDistances.PaperProofs.Section3.D39BallBridge

end
