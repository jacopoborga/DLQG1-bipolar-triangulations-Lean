/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516OriginalIffDirect7
public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation13





public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open unitInterval



theorem plRepresentation_signed_face_unique
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (R : PLCylinderBall.Representation M B) (d : M.core.D)
    (F : B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
    (hF : if (R.data.dartEquiv d).2 then
      B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf F (R.data.dartEquiv d).1
    else B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf F (R.data.dartEquiv d).1) :
    F = R.data.faceOfDart d := by
  let F' := d39PLRepresentationFace R.data.toD39DrawingRepresentationData
    R.drawing R.pos_eq R.arc_eq F
  let G' := d39PLRepresentationFace R.data.toD39DrawingRepresentationData
    R.drawing R.pos_eq R.arc_eq (R.data.faceOfDart d)
  have hvert : Function.Surjective (d39VertexClass M) := by
    intro v
    exact Quotient.exists_rep v
  have hleft : ∀ s : {t : I // t ∈ openParams},
      LeftAtOn F'.val (R.drawing.arc d).toPath s := by
    intro s
    change LeftAtOn F.val (R.drawing.arc d).toPath s
    cases hb : (R.data.dartEquiv d).2
    · rw [hb] at hF
      have hs : ∀ t : {t : I // t ∈ openParams},
          RightAtOn F.val (B.map.toPlaneMapWithMissing.arc (R.data.dartEquiv d).1) t := hF
      have hl := (forall_leftAtOn_symm_iff F.val
        (B.map.toPlaneMapWithMissing.arc (R.data.dartEquiv d).1)).mpr hs
      exact (leftAtOn_congr_fun F.val _ _ s (fun t => by
        rw [R.arc_eq, d39DrawingDartArc, hb]
        rfl)).mpr (hl s)
    · rw [hb] at hF
      exact (leftAtOn_congr_fun F.val _ _ s (fun t => by
        rw [R.arc_eq, d39DrawingDartArc, hb]
        rfl)).mpr (hF s)
  have heq : F' = G' := LeftSideHalfDisk.face_eq_of_forall_leftAtOn_of_surjective
    R.drawing hvert d F' G' hleft
    (d39PLRepresentation_face_leftAtOn R.data.toD39DrawingRepresentationData
      R.drawing R.arc_eq d)
  have hval : F.val = (R.data.faceOfDart d).val :=
    congrArg (fun Q : R.drawing.Face => Q.val) heq
  exact Subtype.ext hval

/-- Helper toward Proposition 5.16: the geometric ball's retained face map
agrees with dart-face assignment when the target has a compatible PL drawing.
This is a carrier-specific helper, not the unrestricted Data3 target. -/
theorem plRepresentation_geomBallIso_retained_face_assignment
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B) (R : PLCylinderBall.Representation N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (d : {d : M.core.D // d ∈ d39BallDarts M r})
    (hret : x.faceOfDart d.1 ∈ d39GeomRetainedFaces B.map B.root r) :
    (e.faceEquiv ⟨x.faceOfDart d.1, hret⟩).1 =
      R.data.faceOfDart (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x R.data e d).1 := by
  have hs := d39DrawingRepresentationData3_geomBallIso_faceEquiv_imageSide x R.data e d hret
  apply plRepresentation_signed_face_unique R _ _
  rw [hs.2.1]
  exact hs.1

/-- Helper toward Proposition 5.16: reversing the geometric ball comparison
reverses the induced equivalence on the represented darts. -/
theorem geomBallIso_ballDartEquiv_symm_apply
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B) (y : D39DrawingRepresentationData3 N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (q : {d : N.core.D // d ∈ d39BallDarts N r}) :
    d39DrawingRepresentationData3_geomBallIso_ballDartEquiv y x e.symm q =
      (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e).symm q := by
  rfl

/-- Helper toward Proposition 5.16: original-face membership is preserved
and reflected between existing compatible PL representations. -/
theorem plRepresentation_geomBallIso_original_face_preservation
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2} {r : ℕ}
    (R : PLCylinderBall.Representation M B) (S : PLCylinderBall.Representation N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (d : {d : M.core.D // d ∈ d39BallDarts M r}) :
    d39DrawingRepresentationData3_geomBallIso_ballDartEquiv R.data S.data e d ∈
        (d39FacedBall N r e.radius_pos).original ↔
      d ∈ (d39FacedBall M r e.radius_pos).original := by
  let E := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv R.data S.data e
  constructor
  · intro hd
    have hret := (d39DrawingRepresentationData3_original_iff_face_retained
      S.data r e.radius_pos (E d)).mp hd
    have heq := plRepresentation_geomBallIso_retained_face_assignment S.data R
      e.symm (E d) hret
    have hback : d39DrawingRepresentationData3_geomBallIso_ballDartEquiv
        S.data R.data e.symm (E d) = d := by
      rw [geomBallIso_ballDartEquiv_symm_apply]
      exact E.symm_apply_apply d
    rw [hback] at heq
    apply (d39DrawingRepresentationData3_original_iff_face_retained
      R.data r e.radius_pos d).mpr
    rw [← heq]
    exact (e.symm.faceEquiv ⟨S.data.faceOfDart (E d).val, hret⟩).property
  · intro hd
    have hret := (d39DrawingRepresentationData3_original_iff_face_retained
      R.data r e.radius_pos d).mp hd
    have heq := plRepresentation_geomBallIso_retained_face_assignment R.data S e d hret
    apply (d39DrawingRepresentationData3_original_iff_face_retained
      S.data r e.radius_pos (E d)).mpr
    rw [← heq]
    exact (e.faceEquiv ⟨R.data.faceOfDart d.val, hret⟩).property

/-- Helper toward Proposition 5.16: the actual canonical UIBHBOT drawing
has a unique face on each signed side. The proof uses its own geometric
edge carrier and does not require literal PL representation path equality. -/
theorem uibhbotCanonicalDomain_signed_face_unique
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (a : (uibhbotD39CanonicalRepresentation13Domain W D).E) (b : Bool)
    (F G : (uibhbotD39CanonicalRepresentation13Domain W D).map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
    (hF : if b then
      (uibhbotD39CanonicalRepresentation13Domain W D).map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf F a
    else (uibhbotD39CanonicalRepresentation13Domain W D).map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf F a)
    (hG : if b then
      (uibhbotD39CanonicalRepresentation13Domain W D).map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf G a
    else (uibhbotD39CanonicalRepresentation13Domain W D).map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf G a) :
    F = G := by
  let P := DirectedDistances.KMSW.uibhbotCcw_assemblyDrawing W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    (uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence)
    (uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence)
    (uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence)
    (uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary)
    (uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary)
    (uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary)
    (uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary)
  cases b
  · exact LeftSideHalfDisk.toPlaneGraphDrawing_right_face_unique_of_surjective P
      (DirectedDistances.KMSW.WholePlanePastGlueData.vertex_incident W) a F G hF hG
  · exact LeftSideHalfDisk.toPlaneGraphDrawing_left_face_unique_of_surjective P
      (DirectedDistances.KMSW.WholePlanePastGlueData.vertex_incident W) a F G hF hG

/-- Helper toward Proposition 5.16: retained-face assignment into the
actual canonical UIBHBOT domain, for any supplied Data3 representation. -/
theorem uibhbotCanonicalDomain_geomBallIso_retained_face_assignment
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    {M N : D39RootedMap} {B : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N (uibhbotD39CanonicalRepresentation13Domain W D))
    (e : D39GeomBallIsoV2 r B.map B.root
      (uibhbotD39CanonicalRepresentation13Domain W D).map
      (uibhbotD39CanonicalRepresentation13Domain W D).root)
    (d : {d : M.core.D // d ∈ d39BallDarts M r})
    (hret : x.faceOfDart d.1 ∈ d39GeomRetainedFaces B.map B.root r) :
    (e.faceEquiv ⟨x.faceOfDart d.1, hret⟩).1 =
      y.faceOfDart (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d).1 := by
  have hs := d39DrawingRepresentationData3_geomBallIso_faceEquiv_imageSide x y e d hret
  apply uibhbotCanonicalDomain_signed_face_unique W D _ _ _ _ hs.1
  have ht := hs.2.2
  rw [hs.2.1] at ht
  exact ht

/-- Helper toward Proposition 5.16: original-face membership is preserved
between an existing PL representation and the actual canonical UIBHBOT
domain, without requiring a literal PL representation of that domain. -/
theorem plRepresentation_uibhbotCanonicalDomain_original_face_preservation
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    {M N : D39RootedMap} {B : D39DomainRootedMapV2} {r : ℕ}
    (R : PLCylinderBall.Representation M B)
    (y : D39DrawingRepresentationData3 N (uibhbotD39CanonicalRepresentation13Domain W D))
    (e : D39GeomBallIsoV2 r B.map B.root
      (uibhbotD39CanonicalRepresentation13Domain W D).map
      (uibhbotD39CanonicalRepresentation13Domain W D).root)
    (d : {d : M.core.D // d ∈ d39BallDarts M r}) :
    d39DrawingRepresentationData3_geomBallIso_ballDartEquiv R.data y e d ∈
        (d39FacedBall N r e.radius_pos).original ↔
      d ∈ (d39FacedBall M r e.radius_pos).original := by
  let E := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv R.data y e
  constructor
  · intro hd
    have hret := (d39DrawingRepresentationData3_original_iff_face_retained
      y r e.radius_pos (E d)).mp hd
    have heq := plRepresentation_geomBallIso_retained_face_assignment y R
      e.symm (E d) hret
    have hback : d39DrawingRepresentationData3_geomBallIso_ballDartEquiv
        y R.data e.symm (E d) = d := by
      rw [geomBallIso_ballDartEquiv_symm_apply]
      exact E.symm_apply_apply d
    rw [hback] at heq
    apply (d39DrawingRepresentationData3_original_iff_face_retained
      R.data r e.radius_pos d).mpr
    rw [← heq]
    exact (e.symm.faceEquiv ⟨y.faceOfDart (E d).val, hret⟩).property
  · intro hd
    have hret := (d39DrawingRepresentationData3_original_iff_face_retained
      R.data r e.radius_pos d).mp hd
    have heq := uibhbotCanonicalDomain_geomBallIso_retained_face_assignment
      W D R.data y e d hret
    apply (d39DrawingRepresentationData3_original_iff_face_retained
      y r e.radius_pos (E d)).mpr
    rw [← heq]
    exact (e.faceEquiv ⟨R.data.faceOfDart d.val, hret⟩).property
































end DirectedDistances.PaperProofs.Section5
