/- Copyright (c) 2026 DirectedDistances contributors. All rights reserved. -/
module

public import DirectedDistances.PaperProofs.Section3.D39GeometricDartIso2
public import DirectedDistances.PaperProofs.Section3.D39GeometricDartIsoSymm

/-! # Restricting geometric dart ball isomorphisms to smaller radii -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open Set
open DirectedDistances.PlanarMap
open scoped ENNReal Topology

universe uV uE uV' uE'

namespace D39GeomBallIsoV2

variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
  {r s : ℕ} {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
  {M' : DirectedPlaneMapWithMissing V' E'} {rho' : E' × Bool}

/-- Helper toward Definition 3.8: a smaller retained-face set lies in its
larger-radius retained-face set. -/
theorem faceBall_mono (hsr : s ≤ r) {F}
    (hF : F ∈ d39GeomRetainedFaces M rho s) :
    F ∈ d39GeomRetainedFaces M rho r := by
  intro v hv
  exact vertexBall_mono (M := M) (rho := rho) hsr (hF v hv)

/-- Helper toward Definition 3.8: a dart ball isomorphism maps every face
retained at the smaller radius to a face retained at that radius. -/
theorem face_map_small (e : D39GeomBallIsoV2 r M rho M' rho')
    (hsr : s ≤ r) {F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face}
    (hF : F ∈ d39GeomRetainedFaces M rho s) :
    (e.faceEquiv ⟨F, faceBall_mono (M := M) (rho := rho) hsr hF⟩).1 ∈
      d39GeomRetainedFaces M' rho' s := by
  let Fr : {F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face //
      F ∈ d39GeomRetainedFaces M rho r} :=
    ⟨F, faceBall_mono (M := M) (rho := rho) hsr hF⟩
  let F'r := e.faceEquiv Fr
  intro w hw
  have hwR : w ∈ d39GeomBallVertices M' rho' r := F'r.2 w hw
  let v := e.vertexEquiv.symm ⟨w, hwR⟩
  have hvpos : e.h (M.toPlaneMapWithMissing.pos v.1) =
      M'.toPlaneMapWithMissing.pos w := by
    simpa [v] using e.pos_map v
  have hwpre : e.h.symm (M'.toPlaneMapWithMissing.pos w) ∈ closure F.1 := by
    have hwface : M'.toPlaneMapWithMissing.pos w ∈ closure F'r.1 := hw
    have hw' : M'.toPlaneMapWithMissing.pos w ∈ closure (e.h '' F.1) := by
      rw [← e.face_image_map Fr] at hwface
      exact hwface
    have hc := image_closure_subset_closure_image e.h.symm.continuous
      (s := e.h '' F.1)
    have hm : e.h.symm (M'.toPlaneMapWithMissing.pos w) ∈
        e.h.symm '' closure (e.h '' F.1) :=
      ⟨M'.toPlaneMapWithMissing.pos w, hw', rfl⟩
    have hsub := hc hm
    simpa [Set.image_image] using hsub
  have hvsmall : v.1 ∈ d39GeomBallVertices M rho s := hF v.1 (by
    have hp : M.toPlaneMapWithMissing.pos v.1 =
        e.h.symm (M'.toPlaneMapWithMissing.pos w) := by
      rw [← hvpos]
      simp
    simpa [hp] using hwpre)
  have hsmall := (restrictVertices e hsr ⟨v.1, hvsmall⟩).2
  have hvw : (restrictVertices e hsr ⟨v.1, hvsmall⟩).1 = w := by
    rw [restrictVertices_val]
    exact congrArg Subtype.val (Equiv.apply_symm_apply e.vertexEquiv ⟨w, hwR⟩)
  simpa [hvw] using hsmall

/-- Helper toward Definition 3.8: the inverse dart map sends a smaller
retained face back to a smaller retained face. -/
theorem face_map_small_symm (e : D39GeomBallIsoV2 r M rho M' rho')
    (hsr : s ≤ r) {F : M'.toPlaneMapWithMissing.toPlaneGraphDrawing.Face}
    (hF : F ∈ d39GeomRetainedFaces M' rho' s) :
    (e.faceEquiv.symm ⟨F,
      faceBall_mono (M := M') (rho := rho') hsr hF⟩).1 ∈
      d39GeomRetainedFaces M rho s := by
  simpa [D39GeomBallIsoV2.symm] using
    (face_map_small (e := D39GeomBallIsoV2.symm e) hsr hF)

/-- Helper toward Definition 3.8: the face equivalence preserves the
smaller-radius retained-face predicates in both directions. -/
theorem faceEquiv_preserves_small (e : D39GeomBallIsoV2 r M rho M' rho')
    (hsr : s ≤ r)
    (F : {F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face //
      F ∈ d39GeomRetainedFaces M rho r}) :
    F.1 ∈ d39GeomRetainedFaces M rho s ↔
      (e.faceEquiv F).1 ∈ d39GeomRetainedFaces M' rho' s := by
  constructor
  · exact face_map_small e hsr
  · intro hF
    have hback := face_map_small_symm e hsr hF
    have hround :
        (e.faceEquiv.symm ⟨(e.faceEquiv F).1,
          faceBall_mono (M := M') (rho := rho') hsr hF⟩).1 = F.1 := by
      exact congrArg Subtype.val (Equiv.symm_apply_apply e.faceEquiv F)
    simpa [hround] using hback

/-- Helper toward Definition 3.8: restrict the retained-face equivalence to
smaller-radius retained faces. -/
def restrictFaces (e : D39GeomBallIsoV2 r M rho M' rho') (hsr : s ≤ r) :
    {F // F ∈ d39GeomRetainedFaces M rho s} ≃
      {F // F ∈ d39GeomRetainedFaces M' rho' s} := by
  let L := Equiv.subtypeSubtypeEquivSubtype
    (p := fun F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face =>
      F ∈ d39GeomRetainedFaces M rho r)
    (q := fun F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face =>
      F ∈ d39GeomRetainedFaces M rho s)
    (fun {_} h => faceBall_mono (M := M) (rho := rho) hsr h)
  let R := Equiv.subtypeSubtypeEquivSubtype
    (p := fun F : M'.toPlaneMapWithMissing.toPlaneGraphDrawing.Face =>
      F ∈ d39GeomRetainedFaces M' rho' r)
    (q := fun F : M'.toPlaneMapWithMissing.toPlaneGraphDrawing.Face =>
      F ∈ d39GeomRetainedFaces M' rho' s)
    (fun {_} h => faceBall_mono (M := M') (rho := rho') hsr h)
  let mid := e.faceEquiv.subtypeEquiv
    (p := fun F : {F // F ∈ d39GeomRetainedFaces M rho r} =>
      F.1 ∈ d39GeomRetainedFaces M rho s)
    (q := fun F : {F // F ∈ d39GeomRetainedFaces M' rho' r} =>
      F.1 ∈ d39GeomRetainedFaces M' rho' s)
    (fun F => faceEquiv_preserves_small e hsr F)
  exact L.symm.trans (mid.trans R)

/-- Helper toward Definition 3.8: the restricted face equivalence acts on
faces by the original radius-`r` face equivalence. -/
theorem restrictFaces_val (e : D39GeomBallIsoV2 r M rho M' rho')
    (hsr : s ≤ r)
    (F : {F // F ∈ d39GeomRetainedFaces M rho s}) :
    (restrictFaces e hsr F).1 =
      (e.faceEquiv ⟨F.1, faceBall_mono (M := M) (rho := rho) hsr F.2⟩).1 := by
  rfl

/-- Helper toward Definition 3.8: the restricted face equivalence obeys the
geometric image identity at radius `s`. -/
theorem restrictFaces_image_map (e : D39GeomBallIsoV2 r M rho M' rho')
    (hsr : s ≤ r)
    (F : {F // F ∈ d39GeomRetainedFaces M rho s}) :
    e.h '' F.1 = (restrictFaces e hsr F).1 := by
  rw [restrictFaces_val]
  exact e.face_image_map ⟨F.1,
    faceBall_mono (M := M) (rho := rho) hsr F.2⟩

end D39GeomBallIsoV2

end DirectedDistances.PaperProofs.Section3

end
