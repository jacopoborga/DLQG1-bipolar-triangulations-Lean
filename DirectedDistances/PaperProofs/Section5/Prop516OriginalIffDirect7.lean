/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516OriginalIffDirect6

/-! Helper toward Proposition 5.16: signed face uniqueness for PL drawings whose
vertices are all incident. This does not assert that arbitrary Data3 has a
with the sole coordinator. -/

public section

namespace DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk

open DirectedDistances.PlanarMap
open unitInterval

/-- Helper toward Proposition 5.16: bounded arc local finiteness controls
all vertex positions when every vertex is incident to a dart. -/
theorem locallyFiniteVertexImage_of_surjective
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert) :
    LocallyFiniteVertexImage P := by
  apply (locallyFiniteVertexImage_iff_finite_inter_isBounded P).mpr
  intro K hK
  refine ((P.locally_finite K hK).image (fun d => P.pos (vert d))).subset ?_
  rintro z ⟨hzK, v, rfl⟩
  obtain ⟨d, rfl⟩ := hvert v
  refine ⟨d, ⟨P.pos (vert d), hzK, ?_⟩, rfl⟩
  rw [← P.arc_start d]
  exact Or.inl rfl

/-- Helper toward Proposition 5.16: the simultaneous winding-left test
implies the geometric dart border, including when both sides have one face. -/
theorem dartBorders_of_forall_leftAtOn_of_surjective
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face)
    (hleft : ∀ s : {t : I // t ∈ openParams},
      LeftAtOn F.val (P.arc d).toPath s) : P.dartBorders d F := by
  have hfinite := locallyFiniteVertexImage_of_surjective P hvert
  have hi : 0 + 1 < (P.arc d).points.length := by
    have := P.arc_length d
    omega
  let α := Polyline.segmentParameterStart 0
  let β := Polyline.segmentParameterEnd (P.arc d).points.length 0
  have hαβ : α < β := Polyline.segmentParameterStart_lt_end _ _
  let tval : ℝ := (α + β) / 2
  have hstart : α < tval := by dsimp [tval]; linarith
  have hend : tval < β := by dsimp [tval]; linarith
  have hα0 : 0 ≤ α := (Polyline.segmentParameterStart_mem_Icc 0).1
  have hβ1 : β ≤ 1 :=
    (Polyline.segmentParameterEnd_mem_Icc (P.arc d).points.length 0).2
  let t : I := ⟨tval, hα0.trans hstart.le, hend.le.trans hβ1⟩
  let s : {t : I // t ∈ openParams} :=
    ⟨t, hα0.trans_lt hstart, hend.trans_le hβ1⟩
  let p : ℂ := (P.arc d).toPath t
  have hp : p ∈ openSegment ℝ ((P.arc d).point 0) ((P.arc d).point 1) :=
    Polyline.toPath_mem_openSegment_of_parameter (P.arc d) hi t hstart hend
  obtain ⟨r, hr, hleftDisc⟩ :=
    exists_leftHalfDisc_subset_of_leftAtOn P hfinite d F hi hp s rfl (hleft s)
  obtain ⟨r', hr', hfaces, _⟩ :=
    exists_unique_oriented_halfDisc_faces_of_openSegment P hfinite d hi hp
  obtain ⟨F₀, hF₀, _⟩ := hfaces
  have hdir : (P.arc d).point 1 - (P.arc d).point 0 ≠ 0 :=
    sub_ne_zero.mpr ((P.arc_simple d).1 0 hi).symm
  obtain ⟨z, hz⟩ := Polyline.leftHalfDisc_nonempty p
    ((P.arc d).point 1 - (P.arc d).point 0) (min r r') hdir (lt_min hr hr')
  have hzF : z ∈ F.val := hleftDisc
    ⟨Metric.ball_subset_ball (min_le_left r r') hz.1, hz.2⟩
  have hzF₀ : z ∈ F₀.val := hF₀.1
    ⟨Metric.ball_subset_ball (min_le_right r r') hz.1, hz.2⟩
  have heq : F = F₀ := P.faces_eq_of_mem hzF hzF₀
  exact heq ▸ hF₀.2

/-- Helper toward Proposition 5.16: two complementary faces passing all
left winding tests on the same incident PL dart are equal. -/
theorem face_eq_of_forall_leftAtOn_of_surjective
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F G : P.Face)
    (hF : ∀ s : {t : I // t ∈ openParams}, LeftAtOn F.val (P.arc d).toPath s)
    (hG : ∀ s : {t : I // t ∈ openParams}, LeftAtOn G.val (P.arc d).toPath s) :
    F = G := by
  exact P.dartBorders_face_unique d F G
    (dartBorders_of_forall_leftAtOn_of_surjective P hvert d F hF)
    (dartBorders_of_forall_leftAtOn_of_surjective P hvert d G hG)

/-- Helper toward Proposition 5.16: the general carrier of an incident PL
drawing has at most one face on the left of a stored geometric edge. -/
theorem toPlaneGraphDrawing_left_face_unique_of_surjective
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (e : P.GeometricEdge) (F G : P.toPlaneGraphDrawing.Face)
    (hF : P.toPlaneGraphDrawing.SideLeftOf F e)
    (hG : P.toPlaneGraphDrawing.SideLeftOf G e) : F = G := by
  apply P.toPlaneGraphDrawingFaceEquiv.injective
  exact face_eq_of_forall_leftAtOn_of_surjective P hvert e.out _ _
    (fun s => (P.toPlaneGraphDrawing_leftAtOn_iff e F s).mp (hF s))
    (fun s => (P.toPlaneGraphDrawing_leftAtOn_iff e G s).mp (hG s))

/-- Helper toward Proposition 5.16: the right side is unique as well;
polyline reversal is used through its proved reparameterization law. -/
theorem toPlaneGraphDrawing_right_face_unique_of_surjective
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (e : P.GeometricEdge) (F G : P.toPlaneGraphDrawing.Face)
    (hF : P.toPlaneGraphDrawing.SideRightOf F e)
    (hG : P.toPlaneGraphDrawing.SideRightOf G e) : F = G := by
  apply P.toPlaneGraphDrawingFaceEquiv.injective
  apply face_eq_of_forall_leftAtOn_of_surjective P hvert (flip e.out)
  · apply (P.forall_leftAtOn_flip_toPath_iff_forall_rightAtOn e.out _).mpr
    exact fun s => (P.toPlaneGraphDrawing_rightAtOn_iff e F s).mp (hF s)
  · apply (P.forall_leftAtOn_flip_toPath_iff_forall_rightAtOn e.out _).mpr
    exact fun s => (P.toPlaneGraphDrawing_rightAtOn_iff e G s).mp (hG s)

end DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk
