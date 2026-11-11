/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact26
import DirectedDistances.PaperProofs.Section5.Prop516OriginalIffDirect6

/-! Helper toward Definition 3.2: the exclusive-side converses follow by
identifying the face selected by a local side test with the face bordering
the corresponding orientation of the dart on the first leg of its drawn arc. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk
open unitInterval

universe uV uE uUL uUR uLR uLL

/-- Helper toward Definition 3.2: a lower-right edge excluded from the
upper-left boundary cannot satisfy every left-side test along its forward
drawn arc. -/
theorem not_forall_leftAtOn_of_mem_lowerRight_not_mem_upperLeft32
    {V : Type uV} {E : Type uE}
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool)
    (h : IsBoundEdges32 M B G U S) (hfinite : LocallyFiniteVertexImage G)
    (e : E) (hp : ¬ M.toPlaneMapWithMissing.missing e)
    (hlr : e ∈ lowerRightBoundary32 B)
    (hnul : e ∉ upperLeftBoundary32 B) :
    ¬ ∀ s : {t : I // t ∈ openParams},
      LeftAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s := by
  intro hleft
  let d : E × Bool := (e, M.forward ⟨e, hp⟩)
  have hi : 0 + 1 < (G.arc d).points.length := by
    have := G.arc_length d
    omega
  let α := Polyline.segmentParameterStart 0
  let β := Polyline.segmentParameterEnd (G.arc d).points.length 0
  have hαβ : α < β := Polyline.segmentParameterStart_lt_end _ _
  let tval : ℝ := (α + β) / 2
  have hstart : α < tval := by dsimp [tval]; linarith
  have hend : tval < β := by dsimp [tval]; linarith
  have hα0 : 0 ≤ α := (Polyline.segmentParameterStart_mem_Icc 0).1
  have hβ1 : β ≤ 1 :=
    (Polyline.segmentParameterEnd_mem_Icc (G.arc d).points.length 0).2
  have ht0 : 0 ≤ tval := le_trans hα0 hstart.le
  have ht1 : tval ≤ 1 := hend.le.trans hβ1
  let t : I := ⟨tval, ⟨ht0, ht1⟩⟩
  have hstart' : α < (t : ℝ) := hstart
  have hend' : (t : ℝ) < β := hend
  have htopen : 0 < (t : ℝ) ∧ (t : ℝ) < 1 :=
    ⟨hα0.trans_lt hstart', hend'.trans_le hβ1⟩
  let s : {t : I // t ∈ openParams} := ⟨t, htopen⟩
  let p : ℂ := (G.arc d).toPath t
  have hpseg : p ∈ openSegment ℝ ((G.arc d).point 0) ((G.arc d).point 1) := by
    exact Polyline.toPath_mem_openSegment_of_parameter (G.arc d) hi t hstart' hend'
  obtain ⟨r, hr, hleftDisc⟩ :=
    exists_leftHalfDisc_subset_of_leftAtOn G hfinite d U hi hpseg s rfl (hleft s)
  obtain ⟨r', hr', hfaces, _⟩ :=
    exists_unique_oriented_halfDisc_faces_of_openSegment G hfinite d hi hpseg
  obtain ⟨F₀, hF₀, _⟩ := hfaces
  have hdir : (G.arc d).point 1 - (G.arc d).point 0 ≠ 0 :=
    sub_ne_zero.mpr (((G.arc_simple d).1 0 hi).symm)
  obtain ⟨z, hz⟩ := Polyline.leftHalfDisc_nonempty p
    ((G.arc d).point 1 - (G.arc d).point 0) (min r r') hdir (lt_min hr hr')
  have hzU : z ∈ U.val := hleftDisc ⟨
    Metric.ball_subset_ball (min_le_left r r') hz.1, hz.2⟩
  have hzF₀ : z ∈ F₀.val := hF₀.1 ⟨
    Metric.ball_subset_ball (min_le_right r r') hz.1, hz.2⟩
  have hUF₀ : U = F₀ := G.faces_eq_of_mem hzU hzF₀
  have hborder : G.dartBorders d U := hUF₀ ▸ hF₀.2
  exact hnul ((mem_upperLeftBoundary32_iff_forward_dartBorders h e).mpr ⟨hp, hborder⟩)

/-- Helper toward Definition 3.2: an upper-left edge excluded from the
lower-right boundary cannot satisfy every right-side test along its forward
drawn arc. -/
theorem not_forall_rightAtOn_of_mem_upperLeft_not_mem_lowerRight32
    {V : Type uV} {E : Type uE}
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool)
    (h : IsBoundEdges32 M B G U S) (hfinite : LocallyFiniteVertexImage G)
    (e : E) (hp : ¬ M.toPlaneMapWithMissing.missing e)
    (hul : e ∈ upperLeftBoundary32 B)
    (hnlr : e ∉ lowerRightBoundary32 B) :
    ¬ ∀ s : {t : I // t ∈ openParams},
      RightAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s := by
  intro hright
  let d : E × Bool := (e, M.forward ⟨e, hp⟩)
  have hleftFlip : ∀ s : {t : I // t ∈ openParams},
      LeftAtOn U.val (G.arc (e, !(M.forward ⟨e, hp⟩))).toPath s :=
    (G.forall_leftAtOn_flip_toPath_iff_forall_rightAtOn d U.val).mpr hright
  let d' : E × Bool := (e, !(M.forward ⟨e, hp⟩))
  have hi : 0 + 1 < (G.arc d').points.length := by
    have := G.arc_length d'
    omega
  let α := Polyline.segmentParameterStart 0
  let β := Polyline.segmentParameterEnd (G.arc d').points.length 0
  have hαβ : α < β := Polyline.segmentParameterStart_lt_end _ _
  let tval : ℝ := (α + β) / 2
  have hstart : α < tval := by dsimp [tval]; linarith
  have hend : tval < β := by dsimp [tval]; linarith
  have hα0 : 0 ≤ α := (Polyline.segmentParameterStart_mem_Icc 0).1
  have hβ1 : β ≤ 1 :=
    (Polyline.segmentParameterEnd_mem_Icc (G.arc d').points.length 0).2
  have ht0 : 0 ≤ tval := le_trans hα0 hstart.le
  have ht1 : tval ≤ 1 := hend.le.trans hβ1
  let t : I := ⟨tval, ⟨ht0, ht1⟩⟩
  have hstart' : α < (t : ℝ) := hstart
  have hend' : (t : ℝ) < β := hend
  have htopen : 0 < (t : ℝ) ∧ (t : ℝ) < 1 :=
    ⟨hα0.trans_lt hstart', hend'.trans_le hβ1⟩
  let s : {t : I // t ∈ openParams} := ⟨t, htopen⟩
  let p : ℂ := (G.arc d').toPath t
  have hpseg : p ∈ openSegment ℝ ((G.arc d').point 0) ((G.arc d').point 1) := by
    exact Polyline.toPath_mem_openSegment_of_parameter (G.arc d') hi t hstart' hend'
  obtain ⟨r, hr, hleftDisc⟩ :=
    exists_leftHalfDisc_subset_of_leftAtOn G hfinite d' U hi hpseg s rfl (hleftFlip s)
  obtain ⟨r', hr', hfaces, _⟩ :=
    exists_unique_oriented_halfDisc_faces_of_openSegment G hfinite d' hi hpseg
  obtain ⟨F₀, hF₀, _⟩ := hfaces
  have hdir : (G.arc d').point 1 - (G.arc d').point 0 ≠ 0 :=
    sub_ne_zero.mpr (((G.arc_simple d').1 0 hi).symm)
  obtain ⟨z, hz⟩ := Polyline.leftHalfDisc_nonempty p
    ((G.arc d').point 1 - (G.arc d').point 0) (min r r') hdir (lt_min hr hr')
  have hzU : z ∈ U.val := hleftDisc ⟨
    Metric.ball_subset_ball (min_le_left r r') hz.1, hz.2⟩
  have hzF₀ : z ∈ F₀.val := hF₀.1 ⟨
    Metric.ball_subset_ball (min_le_right r r') hz.1, hz.2⟩
  have hUF₀ : U = F₀ := G.faces_eq_of_mem hzU hzF₀
  have hborder : G.dartBorders d' U := hUF₀ ▸ hF₀.2
  exact hnlr ((mem_lowerRightBoundary32_iff_reverse_dartBorders h e).mpr ⟨hp, hborder⟩)

end DirectedDistances.PlanarMap

end
