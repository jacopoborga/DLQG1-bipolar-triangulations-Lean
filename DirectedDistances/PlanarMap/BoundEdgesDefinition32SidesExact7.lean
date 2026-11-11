/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact6
import DirectedDistances.PlanarMap.D39PolygonalConnected2

/-! # Local face incidence under a locally finite vertex image

The vertex-image hypothesis is displayed explicitly. These local component
lemmas retain the full drawing, including nonincident vertices. Signed
winding-to-border identification is a separate obligation, recorded below. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval Set Metric
open scoped Topology

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}

/-- Helper toward Definition 3.2: local finiteness of the full vertex image
makes the full drawing image closed, including nonincident vertices. -/
theorem image_isClosed_of_locallyFiniteVertexImage32
    (P : PLDrawing D V flip rot vert) (hfinite : LocallyFiniteVertexImage P) :
    IsClosed P.image := by
  have hlocal : LocallyFinite (fun d => (P.arc d).image) := by
    intro z
    refine ⟨ball z 1, ball_mem_nhds z zero_lt_one, ?_⟩
    simpa only [inter_comm] using P.locally_finite (ball z 1) isBounded_ball
  have harcs : IsClosed (⋃ d, (P.arc d).image) :=
    hlocal.isClosed_iUnion fun d => by
      rw [← Polyline.range_toPath]
      exact (isCompact_range (P.arc d).toPath.continuous).isClosed
  have himage : P.image = Set.range P.pos ∪ ⋃ d, (P.arc d).image := by
    ext z
    exact or_congr Iff.rfl Set.mem_iUnion.symm
  rw [himage]
  exact hfinite.1.union harcs

/-- Helper toward Definition 3.2: every face of the full drawing is open
under local finiteness of all vertex positions. -/
theorem face_isOpen_of_locallyFiniteVertexImage32
    (P : PLDrawing D V flip rot vert) (hfinite : LocallyFiniteVertexImage P)
    (F : P.Face) : IsOpen F.val := by
  obtain ⟨z, _, hF⟩ := F.property
  rw [hF]
  exact (P.image_isClosed_of_locallyFiniteVertexImage32 hfinite).isOpen_compl.connectedComponentIn

/-- Helper toward Definition 3.2: an arc-covered neighborhood of the dart
contains a left wedge avoiding the full drawing at its initial endpoint. -/
theorem wedgeIn_compl_image_of_local_image32
    (P : PLDrawing D V flip rot vert) (d : D)
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hcover : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) :
    WedgeIn (P.arc d).start (P.arc d).initialDirection P.imageᶜ := by
  obtain ⟨δ, hδ, hw⟩ := P.incidentVertexDrawing32.wedgeIn_compl_image
    P.incidentVertexDrawing32_surjective (P.arc d).start
    (P.arc d).initialDirection (P.initial_nonzero d)
  have hstart : (P.arc d).start ∈ N := harc ⟨0, (P.arc d).toPath.source⟩
  obtain ⟨η, hη, hηw⟩ := wedgeIn_of_mem_nhds
    (P.arc d).start (P.arc d).initialDirection (hN.mem_nhds hstart)
  refine ⟨min δ η, lt_min hδ hη, ?_⟩
  intro t ε ht htd he hed hz
  have hzN := hηw t ε ht (htd.trans_le (min_le_right _ _))
    he (hed.trans_le (min_le_right _ _))
  exact hw t ε ht (htd.trans_le (min_le_left _ _))
    he (hed.trans_le (min_le_left _ _))
    ((P.image_mem_iff_incidentVertexDrawing32_of_local_image N hcover hzN).mp hz)

/-- Helper toward Definition 3.2: each dart has a unique bordering face
under local finiteness of the full vertex image; no incidence surjectivity
is required. -/
theorem dartBorders_existsUnique_of_locallyFiniteVertexImage32
    (P : PLDrawing D V flip rot vert) (hfinite : LocallyFiniteVertexImage P)
    (d : D) : ∃! F : P.Face, P.dartBorders d F := by
  obtain ⟨N, hN, harc, hcover⟩ :=
    P.exists_local_image_of_locallyFiniteVertexImage32 hfinite d
  obtain ⟨F, hF⟩ := P.dartBorders_exists_of_wedge_compl d
    (P.wedgeIn_compl_image_of_local_image32 d N hN harc hcover)
  exact ⟨F, hF, fun H hH => P.dartBorders_face_unique d H F hH hF⟩

/-- Helper toward Definition 3.2: a bordering dart has a geometric left
half-disk in its face at every strict segment point under the displayed
local finiteness hypothesis. -/
theorem dartBorders_openSegment_left_halfDisk_of_locallyFiniteVertexImage32
    (P : PLDrawing D V flip rot vert) (hfinite : LocallyFiniteVertexImage P)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    {i : ℕ} (hi : i + 1 < (P.arc d).points.length) (q : ℂ)
    (hq : q ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball q r,
      0 < (star ((P.arc d).point (i + 1) - (P.arc d).point i) * (y - q)).im →
        y ∈ F.val := by
  obtain ⟨N, hN, harc, hcover⟩ :=
    P.exists_local_image_of_locallyFiniteVertexImage32 hfinite d
  exact P.dartBorders_openSegment_left_halfDisk_of_local_image
    d F hborder N hN harc hcover hi q hq

/-- Helper toward Definition 3.2: a bordering reverse dart has a geometric
right half-disk in its face at every strict original segment point. -/
theorem dartBorders_flip_openSegment_right_halfDisk_of_locallyFiniteVertexImage32
    (P : PLDrawing D V flip rot vert) (hfinite : LocallyFiniteVertexImage P)
    (d : D) (F : P.Face) (hborder : P.dartBorders (flip d) F)
    {i : ℕ} (hi : i + 1 < (P.arc d).points.length) (q : ℂ)
    (hq : q ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball q r,
      (star ((P.arc d).point (i + 1) - (P.arc d).point i) * (y - q)).im < 0 →
        y ∈ F.val := by
  let j := (P.arc d).points.length - 2 - i
  have hj : j + 1 < (P.arc d).points.length := by dsimp [j]; omega
  have hlen : (P.arc (flip d)).points.length = (P.arc d).points.length := by
    rw [P.arc_flip d]
    exact List.length_reverse
  have hj' : j + 1 < (P.arc (flip d)).points.length := by omega
  have hfirst : (P.arc (flip d)).point j = (P.arc d).point (i + 1) := by
    rw [P.arc_flip d, Polyline.point_reverse_transfer _ (by omega)]
    congr 1
    dsimp [j]
    omega
  have hlast : (P.arc (flip d)).point (j + 1) = (P.arc d).point i := by
    rw [P.arc_flip d, Polyline.point_reverse_transfer _ hj]
    congr 1
    dsimp [j]
    omega
  have hq' : q ∈ openSegment ℝ ((P.arc (flip d)).point j)
      ((P.arc (flip d)).point (j + 1)) := by
    rw [hfirst, hlast, openSegment_symm]
    exact hq
  obtain ⟨r, hr, hhalf⟩ :=
    P.dartBorders_openSegment_left_halfDisk_of_locallyFiniteVertexImage32
      hfinite (flip d) F hborder hj' q hq'
  refine ⟨r, hr, ?_⟩
  intro y hyr hyneg
  apply hhalf y hyr
  rw [hfirst, hlast, ← neg_sub ((P.arc d).point (i + 1)) ((P.arc d).point i),
    star_neg, neg_mul, Complex.neg_im]
  exact neg_pos.mpr hyneg

/-- Helper toward Definition 3.2: closure incidence at a strict segment
point is equivalent to bordering by one of the two original dart orientations.
This is an unsigned conclusion; along a bridge both alternatives may hold. -/
theorem mem_closure_face_openSegment_iff_dartBorders_of_locallyFiniteVertexImage32
    (P : PLDrawing D V flip rot vert) (hfinite : LocallyFiniteVertexImage P)
    (d : D) (F : P.Face) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length) {q : ℂ}
    (hq : q ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) :
    q ∈ closure F.val ↔ P.dartBorders d F ∨ P.dartBorders (flip d) F := by
  let u := (P.arc d).point (i + 1) - (P.arc d).point i
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i hi).symm
  constructor
  · intro hqF
    obtain ⟨G, hG, _⟩ := P.dartBorders_existsUnique_of_locallyFiniteVertexImage32 hfinite d
    obtain ⟨H, hH, _⟩ :=
      P.dartBorders_existsUnique_of_locallyFiniteVertexImage32 hfinite (flip d)
    obtain ⟨r, hr, hleft⟩ :=
      P.dartBorders_openSegment_left_halfDisk_of_locallyFiniteVertexImage32 hfinite d G hG hi q hq
    obtain ⟨s, hs, hright⟩ :=
      P.dartBorders_flip_openSegment_right_halfDisk_of_locallyFiniteVertexImage32
        hfinite d H hH hi q hq
    let W := F.val ∩ ball q (min r s)
    have hW : IsOpen W := (P.face_isOpen_of_locallyFiniteVertexImage32 hfinite F).inter isOpen_ball
    have hWne : W.Nonempty := by
      obtain ⟨y, hyF, hyq⟩ := Metric.mem_closure_iff.mp hqF (min r s) (lt_min hr hs)
      exact ⟨y, hyF, by simpa only [mem_ball, dist_comm] using hyq⟩
    obtain ⟨y, ⟨hyF, hyball⟩, hyline⟩ :=
      (Polyline.dense_compl_edgeLine q u hu).inter_open_nonempty W hW hWne
    have hside : (star u * (y - q)).im ≠ 0 := hyline
    rcases lt_or_gt_of_ne hside with hneg | hpos
    · have hyH := hright y (ball_subset_ball (min_le_right r s) hyball) hneg
      exact Or.inr ((P.faces_eq_of_mem hyH hyF) ▸ hH)
    · have hyG := hleft y (ball_subset_ball (min_le_left r s) hyball) hpos
      exact Or.inl ((P.faces_eq_of_mem hyG hyF) ▸ hG)
  · rintro (hborder | hborder)
    · obtain ⟨r, hr, hhalf⟩ :=
        P.dartBorders_openSegment_left_halfDisk_of_locallyFiniteVertexImage32
          hfinite d F hborder hi q hq
      exact closure_mono (s := Polyline.leftHalfDisc q u r) (fun y hy => hhalf y hy.1 hy.2)
        (Polyline.mem_closure_leftHalfDisc q u r hu hr)
    · obtain ⟨r, hr, hhalf⟩ :=
        P.dartBorders_flip_openSegment_right_halfDisk_of_locallyFiniteVertexImage32
          hfinite d F hborder hi q hq
      exact closure_mono (s := Polyline.rightHalfDisc q u r) (fun y hy => hhalf y hy.1 hy.2)
        (Polyline.mem_closure_rightHalfDisc q u r hu hr)

/-- Helper toward Definition 3.2: either winding-side test at one strict
segment parameter detects a bordering original dart, without selecting its
orientation. -/
theorem dartBorders_or_flip_of_toPath_windingSide_of_strictSegment32
    (P : PLDrawing D V flip rot vert) (hfinite : LocallyFiniteVertexImage P)
    (d : D) (F : P.Face) (s : {t : I // t ∈ openParams})
    {i : ℕ} (hi : i + 1 < (P.arc d).points.length)
    (hstart : Polyline.segmentParameterStart i < (s.val : ℝ))
    (hend : (s.val : ℝ) < Polyline.segmentParameterEnd (P.arc d).points.length i)
    (hside : LeftAtOn F.val (P.arc d).toPath s ∨
      RightAtOn F.val (P.arc d).toPath s) :
    P.dartBorders d F ∨ P.dartBorders (flip d) F := by
  apply (P.mem_closure_face_openSegment_iff_dartBorders_of_locallyFiniteVertexImage32
    hfinite d F hi (Polyline.toPath_mem_openSegment_of_parameter (P.arc d) hi s.val hstart hend)).mp
  rcases hside with hleft | hright
  · exact leftAtOn_mem_closure F.val (P.arc d).toPath s hleft
  · exact rightAtOn_mem_closure32 F.val (P.arc d).toPath s hright

/-- Helper toward Definition 3.2: all-parameter winding-side tests detect
one of the original oriented borders. The selected parameter is one quarter,
which lies strictly inside the first segment for every nonconstant arc. -/
theorem dartBorders_or_flip_of_forall_toPath_windingSide32
    (P : PLDrawing D V flip rot vert) (hfinite : LocallyFiniteVertexImage P)
    (d : D) (F : P.Face)
    (hside : ∀ s : {t : I // t ∈ openParams},
      LeftAtOn F.val (P.arc d).toPath s ∨ RightAtOn F.val (P.arc d).toPath s) :
    P.dartBorders d F ∨ P.dartBorders (flip d) F := by
  let s : {t : I // t ∈ openParams} :=
    ⟨⟨1 / 4, by norm_num⟩, by
      change 0 < (1 / 4 : ℝ) ∧ (1 / 4 : ℝ) < 1
      norm_num⟩
  apply P.dartBorders_or_flip_of_toPath_windingSide_of_strictSegment32
    hfinite d F s (i := 0) (by have := P.arc_length d; omega)
  · norm_num only [s, Polyline.segmentParameterStart_zero]
  · dsimp only [s, Polyline.segmentParameterEnd]
    split_ifs <;> norm_num
  · exact hside s

end PLDrawing

universe uV uE uUL uUR uLR uLL

/-- Helper toward Definition 3.2: the displayed local finiteness hypothesis
and all forward-arc winding-side tests place a present edge on one of the two
present sides. Selecting UL versus LR still requires signed identification. -/
theorem mapFaceU_windingSide_imp_mem_upperLeft_or_lowerRightBoundary32
    {V : Type uV} {E : Type uE}
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool)
    (h : IsBoundEdges32 M B G U S) (hfinite : LocallyFiniteVertexImage G) (e : E)
    (hside : ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
      ∀ s : {t : I // t ∈ openParams},
        LeftAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s ∨
        RightAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s) :
    e ∈ upperLeftBoundary32 B ∨ e ∈ lowerRightBoundary32 B := by
  obtain ⟨hp, htests⟩ := hside
  rcases G.dartBorders_or_flip_of_forall_toPath_windingSide32
      hfinite (e, M.forward ⟨e, hp⟩) U htests with hf | hr
  · exact Or.inl ((mem_upperLeftBoundary32_iff_forward_dartBorders h e).mpr ⟨hp, hf⟩)
  · exact Or.inr ((mem_lowerRightBoundary32_iff_reverse_dartBorders h e).mpr ⟨hp, hr⟩)































































































end DirectedDistances.PlanarMap

end
