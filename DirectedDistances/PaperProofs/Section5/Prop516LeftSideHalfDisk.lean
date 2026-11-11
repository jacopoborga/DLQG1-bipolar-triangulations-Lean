/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516FaceSideUniqueness
public import DirectedDistances.PaperProofs.Section5.Prop516ReverseComparison4
public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact13








public section

namespace DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk

open DirectedDistances.PlanarMap Set Metric

/-- Helper toward Proposition 5.16: at a strict point of a drawn straight
segment, one positive radius isolates that segment in the full drawing.
Both oriented open half-disks are connected and avoid the full drawing. -/
theorem exists_openSegment_halfDiscs
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hfinite : LocallyFiniteVertexImage P)
    (d : D) {i : ℕ} (hi : i + 1 < (P.arc d).points.length) {p : ℂ}
    (hp : p ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) :
    ∃ r : ℝ, 0 < r ∧
      (∀ y ∈ ball p r, y ∈ P.image ↔ y ∈ (P.arc d).segmentAt i) ∧
      IsConnected (Polyline.leftHalfDisc p
        ((P.arc d).point (i + 1) - (P.arc d).point i) r) ∧
      IsConnected (Polyline.rightHalfDisc p
        ((P.arc d).point (i + 1) - (P.arc d).point i) r) ∧
      Polyline.leftHalfDisc p ((P.arc d).point (i + 1) - (P.arc d).point i) r
        ⊆ P.imageᶜ ∧
      Polyline.rightHalfDisc p ((P.arc d).point (i + 1) - (P.arc d).point i) r
        ⊆ P.imageᶜ := by
  obtain ⟨N, hN, harc, hcover⟩ :=
    P.exists_local_image_of_locallyFiniteVertexImage32 hfinite d
  have hpimage : p ∈ (P.arc d).image :=
    (P.arc d).segmentAt_subset_image hi (openSegment_subset_segment ℝ _ _ hp)
  have hpN : p ∈ N := harc ((Polyline.range_toPath (P.arc d)).symm ▸ hpimage)
  obtain ⟨r, hr, _, hlocal⟩ :=
    P.openSegment_contact_local_image_of_local_image d hi hp N hN hpN hcover
  let u := (P.arc d).point (i + 1) - (P.arc d).point i
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i hi).symm
  have hline : (P.arc d).segmentAt i ⊆ Polyline.edgeLine p u :=
    Polyline.segment_subset_edgeLine _ _ p (openSegment_subset_segment ℝ _ _ hp)
  refine ⟨r, hr, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact ⟨hlocal y hy, fun hyseg => Or.inr ⟨d,
      (P.arc d).segmentAt_subset_image hi hyseg⟩⟩
  · exact Polyline.isConnected_leftHalfDisc p u r
      (Polyline.leftHalfDisc_nonempty p u r hu hr)
  · exact Polyline.isConnected_rightHalfDisc p u r
      (Polyline.rightHalfDisc_nonempty p u r hu hr)
  · intro y hy hyimage
    exact (Set.disjoint_left.mp (Polyline.disjoint_leftHalfDisc_edgeLine p u r))
      hy (hline (hlocal y hy.1 hyimage))
  · intro y hy hyimage
    exact (Set.disjoint_left.mp (Polyline.disjoint_rightHalfDisc_edgeLine p u r))
      hy (hline (hlocal y hy.1 hyimage))

/-- Helper toward Proposition 5.16: finite vertex sets satisfy the full
vertex-image condition, independently of whether dart incidence is surjective. -/
theorem locallyFiniteVertexImage_of_finite_vertices
    {D V : Type*} [Finite V] {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) : LocallyFiniteVertexImage P := by
  have h : (Set.range P.pos).Finite := Set.finite_range P.pos
  exact ⟨h.isClosed, h.isDiscrete⟩

/-- Helper toward Proposition 5.16: both sufficiently small half-disks
at a strict segment point are contained in unique complementary faces.
The two faces are allowed to coincide, as they can along a bridge. -/
theorem exists_openSegment_halfDiscs_unique_faces
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hfinite : LocallyFiniteVertexImage P)
    (d : D) {i : ℕ} (hi : i + 1 < (P.arc d).points.length) {p : ℂ}
    (hp : p ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) :
    ∃ r : ℝ, 0 < r ∧
      (∃! F : P.Face,
        Polyline.leftHalfDisc p ((P.arc d).point (i + 1) - (P.arc d).point i) r
          ⊆ F.val) ∧
      (∃! F : P.Face,
        Polyline.rightHalfDisc p ((P.arc d).point (i + 1) - (P.arc d).point i) r
          ⊆ F.val) := by
  obtain ⟨r, hr, _, hLc, hRc, hLa, hRa⟩ :=
    exists_openSegment_halfDiscs P hfinite d hi hp
  have hface {U : Set ℂ} (hconn : IsConnected U) (havoid : U ⊆ P.imageᶜ) :
      ∃! F : P.Face, U ⊆ F.val := by
    obtain ⟨x, hx⟩ := hconn.nonempty
    obtain ⟨F, hxF⟩ := (P.faces_cover_compl x).mpr (havoid hx)
    have hsub : U ⊆ F.val := by
      obtain ⟨z, _, hF⟩ := F.property
      rw [hF] at hxF ⊢
      rw [connectedComponentIn_eq hxF]
      exact hconn.isPreconnected.subset_connectedComponentIn hx havoid
    exact ⟨F, hsub, fun G hG => P.faces_eq_of_mem (hG hx) (hsub hx)⟩
  exact ⟨r, hr, hface hLc hLa, hface hRc hRa⟩

/-- Helper toward Proposition 5.16: one radius, independent of the face,
identifies containment of the entire left and right half-disks with the
respective dart borders. Faces accumulating at the segment point contain
at least one of these half-disks; this last assertion is unsigned. -/
theorem exists_openSegment_halfDiscs_face_classification
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hfinite : LocallyFiniteVertexImage P)
    (d : D) {i : ℕ} (hi : i + 1 < (P.arc d).points.length) {p : ℂ}
    (hp : p ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) :
    ∃ r : ℝ, 0 < r ∧
      (∀ F : P.Face,
        (Polyline.leftHalfDisc p ((P.arc d).point (i + 1) - (P.arc d).point i) r
          ⊆ F.val ↔ P.dartBorders d F)) ∧
      (∀ F : P.Face,
        (Polyline.rightHalfDisc p ((P.arc d).point (i + 1) - (P.arc d).point i) r
          ⊆ F.val ↔ P.dartBorders (flip d) F)) ∧
      (∀ F : P.Face, p ∈ closure F.val ↔
        (Polyline.leftHalfDisc p ((P.arc d).point (i + 1) - (P.arc d).point i) r
          ⊆ F.val) ∨
        (Polyline.rightHalfDisc p ((P.arc d).point (i + 1) - (P.arc d).point i) r
          ⊆ F.val)) := by
  obtain ⟨r, hr, hleft, hright⟩ :=
    P.exists_ball_face_mem_iff_dartBorders_of_openSegment32 hfinite d hi hp
  let u := (P.arc d).point (i + 1) - (P.arc d).point i
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i hi).symm
  have hL (F : P.Face) :
      Polyline.leftHalfDisc p u r ⊆ F.val ↔ P.dartBorders d F := by
    constructor
    · intro hsub
      obtain ⟨y, hy⟩ := Polyline.leftHalfDisc_nonempty p u r hu hr
      exact (hleft y hy.1 hy.2 F).mp (hsub hy)
    · intro hborder y hy
      exact (hleft y hy.1 hy.2 F).mpr hborder
  have hR (F : P.Face) :
      Polyline.rightHalfDisc p u r ⊆ F.val ↔ P.dartBorders (flip d) F := by
    constructor
    · intro hsub
      obtain ⟨y, hy⟩ := Polyline.rightHalfDisc_nonempty p u r hu hr
      exact (hright y hy.1 hy.2 F).mp (hsub hy)
    · intro hborder y hy
      exact (hright y hy.1 hy.2 F).mpr hborder
  refine ⟨r, hr, hL, hR, ?_⟩
  intro F
  rw [hL F, hR F]
  exact P.mem_closure_face_openSegment_iff_dartBorders_of_locallyFiniteVertexImage32
    hfinite d F hi hp

/-- Helper toward Proposition 5.16: a winding-left witness at a strict
segment point forces the face to contain a whole geometric half-disk.
The proved alternative retains both orientations; it does not identify
winding-left with geometric-left. The radius is uniform over all faces
and all tested parameters mapping to this point. -/
theorem exists_halfDisc_containment_alternative_of_leftAtOn
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hfinite : LocallyFiniteVertexImage P)
    (d : D) {i : ℕ} (hi : i + 1 < (P.arc d).points.length) {p : ℂ}
    (hp : p ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) :
    ∃ r : ℝ, 0 < r ∧ ∀ (F : P.Face)
      (s : {t : unitInterval // t ∈ openParams}),
      (P.arc d).toPath s.val = p → LeftAtOn F.val (P.arc d).toPath s →
      (Polyline.leftHalfDisc p ((P.arc d).point (i + 1) - (P.arc d).point i) r
        ⊆ F.val) ∨
      (Polyline.rightHalfDisc p ((P.arc d).point (i + 1) - (P.arc d).point i) r
        ⊆ F.val) := by
  obtain ⟨r, hr, _, _, hclass⟩ :=
    exists_openSegment_halfDiscs_face_classification P hfinite d hi hp
  refine ⟨r, hr, ?_⟩
  intro F s hsp hleft
  apply (hclass F).mp
  rw [← hsp]
  exact leftAtOn_mem_closure F.val (P.arc d).toPath s hleft

































































end DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk

end
