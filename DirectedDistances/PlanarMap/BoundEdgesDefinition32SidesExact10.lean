/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact9
import DirectedDistances.PlanarMap.D39PolygonalConnected
import DirectedDistances.PlanarMap.GeneralPlaneMapOrientedSideTransport

/-! # Unbounded complementary sets and winding -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval Set Metric
open scoped Topology

/-- Helper toward Definition 3.2: every continuous loop has winding zero
outside some disk, without polygonal or simplicity hypotheses. -/
theorem exists_radius_hasWinding_zero32 {z : ℂ} (L : Path z z) :
    ∃ R : ℝ, ∀ w : ℂ, R < ‖w‖ → HasWinding L w 0 := by
  obtain ⟨R, hR⟩ := (isCompact_range L.continuous).isBounded.subset_closedBall (0 : ℂ)
  refine ⟨max R 0, ?_⟩
  intro w hw
  apply hasWinding_zero_of_norm_bound L (le_max_right R 0) _ hw
  intro t
  have ht := hR (Set.mem_range_self t)
  exact (show ‖L t‖ ≤ R by
    simpa only [mem_closedBall, dist_zero_right] using ht).trans (le_max_left R 0)

/-- Helper toward Definition 3.2: winding vanishes throughout any
unbounded preconnected set avoiding the loop, by constancy and a far point. -/
theorem hasWinding_zero_on_unbounded_preconnected32 {z : ℂ} (L : Path z z)
    (U : Set ℂ) (hconn : IsPreconnected U)
    (havoid : U ⊆ (Set.range L)ᶜ)
    (hunbounded : ∀ R : ℝ, ∃ w ∈ U, R < ‖w‖) :
    ∀ w ∈ U, HasWinding L w 0 := by
  obtain ⟨n, hn⟩ := hasWinding_value_constant_on_preconnected L U havoid hconn
  obtain ⟨R, hR⟩ := exists_radius_hasWinding_zero32 L
  obtain ⟨v, hv, hvR⟩ := hunbounded R
  have hn0 : n = 0 := hasWinding_unique (hn v hv) (hR v hvR)
  intro w hw
  exact hn0 ▸ hn w hw

/-- Helper toward Definition 3.2: a path from a viewpoint to a sufficiently
far point, avoiding the loop throughout, forces winding zero at the viewpoint.
The radius depends only on the loop, uniformly over all avoiding paths. -/
theorem exists_radius_hasWinding_zero_of_avoiding_path32 {z : ℂ} (L : Path z z) :
    ∃ R : ℝ, ∀ (w v : ℂ) (p : Path w v),
      Set.range p ⊆ (Set.range L)ᶜ → R < ‖v‖ → HasWinding L w 0 := by
  obtain ⟨R, hR⟩ := exists_radius_hasWinding_zero32 L
  refine ⟨R, ?_⟩
  intro w v p hp hv
  obtain ⟨n, hn⟩ := hasWinding_value_constant_on_preconnected L (Set.range p) hp
    (isConnected_range p.continuous).isPreconnected
  have hn0 : n = 0 := hasWinding_unique (hn v ⟨1, p.target⟩) (hR v hv)
  exact hn0 ▸ hn w ⟨0, p.source⟩

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}

/-- Helper toward Definition 3.2: a path in the drawing closed by a return
inside a different face has winding zero on every unbounded face it avoids.
The endpoints of the return path are covered by the drawing path. -/
theorem hasWinding_zero_of_return_in_other_face32
    (P : PLDrawing D V flip rot vert) (F U : P.Face) (hne : U ≠ F)
    (hU : P.IsUnbounded U) {a b : ℂ} (γ : Path a b) (q : Path b a)
    (hγ : Set.range γ ⊆ P.image)
    (hqF : ∀ t : I, t ∈ openParams → q t ∈ F.val) :
    ∀ w ∈ U.val, HasWinding (γ.trans q) w 0 := by
  have hconn : IsPreconnected U.val := by
    obtain ⟨z, _, hz⟩ := U.property
    rw [hz]
    exact isPreconnected_connectedComponentIn
  apply hasWinding_zero_on_unbounded_preconnected32 _ U.val hconn _ hU
  intro w hw hloop
  rw [Path.trans_range] at hloop
  rcases hloop with hγw | ⟨t, ht⟩
  · exact P.face_subset_compl U hw (hγ hγw)
  · by_cases ht0 : t = 0
    · subst t
      rw [Path.source] at ht
      exact P.face_subset_compl U hw (ht ▸ hγ ⟨1, γ.target⟩)
    by_cases ht1 : t = 1
    · subst t
      rw [Path.target] at ht
      exact P.face_subset_compl U hw (ht ▸ hγ ⟨0, γ.source⟩)
    have htopen : t ∈ openParams :=
      ⟨unitInterval.pos_iff_ne_zero.mpr ht0, unitInterval.lt_one_iff_ne_one.mpr ht1⟩
    exact hne (P.faces_eq_of_mem hw (ht ▸ hqF t htopen))

/-- Helper toward Definition 3.2: the actual paused PL subarc occurring
in `LeftAtOn`, closed through another face, has winding zero on any
unbounded face different from the return face. -/
theorem hasWinding_zero_edgeSubarc_of_other_unbounded_face32
    (P : PLDrawing D V flip rot vert) (d : D) (F U : P.Face)
    (hne : U ≠ F) (hU : P.IsUnbounded U) (a b : I) (hab : a ≤ b)
    (q : Path ((P.arc d).toPath b) ((P.arc d).toPath a))
    (hqF : ∀ t : I, t ∈ openParams → q t ∈ F.val) :
    ∀ w ∈ U.val,
      HasWinding ((edgeSubarc (P.arc d).toPath a b hab).trans q) w 0 := by
  apply P.hasWinding_zero_of_return_in_other_face32 F U hne hU _ q _ hqF
  rintro w ⟨t, rfl⟩
  rw [edgeSubarc_apply_clamp]
  exact Or.inr ⟨d, (Polyline.range_toPath (P.arc d)) ▸
    Set.mem_range_self (min (max t a) b)⟩

/-- Helper toward Definition 3.2: all-parameter left tests identify the
forward border when the reverse border belongs to a different face.
This incidence consequence does not need that other face to be unbounded. -/
theorem dartBorders_of_forall_leftAtOn_of_other_reverse_face32
    (P : PLDrawing D V flip rot vert) (hfinite : LocallyFiniteVertexImage P)
    (d : D) (F U : P.Face) (hne : U ≠ F)
    (hreverse : P.dartBorders (flip d) U)
    (hleft : ∀ s : {t : I // t ∈ openParams},
      LeftAtOn F.val (P.arc d).toPath s) : P.dartBorders d F := by
  rcases P.dartBorders_or_flip_of_forall_toPath_windingSide32 hfinite d F
      (fun s => Or.inl (hleft s)) with hf | hr
  · exact hf
  · exact (hne (P.dartBorders_face_unique (flip d) U F hreverse hr)).elim

/-- Helper toward Definition 3.2: when the reverse side is an unbounded
face different from the return face, an isolated drawn segment has winding
zero on its right half-disk and one on its left half-disk. -/
theorem exists_halfDisk_winding_one_zero_of_unbounded_reverse_face32
    (P : PLDrawing D V flip rot vert) (hfinite : LocallyFiniteVertexImage P)
    (d : D) (F U : P.Face) (hne : U ≠ F) (hU : P.IsUnbounded U)
    (hborder : P.dartBorders (flip d) U) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length) {x : ℂ}
    (hx : x ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (q : Path ((P.arc d).point (i + 1)) ((P.arc d).point i))
    (hqF : ∀ t : I, t ∈ openParams → q t ∈ F.val) :
    ∃ r : ℝ, 0 < r ∧
      (∀ u ∈ ball x r,
        0 < (star ((P.arc d).point (i + 1) - (P.arc d).point i) * (u - x)).im →
        HasWinding ((Path.segment ((P.arc d).point i)
          ((P.arc d).point (i + 1))).trans q) u 1) ∧
      (∀ v ∈ ball x r,
        (star ((P.arc d).point (i + 1) - (P.arc d).point i) * (v - x)).im < 0 →
        HasWinding ((Path.segment ((P.arc d).point i)
          ((P.arc d).point (i + 1))).trans q) v 0) := by
  let a := (P.arc d).point i
  let b := (P.arc d).point (i + 1)
  have hab : a ≠ b := (P.arc_simple d).1 i hi
  have hseg : Set.range (Path.segment a b) ⊆ P.image := by
    intro w hw
    apply Or.inr
    refine ⟨d, Or.inr ⟨i, hi, ?_⟩⟩
    change w ∈ segment ℝ a b
    simpa only [Path.range_segment] using hw
  have hximage : x ∈ P.image := by
    apply hseg
    rw [Path.range_segment]
    exact openSegment_subset_segment ℝ a b hx
  have havoid : x ∉ Set.range q := by
    have hxa : x ≠ a := fun h => hab (left_mem_openSegment_iff.mp (h ▸ hx))
    have hxb : x ≠ b := fun h => hab (right_mem_openSegment_iff.mp (h ▸ hx))
    rintro ⟨t, ht⟩
    by_cases ht0 : t = 0
    · subst t
      rw [Path.source] at ht
      exact hxb ht.symm
    by_cases ht1 : t = 1
    · subst t
      rw [Path.target] at ht
      exact hxa ht.symm
    exact P.face_subset_compl F
      (ht ▸ hqF t ⟨unitInterval.pos_iff_ne_zero.mpr ht0,
        unitInterval.lt_one_iff_ne_one.mpr ht1⟩) hximage
  obtain ⟨s, hs, hsball⟩ := Metric.isOpen_iff.mp
    (isCompact_range q.continuous).isClosed.isOpen_compl x havoid
  obtain ⟨t, ht, htU⟩ :=
    P.dartBorders_flip_openSegment_right_halfDisk_of_locallyFiniteVertexImage32
      hfinite d U hborder hi x hx
  let r := min s t
  have hr : 0 < r := lt_min hs ht
  have hdisj : Disjoint (ball x r) (Set.range q) := by
    apply Set.disjoint_left.mpr
    intro w hw
    exact hsball (ball_subset_ball (min_le_left s t) hw)
  obtain ⟨n, hnleft, hnright⟩ :=
    exists_segment_return_halfDisk_winding32 hab hx hr q hdisj
  have hzero := P.hasWinding_zero_of_return_in_other_face32 F U hne hU
    (Path.segment a b) q hseg hqF
  have hdir : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  obtain ⟨v, hv⟩ := Polyline.rightHalfDisc_nonempty x (b - a) r hdir hr
  have hvU := htU v (ball_subset_ball (min_le_right s t) hv.1) hv.2
  have hn0 : n = 0 := hasWinding_unique (hnright v hv.1 hv.2) (hzero v hvU)
  refine ⟨r, hr, ?_, ?_⟩
  · simpa only [hn0, zero_add] using hnleft
  · simpa only [hn0] using hnright

/-- Helper toward Definition 3.2: for a straight drawn segment closed
inside a face different from its unbounded reverse face, winding-one
accumulation in the return face is exactly the forward border condition. -/
theorem mem_closure_winding_one_iff_dartBorders_of_unbounded_reverse_face32
    (P : PLDrawing D V flip rot vert) (hfinite : LocallyFiniteVertexImage P)
    (d : D) (F U : P.Face) (hne : U ≠ F) (hU : P.IsUnbounded U)
    (hreverse : P.dartBorders (flip d) U) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length) {x : ℂ}
    (hx : x ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (q : Path ((P.arc d).point (i + 1)) ((P.arc d).point i))
    (hqF : ∀ t : I, t ∈ openParams → q t ∈ F.val) :
    (x ∈ closure {w : ℂ | w ∈ F.val ∧
      HasWinding ((Path.segment ((P.arc d).point i)
        ((P.arc d).point (i + 1))).trans q) w 1}) ↔ P.dartBorders d F := by
  constructor
  · intro hcl
    rcases P.mem_closure_winding_border_cases_of_openSegment32 hfinite d F hi hx
        _ 1 hcl with ⟨hF, _⟩ | ⟨hF, _⟩
    · exact hF
    · exact (hne (P.dartBorders_face_unique (flip d) U F hreverse hF)).elim
  · intro hF
    obtain ⟨r, hr, hwind, _⟩ :=
      P.exists_halfDisk_winding_one_zero_of_unbounded_reverse_face32
        hfinite d F U hne hU hreverse hi hx q hqF
    obtain ⟨s, hs, hface⟩ :=
      P.dartBorders_openSegment_left_halfDisk_of_locallyFiniteVertexImage32
        hfinite d F hF hi x hx
    have hdir : (P.arc d).point (i + 1) - (P.arc d).point i ≠ 0 :=
      sub_ne_zero.mpr ((P.arc_simple d).1 i hi).symm
    apply closure_mono _ (Polyline.mem_closure_leftHalfDisc x
      ((P.arc d).point (i + 1) - (P.arc d).point i) (min r s) hdir (lt_min hr hs))
    intro w hw
    exact ⟨hface w (ball_subset_ball (min_le_right r s) hw.1) hw.2,
      hwind w (ball_subset_ball (min_le_left r s) hw.1) hw.2⟩

end PLDrawing















































































































end DirectedDistances.PlanarMap

end
