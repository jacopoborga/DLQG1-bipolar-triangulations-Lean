/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact7
import DirectedDistances.PlanarMap.D39PolygonParity
import DirectedDistances.PlanarMap.D39PolygonalConnected2

/-! # Signed accumulation for the winding-side converse

The winding test uses an arbitrary injective continuous return path, rather
than a geometric half-disk test. The results below retain the winding witness
remain with the sole coordinator. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval Set Metric
open scoped Topology

/-- Helper toward Definition 3.2: the locus of any fixed logarithmic winding
integer is open, with no regularity assumption on the continuous loop. -/
theorem isOpen_setOf_hasWinding32 {z : ℂ} (L : Path z z) (n : ℤ) :
    IsOpen {w : ℂ | HasWinding L w n} := by
  apply Metric.isOpen_iff.mpr
  intro w hw
  have havoid : ∀ t : I, L t ≠ w := by
    obtain ⟨φ, hφ, _⟩ := hw
    intro t ht
    have he : Complex.exp (φ t) = 0 := by rw [hφ t, ht, sub_self]
    exact Complex.exp_ne_zero _ he
  obtain ⟨r, hr, hnear⟩ := hasWinding_stable_nearby L w n havoid hw
  exact ⟨r, hr, fun w' hw' => hnear w' hw'⟩

/-- Helper toward Definition 3.2: winding accumulation in an open set
splits into accumulation from at least one strict transverse side, while
retaining the original loop and the original signed winding integer. -/
theorem mem_closure_winding_side_or32 {z : ℂ} (L : Path z z) (n : ℤ)
    (F : Set ℂ) (hF : IsOpen F) (x u : ℂ) (hu : u ≠ 0)
    (hx : x ∈ closure {w : ℂ | w ∈ F ∧ HasWinding L w n}) :
    x ∈ closure {w : ℂ | w ∈ F ∧ HasWinding L w n ∧
      0 < (star u * (w - x)).im} ∨
    x ∈ closure {w : ℂ | w ∈ F ∧ HasWinding L w n ∧
      (star u * (w - x)).im < 0} := by
  let A : Set ℂ := {w | w ∈ F ∧ HasWinding L w n}
  have hA : IsOpen A := hF.inter (isOpen_setOf_hasWinding32 L n)
  have hdense := (Polyline.dense_compl_edgeLine x u hu).open_subset_closure_inter hA
  have hcl : x ∈ closure (A ∩ (Polyline.edgeLine x u)ᶜ) := by
    exact (closure_minimal hdense isClosed_closure) hx
  have hsplit : A ∩ (Polyline.edgeLine x u)ᶜ =
      {w : ℂ | w ∈ F ∧ HasWinding L w n ∧ 0 < (star u * (w - x)).im} ∪
      {w : ℂ | w ∈ F ∧ HasWinding L w n ∧ (star u * (w - x)).im < 0} := by
    ext w
    constructor
    · rintro ⟨⟨hwF, hw⟩, hline⟩
      have hne : (star u * (w - x)).im ≠ 0 := hline
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · exact Or.inr ⟨hwF, hw, hneg⟩
      · exact Or.inl ⟨hwF, hw, hpos⟩
    · rintro (⟨hwF, hw, hpos⟩ | ⟨hwF, hw, hneg⟩)
      · exact ⟨⟨hwF, hw⟩, ne_of_gt hpos⟩
      · exact ⟨⟨hwF, hw⟩, ne_of_lt hneg⟩
  rw [hsplit, closure_union] at hcl
  exact hcl

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}

/-- Helper toward Definition 3.2: a return path whose open part is in a
face avoids every strictly intermediate point of the simple drawn arc.
Consequently it avoids an entire disk about the tested point. -/
theorem exists_ball_disjoint_returnPath32
    (P : PLDrawing D V flip rot vert) (d : D) (F : P.Face)
    (a b : I) (s : {t : I // t ∈ openParams})
    (has : a < s.val) (hsb : s.val < b)
    (q : Path ((P.arc d).toPath b) ((P.arc d).toPath a))
    (hqF : ∀ t : I, t ∈ openParams → q t ∈ F.val) :
    ∃ r : ℝ, 0 < r ∧ Disjoint (ball ((P.arc d).toPath s.val) r) (Set.range q) := by
  have hinj := (P.arc d).toPath_injective (P.arc_length d) (P.arc_simple d)
  have hximage : (P.arc d).toPath s.val ∈ P.image := by
    exact Or.inr ⟨d, (Polyline.range_toPath (P.arc d)) ▸ Set.mem_range_self s.val⟩
  have havoid : (P.arc d).toPath s.val ∉ Set.range q := by
    rintro ⟨t, ht⟩
    by_cases ht0 : t = 0
    · subst t
      rw [Path.source] at ht
      exact (ne_of_gt hsb) (hinj ht)
    by_cases ht1 : t = 1
    · subst t
      rw [Path.target] at ht
      exact (ne_of_lt has) (hinj ht)
    have htopen : t ∈ openParams :=
      ⟨unitInterval.pos_iff_ne_zero.mpr ht0, unitInterval.lt_one_iff_ne_one.mpr ht1⟩
    exact P.face_subset_compl F (ht ▸ hqF t htopen) hximage
  have hopen : IsOpen (Set.range q)ᶜ :=
    (isCompact_range q.continuous).isClosed.isOpen_compl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen _ havoid
  exact ⟨r, hr, Set.disjoint_left.mpr (fun y hy hq => hball hy hq)⟩

/-- Helper toward Definition 3.2: at a strict segment point, one common
radius identifies the faces of every positive and negative transverse point
by the corresponding original dart border. Both borders may have the same face. -/
theorem exists_ball_face_mem_iff_dartBorders_of_openSegment32
    (P : PLDrawing D V flip rot vert) (hfinite : LocallyFiniteVertexImage P)
    (d : D) {i : ℕ} (hi : i + 1 < (P.arc d).points.length) {x : ℂ}
    (hx : x ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) :
    ∃ r : ℝ, 0 < r ∧
      (∀ y ∈ ball x r,
        0 < (star ((P.arc d).point (i + 1) - (P.arc d).point i) * (y - x)).im →
        ∀ F : P.Face, y ∈ F.val ↔ P.dartBorders d F) ∧
      (∀ y ∈ ball x r,
        (star ((P.arc d).point (i + 1) - (P.arc d).point i) * (y - x)).im < 0 →
        ∀ F : P.Face, y ∈ F.val ↔ P.dartBorders (flip d) F) := by
  obtain ⟨G, hG, _⟩ := P.dartBorders_existsUnique_of_locallyFiniteVertexImage32 hfinite d
  obtain ⟨H, hH, _⟩ := P.dartBorders_existsUnique_of_locallyFiniteVertexImage32 hfinite (flip d)
  obtain ⟨r, hr, hleft⟩ :=
    P.dartBorders_openSegment_left_halfDisk_of_locallyFiniteVertexImage32 hfinite d G hG hi x hx
  obtain ⟨s, hs, hright⟩ :=
    P.dartBorders_flip_openSegment_right_halfDisk_of_locallyFiniteVertexImage32
      hfinite d H hH hi x hx
  refine ⟨min r s, lt_min hr hs, ?_, ?_⟩
  · intro y hy hpos F
    have hyG := hleft y (ball_subset_ball (min_le_left r s) hy) hpos
    constructor
    · intro hyF
      exact (P.faces_eq_of_mem hyG hyF) ▸ hG
    · intro hF
      exact (P.dartBorders_face_unique d G F hG hF) ▸ hyG
  · intro y hy hneg F
    have hyH := hright y (ball_subset_ball (min_le_right r s) hy) hneg
    constructor
    · intro hyF
      exact (P.faces_eq_of_mem hyH hyF) ▸ hH
    · intro hF
      exact (P.dartBorders_face_unique (flip d) H F hH hF) ▸ hyH

/-- Helper toward Definition 3.2: winding accumulation at a strict segment
point retains its sign and its loop in a two-orientation border alternative.
This does not identify winding sign with transverse sign. -/
theorem mem_closure_winding_border_cases_of_openSegment32
    (P : PLDrawing D V flip rot vert) (hfinite : LocallyFiniteVertexImage P)
    (d : D) (F : P.Face) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length) {x : ℂ}
    (hx : x ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    {z : ℂ} (L : Path z z) (n : ℤ)
    (hcl : x ∈ closure {w : ℂ | w ∈ F.val ∧ HasWinding L w n}) :
    (P.dartBorders d F ∧
      x ∈ closure {w : ℂ | w ∈ F.val ∧ HasWinding L w n ∧
        0 < (star ((P.arc d).point (i + 1) - (P.arc d).point i) * (w - x)).im}) ∨
    (P.dartBorders (flip d) F ∧
      x ∈ closure {w : ℂ | w ∈ F.val ∧ HasWinding L w n ∧
        (star ((P.arc d).point (i + 1) - (P.arc d).point i) * (w - x)).im < 0}) := by
  let u := (P.arc d).point (i + 1) - (P.arc d).point i
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i hi).symm
  obtain ⟨r, hr, hpos, hneg⟩ :=
    P.exists_ball_face_mem_iff_dartBorders_of_openSegment32 hfinite d hi hx
  rcases mem_closure_winding_side_or32 L n F.val
      (P.face_isOpen_of_locallyFiniteVertexImage32 hfinite F) x u hu hcl with hp | hn
  · obtain ⟨y, hy, hyx⟩ := Metric.mem_closure_iff.mp hp r hr
    have hyball : y ∈ ball x r := by simpa only [mem_ball, dist_comm] using hyx
    exact Or.inl ⟨(hpos y hyball hy.2.2 F).mp hy.1, hp⟩
  · obtain ⟨y, hy, hyx⟩ := Metric.mem_closure_iff.mp hn r hr
    have hyball : y ∈ ball x r := by simpa only [mem_ball, dist_comm] using hyx
    exact Or.inr ⟨(hneg y hyball hy.2.2 F).mp hy.1, hn⟩

end PLDrawing






































































































end DirectedDistances.PlanarMap

end
