/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLPolygonDiskChart2

/-! # Local sectors at extreme polygon vertices

Helpers toward Proposition 5.16. These geometric dependencies do not assert -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
namespace Polyline
open Topology

/-- Helper toward Proposition 5.16: a real-coordinate lower bound on all
listed vertices extends to every geometric edge, including the repeated root. -/
theorem re_le_of_mem_image (c : Polyline) (a : ℝ)
    (hpoints : ∀ j, j < c.points.length → a ≤ (c.point j).re)
    {z : ℂ} (hz : z ∈ c.image) : a ≤ z.re := by
  rcases hz with hz | ⟨j, hj, hz⟩
  · rw [Set.mem_singleton_iff] at hz
    rw [hz, ← point_zero_eq_start c]
    exact hpoints 0 (List.length_pos_iff.mpr c.nonempty)
  · obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    have hja := hpoints j (by omega)
    have hjb := hpoints (j + 1) hj
    calc
      a = s * a + t * a := by rw [← add_mul, hst, one_mul]
      _ ≤ s * (c.point j).re + t * (c.point (j + 1)).re :=
        add_le_add (mul_le_mul_of_nonneg_left hja hs)
          (mul_le_mul_of_nonneg_left hjb ht)

/-- Helper toward Proposition 5.16: every preconnected set avoiding a closed
polygon lies entirely in one winding side. -/
theorem subset_inside_or_outside_of_isPreconnected (c : Polyline)
    (hclosed : c.start = c.finish) (s : Set ℂ) (hs : IsPreconnected s)
    (havoid : s ⊆ c.imageᶜ) : s ⊆ c.inside ∨ s ⊆ c.outside := by
  apply hs.subset_or_subset (isOpen_inside c hclosed) (isOpen_outside c hclosed)
    (disjoint_inside_outside c)
  rw [inside_union_outside]
  exact havoid

/-- Helper toward Proposition 5.16: the open half-plane strictly left of a
supporting vertical line belongs to the outside. No strictness is required of
the supporting bound on the image, so vertical incident edges are allowed. -/
theorem re_lt_subset_outside (c : Polyline) (hclosed : c.start = c.finish)
    (a : ℝ) (hbound : ∀ z ∈ c.image, a ≤ z.re) :
    {z : ℂ | z.re < a} ⊆ c.outside := by
  let s : Set ℂ := {z : ℂ | z.re < a}
  have havoid : s ⊆ c.imageᶜ := fun z hz hzi => (not_le_of_gt hz) (hbound z hzi)
  obtain ⟨R, hR⟩ := exists_radius_exterior_subset_outside c hclosed
  let q : ℂ := (a - (|a| + |R| + 1) : ℝ)
  have hqre : q.re = a - (|a| + |R| + 1) := Complex.ofReal_re _
  have hqs : q ∈ s := by
    change q.re < a
    rw [hqre]
    linarith only [abs_nonneg a, abs_nonneg R]
  have hqnorm : R < ‖q‖ := by
    have hnorm := Complex.abs_re_le_norm q
    have hneg := neg_le_abs q.re
    have ha := le_abs_self a
    have hRabs := le_abs_self R
    rw [hqre] at hneg hnorm
    linarith only [hnorm, hneg, ha, hRabs]
  have hqo := hR q hqnorm
  rcases subset_inside_or_outside_of_isPreconnected c hclosed s
      (convex_halfSpace_re_lt a).isPreconnected havoid with hin | hout
  · exact False.elim ((hin hqs).2 hqo.2)
  · exact hout

/-- Helper toward Proposition 5.16: every local triangular sector supplied
by Chart2 is connected; its winding side is therefore constant. -/
theorem triangle_sector_subset_inside_or_outside (c : Polyline)
    (hclosed : c.start = c.finish) (u v w : ℂ) (r : ℝ)
    (havoid : Disjoint (Metric.ball v r ∩ _root_.interior
      (convexHull ℝ ({u, v, w} : Set ℂ))) c.image) :
    Metric.ball v r ∩ _root_.interior (convexHull ℝ ({u, v, w} : Set ℂ)) ⊆ c.inside ∨
    Metric.ball v r ∩ _root_.interior (convexHull ℝ ({u, v, w} : Set ℂ)) ⊆ c.outside := by
  apply subset_inside_or_outside_of_isPreconnected c hclosed
    _ ((convex_ball v r).inter (convex_convexHull ℝ _).interior).isPreconnected
  exact fun _ hz => Set.disjoint_left.mp havoid hz

/-- Helper toward Proposition 5.16: a closed transverse half-plane is convex. -/
theorem convex_transverse_nonneg (v d : ℂ) :
    Convex ℝ {z : ℂ | 0 ≤ (star d * (z - v)).im} := by
  let F : ℂ →ₗ[ℝ] ℂ := {
    toFun := fun z => star d * z
    map_add' := fun _ _ => mul_add _ _ _
    map_smul' := by
      intro t z
      simp only [RCLike.real_smul_eq_coe_mul]
      ac_rfl }
  have hb := (convex_halfSpace_im_ge 0).linear_preimage F
  change Convex ℝ ((fun z : ℂ => z - v) ⁻¹' (F ⁻¹' {w : ℂ | 0 ≤ w.im}))
  simpa only [sub_eq_add_neg] using hb.translate_preimage_left (-v)

/-- Helper toward Proposition 5.16: an interior point of a set supported by
a nondegenerate line lies strictly on the supported side. -/
theorem transverse_pos_of_mem_interior (v d : ℂ) (hd : d ≠ 0)
    (s : Set ℂ) (hs : ∀ z ∈ s, 0 ≤ (star d * (z - v)).im)
    {z : ℂ} (hz : z ∈ _root_.interior s) :
    0 < (star d * (z - v)).im := by
  have hn := hs z (interior_subset hz)
  apply lt_of_le_of_ne hn
  intro heq
  obtain ⟨w, hws, hw⟩ := mem_closure_iff.mp
    (mem_closure_rightHalfDisc z d 1 hd (by norm_num))
    (_root_.interior s) isOpen_interior hz
  have hwneg := hw.2
  have hid : star d * (w - v) = star d * (w - z) + star d * (z - v) := by ring
  have hnw := hs w (interior_subset hws)
  rw [hid, Complex.add_im, ← heq, add_zero] at hnw
  exact (not_lt_of_ge hnw) hwneg

/-- Helper toward Proposition 5.16: the interior of a positively oriented
neighbour triangle lies between its two incident supporting rays. -/
theorem triangle_interior_transverse_pos (v a b : ℂ)
    (hcross : 0 < (star (a - v) * (b - v)).im)
    {z : ℂ} (hz : z ∈ _root_.interior
      (convexHull ℝ ({a, v, b} : Set ℂ))) :
    0 < (star (a - v) * (z - v)).im ∧
      (star (b - v) * (z - v)).im < 0 := by
  have hself (d : ℂ) : (star d * d).im = 0 := by
    have h := transverse_swap d d
    linarith only [h]
  have ha : a - v ≠ 0 := by
    intro h
    simp only [h, star_zero, zero_mul, Complex.zero_im] at hcross
    exact (lt_irrefl 0) hcross
  have hb : -(b - v) ≠ 0 := by
    intro h
    have h' := neg_eq_zero.mp h
    simp only [h', mul_zero, Complex.zero_im] at hcross
    exact (lt_irrefl 0) hcross
  have hA : ∀ y ∈ convexHull ℝ ({a, v, b} : Set ℂ),
      0 ≤ (star (a - v) * (y - v)).im := by
    apply convexHull_min _ (convex_transverse_nonneg v (a - v))
    intro y hy
    change 0 ≤ (star (a - v) * (y - v)).im
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact (hself _).ge
    · simp only [sub_self, mul_zero, Complex.zero_im, le_refl]
    · exact hcross.le
  have hB : ∀ y ∈ convexHull ℝ ({a, v, b} : Set ℂ),
      0 ≤ (star (-(b - v)) * (y - v)).im := by
    apply convexHull_min _ (convex_transverse_nonneg v (-(b - v)))
    intro y hy
    change 0 ≤ (star (-(b - v)) * (y - v)).im
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    simp only [star_neg, neg_mul, Complex.neg_im]
    rcases hy with rfl | rfl | rfl
    · rw [transverse_swap, neg_neg]
      exact hcross.le
    · simp only [sub_self, mul_zero, Complex.zero_im, neg_zero, le_refl]
    · rw [hself, neg_zero]
  refine ⟨transverse_pos_of_mem_interior v (a - v) ha _ hA hz, ?_⟩
  have ht := transverse_pos_of_mem_interior v (-(b - v)) hb _ hB hz
  simpa only [star_neg, neg_mul, Complex.neg_im, neg_pos] using ht

/-- Helper toward Proposition 5.16: a transverse bound at the three vertices
extends throughout their closed triangle. -/
theorem transverse_nonneg_on_triangle (v a b d : ℂ)
    (ha : 0 ≤ (star d * (a - v)).im)
    (hb : 0 ≤ (star d * (b - v)).im) :
    ∀ z ∈ convexHull ℝ ({a, v, b} : Set ℂ),
      0 ≤ (star d * (z - v)).im := by
  apply convexHull_min _ (convex_transverse_nonneg v d)
  intro z hz
  change 0 ≤ (star d * (z - v)).im
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  · exact ha
  · simp only [sub_self, mul_zero, Complex.zero_im, le_refl]
  · exact hb

/-- Helper toward Proposition 5.16: a noncollinear neighbour triangle has a
nonzero signed transverse coordinate. -/
theorem transverse_ne_zero_of_not_collinear (v a b : ℂ)
    (hnc : ¬ Collinear ℝ ({a, v, b} : Set ℂ)) :
    (star (a - v) * (b - v)).im ≠ 0 := by
  intro heq
  have hd : a - v ≠ 0 := by
    intro h
    have hav := sub_eq_zero.mp h
    apply hnc
    simpa only [hav, Set.insert_idem] using collinear_pair ℝ v b
  have hself : (star (a - v) * (a - v)).im = 0 := by
    have h := transverse_swap (a - v) (a - v)
    linarith only [h]
  have hp := transverse_nonneg_on_triangle v a b (a - v) hself.ge heq.ge
  have hm := transverse_nonneg_on_triangle v a b (-(a - v))
    (by simp only [star_neg, neg_mul, Complex.neg_im, hself, neg_zero, le_refl])
    (by simp only [star_neg, neg_mul, Complex.neg_im, heq, neg_zero, le_refl])
  obtain ⟨z, hz⟩ := triangle_interior_nonempty a v b hnc
  have hpos := transverse_pos_of_mem_interior v (a - v) hd _ hp hz
  have hnonpos := hm z (interior_subset hz)
  simp only [star_neg, neg_mul, Complex.neg_im, neg_nonneg] at hnonpos
  exact (not_lt_of_ge hnonpos) hpos

/-- Helper toward Proposition 5.16: for two positively ordered rays at a
left supporting vertex, the local reflex region is outside the polygon. -/
theorem reflex_region_subset_outside_of_cross_pos (c : Polyline)
    (hclosed : c.start = c.finish) (v a b : ℂ) (r : ℝ) (hr : 0 < r)
    (hcross : 0 < (star (a - v) * (b - v)).im)
    (ha : v.re ≤ a.re) (hb : v.re ≤ b.re)
    (hbound : ∀ z ∈ c.image, v.re ≤ z.re)
    (hlocal : ∀ z ∈ Metric.ball v r,
      z ∈ c.image ↔ z ∈ segment ℝ v a ∪ segment ℝ v b) :
    rightHalfDisc v (a - v) r ∪ leftHalfDisc v (b - v) r ⊆ c.outside := by
  let u := a - v
  let e := b - v
  obtain ⟨_, hRinter⟩ := halfDisc_sector_intersections_nonempty v u e r hr hcross
  have hRc : IsConnected (rightHalfDisc v u r ∪ leftHalfDisc v e r) :=
    (isConnected_rightHalfDisc _ _ _ (hRinter.mono Set.inter_subset_left)).union hRinter
      (isConnected_leftHalfDisc _ _ _ (hRinter.mono Set.inter_subset_right))
  have hself (d : ℂ) : (star d * d).im = 0 := by
    have h := transverse_swap d d
    linarith only [h]
  have havoid : rightHalfDisc v u r ∪ leftHalfDisc v e r ⊆ c.imageᶜ := by
    intro z hz hzi
    rcases hz with hz | hz
    · rcases (hlocal z hz.1).mp hzi with hza | hzb
      · have hn := transverse_nonneg_segment v a u z (hself u).ge hza
        exact (not_lt_of_ge hn) hz.2
      · have hn := transverse_nonneg_segment v b u z hcross.le hzb
        exact (not_lt_of_ge hn) hz.2
    · rcases (hlocal z hz.1).mp hzi with hza | hzb
      · have heq : (star e * (a - v)).im = -(star u * e).im := transverse_swap e u
        have hn := transverse_nonneg_segment v a (-e) z (by
          simp only [star_neg, neg_mul, Complex.neg_im, heq, neg_neg]
          exact hcross.le) hza
        have hn' : (star e * (z - v)).im ≤ 0 := by
          simpa only [star_neg, neg_mul, Complex.neg_im, neg_nonneg] using hn
        exact (not_lt_of_ge hn') hz.2
      · have hn := transverse_nonneg_segment v b (-e) z (by
          change 0 ≤ (star (-e) * e).im
          simp only [star_neg, neg_mul, Complex.neg_im, hself e, neg_zero, le_refl]) hzb
        have hn' : (star e * (z - v)).im ≤ 0 := by
          simpa only [star_neg, neg_mul, Complex.neg_im, neg_nonneg] using hn
        exact (not_lt_of_ge hn') hz.2
  have hreal : 0 < (u + e).re := by
    have hu : 0 ≤ u.re := sub_nonneg.mpr ha
    have he : 0 ≤ e.re := sub_nonneg.mpr hb
    apply lt_of_le_of_ne (by simpa only [Complex.add_re] using add_nonneg hu he)
    intro hzero
    have hu0 : u.re = 0 := by simp only [Complex.add_re] at hzero; linarith only [hu, he, hzero]
    have he0 : e.re = 0 := by simp only [Complex.add_re] at hzero; linarith only [hu, he, hzero]
    have hc0 : (star u * e).im = 0 := by
      simp only [Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        hu0, he0, zero_mul, mul_zero, add_zero]
    exact (ne_of_gt hcross) hc0
  obtain ⟨t, ht, htr⟩ := exists_pos_mul_lt hr ‖u + e‖
  let q := v - t • (u + e)
  have hqball : q ∈ Metric.ball v r := by
    simp only [q, Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg,
      norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact (mul_comm t ‖u + e‖) ▸ htr
  have hqleft : q.re < v.re := by
    change (v - t • (u + e)).re < v.re
    simp only [Complex.sub_re, Complex.smul_re, smul_eq_mul]
    exact sub_lt_self _ (mul_pos ht hreal)
  have hqR : q ∈ rightHalfDisc v u r ∪ leftHalfDisc v e r := by
    left
    refine ⟨hqball, ?_⟩
    change (star u * (v - t • (u + e) - v)).im < 0
    rw [sub_sub_cancel_left, mul_neg, Complex.neg_im, transverse_smul, mul_add,
      Complex.add_im, hself u, zero_add]
    exact neg_neg_of_pos (mul_pos ht hcross)
  have hqo := re_lt_subset_outside c hclosed v.re hbound hqleft
  rcases subset_inside_or_outside_of_isPreconnected c hclosed _ hRc.isPreconnected
      havoid with hin | hout
  · exact False.elim ((hin hqR).2 hqo.2)
  · exact hout

/-- Helper toward Proposition 5.16: when a polygon locally consists of two
positively ordered incident edges at a left supporting boundary point, its
open neighbour-triangle sector is inside. -/
theorem triangle_sector_subset_inside_of_cross_pos (c : Polyline)
    (hc : c.IsCyclicSimple) (v a b : ℂ) (hv : v ∈ c.image)
    (r : ℝ) (hr : 0 < r)
    (hcross : 0 < (star (a - v) * (b - v)).im)
    (ha : v.re ≤ a.re) (hb : v.re ≤ b.re)
    (hbound : ∀ z ∈ c.image, v.re ≤ z.re)
    (hlocal : ∀ z ∈ Metric.ball v r,
      z ∈ c.image ↔ z ∈ segment ℝ v a ∪ segment ℝ v b) :
    Metric.ball v r ∩ _root_.interior
      (convexHull ℝ ({a, v, b} : Set ℂ)) ⊆ c.inside := by
  have hclosed : c.start = c.finish := by
    rw [← point_zero_eq_start c, ← point_last_eq_finish c]
    exact hc.2.1
  let u := a - v
  let e := b - v
  have hu : u ≠ 0 := by
    intro h
    change 0 < (star u * e).im at hcross
    simp only [h, star_zero, zero_mul, Complex.zero_im, lt_self_iff_false] at hcross
  have he : e ≠ 0 := by
    intro h
    change 0 < (star u * e).im at hcross
    simp only [h, mul_zero, Complex.zero_im, lt_self_iff_false] at hcross
  have hR := reflex_region_subset_outside_of_cross_pos c hclosed v a b r hr
    hcross ha hb hbound hlocal
  let L := leftHalfDisc v u r ∩ rightHalfDisc v e r
  have hLc : IsPreconnected L :=
    ((convex_leftHalfDisc v u r).inter (convex_rightHalfDisc v e r)).isPreconnected
  have hLavoid : L ⊆ c.imageᶜ := by
    intro z hz hzi
    have hsegs := (hlocal z hz.1.1).mp hzi
    rcases hsegs with hza | hzb
    · have hline := segment_subset_edgeLine v a v (left_mem_segment ℝ v a) hza
      exact (ne_of_gt hz.1.2) hline
    · have hline := segment_subset_edgeLine v b v (left_mem_segment ℝ v b) hzb
      exact (ne_of_lt hz.2.2) hline
  have hvcl : v ∈ closure c.inside := by
    have hvfront : v ∈ frontier c.inside :=
      (frontier_inside_outside_eq_image_cyclic c hc).1.symm ▸ hv
    exact frontier_subset_closure hvfront
  obtain ⟨x, hxball, hxinside⟩ := mem_closure_iff.mp hvcl
    (Metric.ball v r) Metric.isOpen_ball (Metric.mem_ball_self hr)
  let O := c.inside ∩ Metric.ball v r
  have hO : IsOpen O := (isOpen_inside c hclosed).inter Metric.isOpen_ball
  obtain ⟨y, hy, hyu, hye⟩ := exists_mem_open_off_two_edgeLines O hO
    ⟨x, hxinside, hxball⟩ v u e hu he
  have hyL : y ∈ L := by
    have hyupos : 0 < (star u * (y - v)).im := by
      apply lt_of_le_of_ne _ (Ne.symm hyu)
      apply le_of_not_gt
      intro hneg
      have hyo := hR (Or.inl ⟨hy.2, hneg⟩)
      exact hy.1.2 hyo.2
    have hyeneg : (star e * (y - v)).im < 0 := by
      apply lt_of_le_of_ne _ hye
      apply le_of_not_gt
      intro hpos
      have hyo := hR (Or.inr ⟨hy.2, hpos⟩)
      exact hy.1.2 hyo.2
    exact ⟨⟨hy.2, hyupos⟩, ⟨hy.2, hyeneg⟩⟩
  have hLin : L ⊆ c.inside := by
    rcases subset_inside_or_outside_of_isPreconnected c hclosed L hLc hLavoid with hi | ho
    · exact hi
    · exact False.elim (hy.1.2 (ho hyL).2)
  intro z hz
  have ht := triangle_interior_transverse_pos v a b hcross hz.2
  exact hLin ⟨⟨hz.1, ht.1⟩, ⟨hz.1, ht.2⟩⟩

/-- Helper toward Proposition 5.16: the local sector is inside for either
orientation of a nondegenerate neighbour triangle at a left supporting point. -/
theorem triangle_sector_subset_inside_of_support (c : Polyline)
    (hc : c.IsCyclicSimple) (v a b : ℂ) (hv : v ∈ c.image)
    (r : ℝ) (hr : 0 < r)
    (hnc : ¬ Collinear ℝ ({a, v, b} : Set ℂ))
    (ha : v.re ≤ a.re) (hb : v.re ≤ b.re)
    (hbound : ∀ z ∈ c.image, v.re ≤ z.re)
    (hlocal : ∀ z ∈ Metric.ball v r,
      z ∈ c.image ↔ z ∈ segment ℝ v a ∪ segment ℝ v b) :
    Metric.ball v r ∩ _root_.interior
      (convexHull ℝ ({a, v, b} : Set ℂ)) ⊆ c.inside := by
  rcases (transverse_ne_zero_of_not_collinear v a b hnc).lt_or_gt with hn | hp
  · have hpos : 0 < (star (b - v) * (a - v)).im := by
      rw [transverse_swap]
      exact neg_pos.mpr hn
    have hsets : ({b, v, a} : Set ℂ) = {a, v, b} := by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have hlocal' : ∀ z ∈ Metric.ball v r,
        z ∈ c.image ↔ z ∈ segment ℝ v b ∪ segment ℝ v a := by
      simpa only [Set.union_comm] using hlocal
    simpa only [hsets] using triangle_sector_subset_inside_of_cross_pos c hc v b a hv
      r hr hpos hb ha hbound hlocal'
  · exact triangle_sector_subset_inside_of_cross_pos c hc v a b hv r hr hp ha hb hbound hlocal

/-- Helper toward Proposition 5.16: every cyclically simple polygon has a
lexicographically least vertex with a nonempty local neighbour-triangle sector
contained in its inside. Equal real coordinates are resolved by the imaginary
coordinate; the repeated root and vertical incident edges are retained. -/
theorem exists_local_triangle_sector_subset_inside_cyclic (c : Polyline)
    (hc : c.IsCyclicSimple) :
    ∃ i : ℕ, i + 1 < c.points.length ∧
      (∀ j : ℕ, j + 1 < c.points.length → c.point j ≠ c.point i →
        (c.point i).re < (c.point j).re ∨
          (c.point i).re = (c.point j).re ∧ (c.point i).im < (c.point j).im) ∧
      let k := if i = 0 then c.points.length - 2 else i - 1
      ¬ Collinear ℝ ({c.point k, c.point i, c.point (i + 1)} : Set ℂ) ∧
      ∃ r : ℝ, 0 < r ∧
        (Metric.ball (c.point i) r ∩ _root_.interior
          (convexHull ℝ ({c.point k, c.point i, c.point (i + 1)} : Set ℂ))).Nonempty ∧
        Metric.ball (c.point i) r ∩ _root_.interior
          (convexHull ℝ ({c.point k, c.point i, c.point (i + 1)} : Set ℂ)) ⊆ c.inside := by
  obtain ⟨i, hi, hmin, hnc⟩ := exists_noncollinear_lexicographic_min_vertex c hc
  let k := if i = 0 then c.points.length - 2 else i - 1
  have hk : k + 1 < c.points.length := by
    dsimp only [k]
    split_ifs <;> have := hc.1 <;> omega
  have hkv : c.point (k + 1) = c.point i := by
    dsimp only [k]
    split_ifs with h
    · rw [show c.points.length - 2 + 1 = c.points.length - 1 by have := hc.1; omega]
      exact hc.2.1.symm.trans (congrArg c.point h.symm)
    · congr 1
      omega
  have hpoint (j : ℕ) (hj : j + 1 < c.points.length) :
      (c.point i).re ≤ (c.point j).re := by
    by_cases heq : c.point j = c.point i
    · exact heq ▸ le_rfl
    · exact (hmin j hj heq).elim le_of_lt (fun h => h.1.le)
  have hpoints (j : ℕ) (hj : j < c.points.length) :
      (c.point i).re ≤ (c.point j).re := by
    by_cases hj' : j + 1 < c.points.length
    · exact hpoint j hj'
    · have hjlast : j = c.points.length - 1 := by omega
      rw [hjlast, ← hc.2.1]
      exact hpoint 0 (by have := hc.1; omega)
  obtain ⟨r, hr, hlocal⟩ := exists_pos_ball_image_eq_incident_segments_cyclic c hc i hi
  have hlocal' : ∀ z ∈ Metric.ball (c.point i) r,
      z ∈ c.image ↔ z ∈ segment ℝ (c.point i) (c.point k) ∪
        segment ℝ (c.point i) (c.point (i + 1)) := by
    intro z hz
    have hh := hlocal z hz
    change z ∈ c.image ↔ z ∈ c.segmentAt k ∪ c.segmentAt i at hh
    simpa only [segmentAt, hkv, segment_symm ℝ (c.point k) (c.point i)] using hh
  refine ⟨i, hi, hmin, hnc, r, hr, ?_, ?_⟩
  · have hv : c.point i ∈ closure (_root_.interior
        (convexHull ℝ ({c.point k, c.point i, c.point (i + 1)} : Set ℂ))) := by
      rw [closure_triangle_interior _ _ _ hnc]
      exact subset_convexHull ℝ _ (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true])
    obtain ⟨z, hz, hd⟩ := Metric.mem_closure_iff.mp hv r hr
    exact ⟨z, ⟨by simpa only [Metric.mem_ball, dist_comm] using hd, hz⟩⟩
  · exact triangle_sector_subset_inside_of_support c hc _ _ _
      (c.point_mem_image (by omega)) r hr hnc (hpoint k hk) (hpoints (i + 1) hi)
      (fun z hz => re_le_of_mem_image c _ hpoints hz) hlocal'

/-- Helper toward Proposition 5.16: the open part of one edge misses every
other edge of a cyclically simple polygon, including the first/last pair. -/
theorem disjoint_openSegment_segmentAt_cyclic (c : Polyline) (hc : c.IsCyclicSimple)
    (i j : ℕ) (hi : i + 1 < c.points.length) (hj : j + 1 < c.points.length)
    (hne : i ≠ j) :
    Disjoint (openSegment ℝ (c.point i) (c.point (i + 1))) (c.segmentAt j) := by
  have hleft : c.point i ∉ openSegment ℝ (c.point i) (c.point (i + 1)) := by
    rw [left_mem_openSegment_iff]
    exact hc.2.2.1 i hi
  have hright : c.point (i + 1) ∉ openSegment ℝ (c.point i) (c.point (i + 1)) := by
    rw [right_mem_openSegment_iff]
    exact hc.2.2.1 i hi
  apply Set.disjoint_left.mpr
  intro z hzo hzj
  have hzi : z ∈ c.segmentAt i := openSegment_subset_segment ℝ _ _ hzo
  rcases lt_or_gt_of_ne hne with hij | hji
  · by_cases hadj : i + 1 = j
    · have hz : z = c.point (i + 1) := Set.mem_singleton_iff.mp
        (hc.2.2.2.1 i (by omega) ▸ ⟨hzi, hadj.symm ▸ hzj⟩)
      exact hright (hz ▸ hzo)
    · by_cases hwrap : i = 0 ∧ j + 2 = c.points.length
      · have hz : z = c.point 0 := Set.mem_singleton_iff.mp
          (hc.2.2.2.2.2 ▸ (show z ∈ c.segmentAt 0 ∩
            c.segmentAt (c.points.length - 2) from by
              simpa only [Set.mem_inter_iff, hwrap.1, show j = c.points.length - 2 by omega] using And.intro hzi hzj))
        exact hleft (by simpa only [hwrap.1, hz] using hzo)
      · exact Set.disjoint_left.mp (hc.2.2.2.2.1 i j hi hj (by omega) hwrap) hzi hzj
  · by_cases hadj : j + 1 = i
    · have hz : z = c.point i := by
        have hz' : z = c.point (j + 1) := Set.mem_singleton_iff.mp
          (hc.2.2.2.1 j (by omega) ▸ ⟨hzj, hadj.symm ▸ hzi⟩)
        exact hz'.trans (congrArg c.point hadj)
      exact hleft (hz ▸ hzo)
    · by_cases hwrap : j = 0 ∧ i + 2 = c.points.length
      · have hz : z = c.point 0 := Set.mem_singleton_iff.mp
          (hc.2.2.2.2.2 ▸ (show z ∈ c.segmentAt 0 ∩
            c.segmentAt (c.points.length - 2) from by
              simpa only [Set.mem_inter_iff, hwrap.1, show i = c.points.length - 2 by omega] using And.intro hzj hzi))
        have heq : c.point 0 = c.point (i + 1) := by
          rw [show i + 1 = c.points.length - 1 by omega]
          exact hc.2.1
        exact hright ((hz.trans heq) ▸ hzo)
      · exact Set.disjoint_left.mp (hc.2.2.2.2.1 j i hj hi (by omega) hwrap) hzj hzi

/-- Helper toward Proposition 5.16: an edge entering a triangle through its
interior, with neither endpoint in the triangle above its opposite side, must
cross one of the two incident sides in the open part of the edge. The basis
labels the tip by `1` and its neighbours by `0` and `2`. -/
theorem exists_incident_side_mem_openSegment (B : AffineBasis (Fin 3) ℝ ℂ)
    (p q z : ℂ)
    (hp : p ∈ convexHull ℝ (Set.range B) → B.coord 1 p ≤ 0)
    (hq : q ∈ convexHull ℝ (Set.range B) → B.coord 1 q ≤ 0)
    (hzseg : z ∈ segment ℝ p q)
    (hz : z ∈ _root_.interior (convexHull ℝ (Set.range B))) :
    ∃ y ∈ openSegment ℝ p q,
      y ∈ segment ℝ (B 0) (B 1) ∪ segment ℝ (B 1) (B 2) := by
  have hzpos : ∀ i, 0 < B.coord i z := by
    rwa [B.interior_convexHull] at hz
  have main (p q : ℂ)
      (hp : p ∈ convexHull ℝ (Set.range B) → B.coord 1 p ≤ 0)
      (hq : q ∈ convexHull ℝ (Set.range B) → B.coord 1 q ≤ 0)
      (hzseg : z ∈ segment ℝ p q) (hpβ : 0 < B.coord 1 p) :
      ∃ y ∈ openSegment ℝ p q,
        y ∈ segment ℝ (B 0) (B 1) ∪ segment ℝ (B 1) (B 2) := by
    have hpnot : p ∉ convexHull ℝ (Set.range B) := fun h => (not_lt_of_ge (hp h)) hpβ
    have hpmin : min (B.coord 0 p) (B.coord 2 p) < 0 := by
      apply lt_of_not_ge
      intro hm
      apply hpnot
      rw [B.convexHull_eq_nonneg_coord]
      intro i
      have h0 := (le_min_iff.mp hm).1
      have h2 := (le_min_iff.mp hm).2
      fin_cases i
      · exact h0
      · exact hpβ.le
      · exact h2
    have hzmin : 0 < min (B.coord 0 z) (B.coord 2 z) := lt_min (hzpos 0) (hzpos 2)
    have hf : Continuous (fun x : ℂ => min (B.coord 0 x) (B.coord 2 x)) :=
      ((B.coord 0).continuous_of_finiteDimensional).min
        ((B.coord 2).continuous_of_finiteDimensional)
    obtain ⟨y, hyseg, hyzero⟩ := (convex_segment p z).isPreconnected.intermediate_value
      (left_mem_segment ℝ p z) (right_mem_segment ℝ p z) hf.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (min (B.coord 0 p) (B.coord 2 p))
        (min (B.coord 0 z) (B.coord 2 z)) from ⟨hpmin.le, hzmin.le⟩)
    change min (B.coord 0 y) (B.coord 2 y) = 0 at hyzero
    have hyβ : 0 < B.coord 1 y :=
      ((convex_Ioi (0 : ℝ)).affine_preimage (B.coord 1)).segment_subset hpβ (hzpos 1) hyseg
    have hy0 : 0 ≤ B.coord 0 y := by
      have hm : 0 ≤ min (B.coord 0 y) (B.coord 2 y) := hyzero.ge
      exact (le_min_iff.mp hm).1
    have hy2 : 0 ≤ B.coord 2 y := by
      have hm : 0 ≤ min (B.coord 0 y) (B.coord 2 y) := hyzero.ge
      exact (le_min_iff.mp hm).2
    have hyT : y ∈ convexHull ℝ (Set.range B) := by
      rw [B.convexHull_eq_nonneg_coord]
      intro i
      fin_cases i
      · exact hy0
      · exact hyβ.le
      · exact hy2
    have hysub : y ∈ segment ℝ p q :=
      (convex_segment p q).segment_subset (left_mem_segment ℝ p q) hzseg hyseg
    have hpne : p ≠ y := by rintro rfl; exact hpnot hyT
    have hqne : q ≠ y := by rintro rfl; exact (not_lt_of_ge (hq hyT)) hyβ
    refine ⟨y, mem_openSegment_of_ne_left_right hpne hqne hysub, ?_⟩
    have hsum : B.coord 0 y + B.coord 1 y + B.coord 2 y = 1 := by
      simpa only [Fin.sum_univ_three] using B.sum_coord_apply_eq_one y
    have hrep : B.coord 0 y • B 0 + B.coord 1 y • B 1 + B.coord 2 y • B 2 = y := by
      simpa only [Fin.sum_univ_three] using B.linear_combination_coord_eq_self y
    rcases le_total (B.coord 0 y) (B.coord 2 y) with hle | hle
    · have hy0eq : B.coord 0 y = 0 := by rwa [min_eq_left hle] at hyzero
      right
      refine ⟨B.coord 1 y, B.coord 2 y, hyβ.le, hy2, ?_, ?_⟩
      · linarith only [hsum, hy0eq]
      · simpa only [hy0eq, zero_smul, zero_add] using hrep
    · have hy2eq : B.coord 2 y = 0 := by rwa [min_eq_right hle] at hyzero
      left
      refine ⟨B.coord 0 y, B.coord 1 y, hy0, hyβ.le, ?_, ?_⟩
      · linarith only [hsum, hy2eq]
      · simpa only [hy2eq, zero_smul, add_zero] using hrep
  have hend : 0 < B.coord 1 p ∨ 0 < B.coord 1 q := by
    by_contra hn
    push Not at hn
    have hznon : B.coord 1 z ≤ 0 :=
      ((convex_Iic (0 : ℝ)).affine_preimage (B.coord 1)).segment_subset hn.1 hn.2 hzseg
    exact (not_lt_of_ge hznon) (hzpos 1)
  rcases hend with hpβ | hqβ
  · exact main p q hp hq hzseg hpβ
  · simpa only [openSegment_symm] using main q p hq hp
      (by simpa only [segment_symm] using hzseg) hqβ

/-- Helper toward Proposition 5.16: if the closed neighbour triangle contains
no other polygon vertex, its interior misses the entire polygon image. -/
theorem disjoint_triangle_interior_image_of_no_other_vertex (c : Polyline)
    (hc : c.IsCyclicSimple) (i : ℕ) (hi : i + 1 < c.points.length)
    (hnc : ¬ Collinear ℝ ({c.point (if i = 0 then c.points.length - 2 else i - 1),
      c.point i, c.point (i + 1)} : Set ℂ))
    (hvertices : ∀ j, j < c.points.length →
      c.point j ∈ convexHull ℝ
        ({c.point (if i = 0 then c.points.length - 2 else i - 1), c.point i,
          c.point (i + 1)} : Set ℂ) →
      c.point j ∈ ({c.point (if i = 0 then c.points.length - 2 else i - 1),
        c.point i, c.point (i + 1)} : Set ℂ)) :
    Disjoint (_root_.interior (convexHull ℝ
      ({c.point (if i = 0 then c.points.length - 2 else i - 1), c.point i,
        c.point (i + 1)} : Set ℂ))) c.image := by
  let k := if i = 0 then c.points.length - 2 else i - 1
  let a := c.point k
  let v := c.point i
  let b := c.point (i + 1)
  have hk : k + 1 < c.points.length := by
    dsimp only [k]
    split_ifs <;> have := hc.1 <;> omega
  have hkv : c.point (k + 1) = v := by
    dsimp only [k, v]
    split_ifs with h
    · rw [show c.points.length - 2 + 1 = c.points.length - 1 by have := hc.1; omega]
      exact hc.2.1.symm.trans (congrArg c.point h.symm)
    · congr 1
      omega
  let B : AffineBasis (Fin 3) ℝ ℂ := {
    toFun := ![a, v, b]
    ind' := affineIndependent_iff_not_collinear_set.mpr hnc
    tot' := by
      have hind := affineIndependent_iff_not_collinear_set.mpr hnc
      apply hind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
      simp only [Fintype.card_fin, Module.finrank_eq_card_basis Complex.basisOneI,
        Fintype.card_fin, Nat.reduceAdd] }
  have hrange : Set.range B = ({a, v, b} : Set ℂ) := by
    change Set.range ![a, v, b] = _
    simp only [Matrix.range_cons, Matrix.range_empty, Set.singleton_union, insert_empty_eq]
  have hside : Disjoint (_root_.interior (convexHull ℝ ({a, v, b} : Set ℂ)))
      (segment ℝ a v ∪ segment ℝ v b) := by
    apply Set.disjoint_left.mpr
    intro z hz hzs
    have hf : z ∈ frontier (_root_.interior (convexHull ℝ ({a, v, b} : Set ℂ))) :=
      (frontier_triangle_interior a v b hnc).symm ▸ Or.inl hzs
    exact hf.2 (by simpa only [interior_interior] using hz)
  apply Set.disjoint_left.mpr
  intro z hz hzi
  obtain ⟨j, hj, hzj⟩ : ∃ j, j + 1 < c.points.length ∧ z ∈ c.segmentAt j := by
    rcases hzi with hroot | ⟨j, hj, hzj⟩
    · refine ⟨0, by have := hc.1; omega, ?_⟩
      rw [Set.mem_singleton_iff] at hroot
      rw [hroot, ← point_zero_eq_start c]
      exact left_mem_segment ℝ _ _
    · exact ⟨j, hj, hzj⟩
  by_cases hji : j = i
  · apply Set.disjoint_left.mp hside hz
    right
    have hh : z ∈ c.segmentAt i := hji ▸ hzj
    exact hh
  by_cases hjk : j = k
  · apply Set.disjoint_left.mp hside hz
    left
    have hh : z ∈ c.segmentAt k := hjk ▸ hzj
    simpa only [segmentAt, hkv] using hh
  have hvnot : v ∉ c.segmentAt j := by
    apply not_mem_segmentAt_of_ne_vertex_cyclic c hc i j hi hj hji
    · intro heq
      apply hjk
      dsimp only [k]
      split_ifs <;> omega
    · intro hw
      apply hjk
      dsimp only [k]
      rw [ite_eq_left hw.1]
      omega
  have hcoord (m : ℕ) (hm : m < c.points.length) (hmem : c.point m ∈ c.segmentAt j)
      (hT : c.point m ∈ convexHull ℝ (Set.range B)) : B.coord 1 (c.point m) ≤ 0 := by
    have hcases := hvertices m hm (by simpa only [hrange] using hT)
    change c.point m ∈ ({a, v, b} : Set ℂ) at hcases
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcases
    rcases hcases with heq | heq | heq
    · rw [heq]
      change B.coord 1 (B 0) ≤ 0
      rw [B.coord_apply_ne (by decide : (1 : Fin 3) ≠ 0)]
    · exact False.elim (hvnot (heq ▸ hmem))
    · rw [heq]
      change B.coord 1 (B 2) ≤ 0
      rw [B.coord_apply_ne (by decide : (1 : Fin 3) ≠ 2)]
  obtain ⟨y, hyopen, hysides⟩ := exists_incident_side_mem_openSegment B
    (c.point j) (c.point (j + 1)) z
    (hcoord j (by omega) (left_mem_segment ℝ _ _))
    (hcoord (j + 1) hj (right_mem_segment ℝ _ _)) hzj
    (by simpa only [hrange] using hz)
  change y ∈ segment ℝ a v ∪ segment ℝ v b at hysides
  rcases hysides with hyav | hyvb
  · have hyk : y ∈ c.segmentAt k := by simpa only [segmentAt, hkv] using hyav
    exact Set.disjoint_left.mp (disjoint_openSegment_segmentAt_cyclic c hc j k hj hk hjk)
      hyopen hyk
  · exact Set.disjoint_left.mp (disjoint_openSegment_segmentAt_cyclic c hc j i hj hi hji)
      hyopen hyvb

/-- Helper toward Proposition 5.16: at a left supporting vertex, absence of
other vertices from the closed neighbour triangle puts its whole interior
inside the polygon, rather than just the local sector. -/
theorem triangle_interior_subset_inside_of_no_other_vertex (c : Polyline)
    (hc : c.IsCyclicSimple) (i : ℕ) (hi : i + 1 < c.points.length)
    (hbound : ∀ j, j < c.points.length → (c.point i).re ≤ (c.point j).re)
    (hnc : ¬ Collinear ℝ ({c.point (if i = 0 then c.points.length - 2 else i - 1),
      c.point i, c.point (i + 1)} : Set ℂ))
    (hvertices : ∀ j, j < c.points.length →
      c.point j ∈ convexHull ℝ
        ({c.point (if i = 0 then c.points.length - 2 else i - 1), c.point i,
          c.point (i + 1)} : Set ℂ) →
      c.point j ∈ ({c.point (if i = 0 then c.points.length - 2 else i - 1),
        c.point i, c.point (i + 1)} : Set ℂ)) :
    _root_.interior (convexHull ℝ
      ({c.point (if i = 0 then c.points.length - 2 else i - 1), c.point i,
        c.point (i + 1)} : Set ℂ)) ⊆ c.inside := by
  let k := if i = 0 then c.points.length - 2 else i - 1
  have hk : k + 1 < c.points.length := by
    dsimp only [k]
    split_ifs <;> have := hc.1 <;> omega
  have hkv : c.point (k + 1) = c.point i := by
    dsimp only [k]
    split_ifs with h
    · rw [show c.points.length - 2 + 1 = c.points.length - 1 by have := hc.1; omega]
      exact hc.2.1.symm.trans (congrArg c.point h.symm)
    · congr 1
      omega
  have hclosed : c.start = c.finish := by
    rw [← point_zero_eq_start c, ← point_last_eq_finish c]
    exact hc.2.1
  obtain ⟨r, hr, hlocal⟩ := exists_pos_ball_image_eq_incident_segments_cyclic c hc i hi
  have hlocal' : ∀ z ∈ Metric.ball (c.point i) r,
      z ∈ c.image ↔ z ∈ segment ℝ (c.point i) (c.point k) ∪
        segment ℝ (c.point i) (c.point (i + 1)) := by
    intro z hz
    have hh := hlocal z hz
    change z ∈ c.image ↔ z ∈ c.segmentAt k ∪ c.segmentAt i at hh
    simpa only [segmentAt, hkv, segment_symm ℝ (c.point k) (c.point i)] using hh
  have hsector := triangle_sector_subset_inside_of_support c hc _ _ _
    (c.point_mem_image (by omega)) r hr hnc (hbound k (by omega)) (hbound (i + 1) hi)
    (fun z hz => re_le_of_mem_image c _ hbound hz) hlocal'
  have hvcl : c.point i ∈ closure (_root_.interior
      (convexHull ℝ ({c.point k, c.point i, c.point (i + 1)} : Set ℂ))) := by
    rw [closure_triangle_interior _ _ _ hnc]
    exact subset_convexHull ℝ _ (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true])
  obtain ⟨z, hz, hd⟩ := Metric.mem_closure_iff.mp hvcl r hr
  have hzinside : z ∈ c.inside := hsector ⟨by
    simpa only [Metric.mem_ball, dist_comm] using hd, hz⟩
  have hdisj := disjoint_triangle_interior_image_of_no_other_vertex c hc i hi hnc hvertices
  rcases subset_inside_or_outside_of_isPreconnected c hclosed _
      (convex_convexHull ℝ _).interior.isPreconnected
      (fun _ hx => Set.disjoint_left.mp hdisj hx) with hin | hout
  · exact hin
  · exact False.elim (hzinside.2 (hout hz).2)

/-- Helper toward Proposition 5.16: a segment touching the open opposite
side of a triangle, while missing its interior, lies on that side's supporting
line. The strict open-segment condition excludes endpoint-only contacts. -/
theorem coord_eq_zero_of_disjoint_triangle_interior (B : AffineBasis (Fin 3) ℝ ℂ)
    (p q z : ℂ) (hz : z ∈ openSegment ℝ p q)
    (hz0 : 0 < B.coord 0 z) (hz2 : 0 < B.coord 2 z) (hz1 : B.coord 1 z = 0)
    (havoid : Disjoint (segment ℝ p q)
      (_root_.interior (convexHull ℝ (Set.range B)))) :
    B.coord 1 p = 0 ∧ B.coord 1 q = 0 := by
  have hzseg : z ∈ segment ℝ p q := openSegment_subset_segment ℝ _ _ hz
  have hn (x : ℂ) (hx : x ∈ segment ℝ p q) : B.coord 1 x ≤ 0 := by
    apply le_of_not_gt
    intro hx1
    let O : Set ℂ := {y | 0 < B.coord 0 y ∧ 0 < B.coord 2 y}
    have hO : IsOpen O :=
      (isOpen_lt continuous_const (B.coord 0).continuous_of_finiteDimensional).inter
        (isOpen_lt continuous_const (B.coord 2).continuous_of_finiteDimensional)
    have hzcl : z ∈ closure (openSegment ℝ z x) :=
      segment_subset_closure_openSegment (left_mem_segment ℝ z x)
    obtain ⟨y, hyO, hyseg⟩ := mem_closure_iff.mp hzcl O hO ⟨hz0, hz2⟩
    have hy1 : 0 < B.coord 1 y := by
      obtain ⟨s, t, hs, ht, hst, rfl⟩ := hyseg
      rw [Convex.combo_affine_apply hst, hz1, smul_zero, zero_add]
      exact mul_pos ht hx1
    have hyT : y ∈ _root_.interior (convexHull ℝ (Set.range B)) := by
      rw [B.interior_convexHull]
      intro i
      fin_cases i
      · exact hyO.1
      · exact hy1
      · exact hyO.2
    have hyedge : y ∈ segment ℝ p q :=
      (convex_segment p q).segment_subset hzseg hx
        (openSegment_subset_segment ℝ _ _ hyseg)
    exact Set.disjoint_left.mp havoid hyedge hyT
  have hp := hn p (left_mem_segment ℝ p q)
  have hq := hn q (right_mem_segment ℝ p q)
  obtain ⟨s, t, hs, ht, hst, heq⟩ := hz
  have hcomb : s * B.coord 1 p + t * B.coord 1 q = 0 := by
    rw [← hz1, ← heq, Convex.combo_affine_apply hst]
    rfl
  have hsp : s * B.coord 1 p ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs.le hp
  have htq : t * B.coord 1 q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le hq
  have hsp0 : s * B.coord 1 p = 0 := by linarith only [hcomb, hsp, htq]
  have htq0 : t * B.coord 1 q = 0 := by linarith only [hcomb, hsp, htq]
  exact ⟨(mul_eq_zero.mp hsp0).resolve_left hs.ne',
    (mul_eq_zero.mp htq0).resolve_left ht.ne'⟩

/-- Helper toward Proposition 5.16: an edge touching the open opposite side,
missing the triangle interior, and having no endpoint in the open side must
contain both opposite-side vertices. -/
theorem base_vertices_mem_segment_of_contact (B : AffineBasis (Fin 3) ℝ ℂ)
    (p q z : ℂ) (hz : z ∈ openSegment ℝ p q)
    (hz0 : 0 < B.coord 0 z) (hz2 : 0 < B.coord 2 z) (hz1 : B.coord 1 z = 0)
    (hp : p ∈ convexHull ℝ (Set.range B) → p ∈ ({B 0, B 1, B 2} : Set ℂ))
    (hq : q ∈ convexHull ℝ (Set.range B) → q ∈ ({B 0, B 1, B 2} : Set ℂ))
    (havoid : Disjoint (segment ℝ p q)
      (_root_.interior (convexHull ℝ (Set.range B)))) :
    B 0 ∈ segment ℝ p q ∧ B 2 ∈ segment ℝ p q := by
  obtain ⟨hp1, hq1⟩ := coord_eq_zero_of_disjoint_triangle_interior B p q z hz hz0 hz2 hz1 havoid
  have hs (x : ℂ) : B.coord 0 x + B.coord 1 x + B.coord 2 x = 1 := by
    simpa only [Fin.sum_univ_three] using B.sum_coord_apply_eq_one x
  have hout (x : ℂ) (hx1 : B.coord 1 x = 0)
      (hx : x ∈ convexHull ℝ (Set.range B) → x ∈ ({B 0, B 1, B 2} : Set ℂ)) :
      B.coord 0 x ≤ 0 ∨ 1 ≤ B.coord 0 x := by
    by_contra hn
    push Not at hn
    have hxT : x ∈ convexHull ℝ (Set.range B) := by
      rw [B.convexHull_eq_nonneg_coord]
      intro i
      have hsum := hs x
      fin_cases i
      · exact hn.1.le
      · exact hx1.ge
      · change 0 ≤ B.coord 2 x
        linarith only [hsum, hx1, hn.2]
    have hcase := hx hxT
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcase
    rcases hcase with rfl | rfl | rfl
    · have h0 := B.coord_apply_eq (0 : Fin 3)
      exact (not_le_of_gt hn.2) h0.ge
    · have h0 := B.coord_apply_ne (show (0 : Fin 3) ≠ 1 by decide)
      exact (ne_of_gt hn.1) h0
    · have h0 := B.coord_apply_ne (show (0 : Fin 3) ≠ 2 by decide)
      exact (ne_of_gt hn.1) h0
  have hpout := hout p hp1 hp
  have hqout := hout q hq1 hq
  have hzlt : B.coord 0 z < 1 := by
    have hsum := hs z
    linarith only [hsum, hz1, hz2]
  have hcase : (B.coord 0 p ≤ 0 ∧ 1 ≤ B.coord 0 q) ∨
      (B.coord 0 q ≤ 0 ∧ 1 ≤ B.coord 0 p) := by
    rcases hpout with hp0 | hp0 <;> rcases hqout with hq0 | hq0
    · have hn : B.coord 0 z ≤ 0 :=
        ((convex_Iic (0 : ℝ)).affine_preimage (B.coord 0)).segment_subset hp0 hq0
          (openSegment_subset_segment ℝ _ _ hz)
      exact False.elim ((not_lt_of_ge hn) hz0)
    · exact Or.inl ⟨hp0, hq0⟩
    · exact Or.inr ⟨hq0, hp0⟩
    · have hn : 1 ≤ B.coord 0 z :=
        ((convex_Ici (1 : ℝ)).affine_preimage (B.coord 0)).segment_subset hp0 hq0
          (openSegment_subset_segment ℝ _ _ hz)
      exact False.elim ((not_lt_of_ge hn) hzlt)
  have hzero (y : ℂ) (hy : y ∈ segment ℝ p q) : B.coord 1 y = 0 := by
    obtain ⟨s, t, _, _, hst, rfl⟩ := hy
    rw [Convex.combo_affine_apply hst, hp1, hq1, smul_zero, smul_zero, add_zero]
  have hmem (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
      ∃ y ∈ segment ℝ p q, B.coord 0 y = t := by
    rcases hcase with hcase | hcase
    · exact (convex_segment p q).isPreconnected.intermediate_value
        (left_mem_segment ℝ p q) (right_mem_segment ℝ p q)
        (B.coord 0).continuous_of_finiteDimensional.continuousOn
        ⟨hcase.1.trans ht.1, ht.2.trans hcase.2⟩
    · exact (convex_segment p q).isPreconnected.intermediate_value
        (right_mem_segment ℝ p q) (left_mem_segment ℝ p q)
        (B.coord 0).continuous_of_finiteDimensional.continuousOn
        ⟨hcase.1.trans ht.1, ht.2.trans hcase.2⟩
  obtain ⟨y, hy, hy0⟩ := hmem 1 ⟨by norm_num, le_rfl⟩
  obtain ⟨w, hw, hw0⟩ := hmem 0 ⟨le_rfl, by norm_num⟩
  have hyB : y = B 0 := by
    apply B.ext_elem
    intro i
    have hy1 := hzero y hy
    have hsum := hs y
    fin_cases i
    · change B.coord 0 y = B.coord 0 (B 0)
      simpa only [B.coord_apply_eq] using hy0
    · change B.coord 1 y = B.coord 1 (B 0)
      simpa only [B.coord_apply_ne (by decide : (1 : Fin 3) ≠ 0)] using hy1
    · change B.coord 2 y = B.coord 2 (B 0)
      rw [B.coord_apply_ne (by decide : (2 : Fin 3) ≠ 0)]
      linarith only [hsum, hy0, hy1]
  have hwB : w = B 2 := by
    apply B.ext_elem
    intro i
    have hw1 := hzero w hw
    have hsum := hs w
    fin_cases i
    · change B.coord 0 w = B.coord 0 (B 2)
      simpa only [B.coord_apply_ne (by decide : (0 : Fin 3) ≠ 2)] using hw0
    · change B.coord 1 w = B.coord 1 (B 2)
      simpa only [B.coord_apply_ne (by decide : (1 : Fin 3) ≠ 2)] using hw1
    · change B.coord 2 w = B.coord 2 (B 2)
      rw [B.coord_apply_eq]
      linarith only [hsum, hw0, hw1]
  exact ⟨hyB ▸ hy, hwB ▸ hw⟩

/-- Helper toward Proposition 5.16: in a polygon with at least four distinct
cyclic vertices, no single edge contains both neighbours of a vertex. -/
theorem not_neighbors_mem_same_segmentAt_cyclic (c : Polyline) (hc : c.IsCyclicSimple)
    (hlen : 5 ≤ c.points.length) (i j : ℕ)
    (hi : i + 1 < c.points.length) (hj : j + 1 < c.points.length) :
    ¬ (c.point (if i = 0 then c.points.length - 2 else i - 1) ∈ c.segmentAt j ∧
      c.point (i + 1) ∈ c.segmentAt j) := by
  intro hboth
  have hinc (m : ℕ) (hm : m + 1 < c.points.length) (hmem : c.point m ∈ c.segmentAt j) :
      j = m ∨ j + 1 = m ∨ m = 0 ∧ j + 2 = c.points.length := by
    by_contra hn
    push Not at hn
    exact not_mem_segmentAt_of_ne_vertex_cyclic c hc m j hm hj hn.1 hn.2.1
      (fun h => hn.2.2 h.1 h.2) hmem
  by_cases hi0 : i = 0
  · subst i
    simp only [ite_true] at hboth
    have hu := hinc (c.points.length - 2) (by omega) hboth.1
    have hw := hinc 1 (by omega) hboth.2
    omega
  · simp only [ite_eq_right hi0] at hboth
    have hu := hinc (i - 1) (by omega) hboth.1
    by_cases hn : i + 2 < c.points.length
    · have hw := hinc (i + 1) hn hboth.2
      omega
    · have heq : c.point (i + 1) = c.point 0 := by
        rw [show i + 1 = c.points.length - 1 by omega]
        exact hc.2.1.symm
      have hw := hinc 0 (by omega) (heq ▸ hboth.2)
      omega

/-- Helper toward Proposition 5.16: an empty closed neighbour triangle in a
polygon with at least four cyclic vertices has an opposite open side avoiding
the polygon image. -/
theorem disjoint_openSegment_neighbors_image_of_no_other_vertex (c : Polyline)
    (hc : c.IsCyclicSimple) (hlen : 5 ≤ c.points.length)
    (i : ℕ) (hi : i + 1 < c.points.length)
    (hnc : ¬ Collinear ℝ ({c.point (if i = 0 then c.points.length - 2 else i - 1),
      c.point i, c.point (i + 1)} : Set ℂ))
    (hvertices : ∀ j, j < c.points.length →
      c.point j ∈ convexHull ℝ
        ({c.point (if i = 0 then c.points.length - 2 else i - 1), c.point i,
          c.point (i + 1)} : Set ℂ) →
      c.point j ∈ ({c.point (if i = 0 then c.points.length - 2 else i - 1),
        c.point i, c.point (i + 1)} : Set ℂ)) :
    Disjoint (openSegment ℝ
      (c.point (if i = 0 then c.points.length - 2 else i - 1)) (c.point (i + 1))) c.image := by
  let a := c.point (if i = 0 then c.points.length - 2 else i - 1)
  let v := c.point i
  let b := c.point (i + 1)
  let B : AffineBasis (Fin 3) ℝ ℂ := {
    toFun := ![a, v, b]
    ind' := affineIndependent_iff_not_collinear_set.mpr hnc
    tot' := by
      have hind := affineIndependent_iff_not_collinear_set.mpr hnc
      apply hind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
      simp only [Fintype.card_fin, Module.finrank_eq_card_basis Complex.basisOneI,
        Fintype.card_fin, Nat.reduceAdd] }
  have hrange : Set.range B = ({a, v, b} : Set ℂ) := by
    change Set.range ![a, v, b] = _
    simp only [Matrix.range_cons, Matrix.range_empty, Set.singleton_union, insert_empty_eq]
  have hdisj := disjoint_triangle_interior_image_of_no_other_vertex c hc i hi hnc hvertices
  apply Set.disjoint_left.mpr
  intro z hz hzi
  change z ∈ openSegment ℝ (B 0) (B 2) at hz
  have hzcoords : 0 < B.coord 0 z ∧ B.coord 1 z = 0 ∧ 0 < B.coord 2 z := by
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
    simp only [Convex.combo_affine_apply hst, B.coord_apply_eq,
      B.coord_apply_ne (by decide : (0 : Fin 3) ≠ 2),
      B.coord_apply_ne (by decide : (1 : Fin 3) ≠ 0),
      B.coord_apply_ne (by decide : (1 : Fin 3) ≠ 2),
      B.coord_apply_ne (by decide : (2 : Fin 3) ≠ 0),
      smul_eq_mul, mul_zero, mul_one, zero_add, add_zero]
    exact ⟨hs, trivial, ht⟩
  have hzT : z ∈ convexHull ℝ (Set.range B) :=
    segment_subset_convexHull (Set.mem_range_self 0) (Set.mem_range_self 2)
      (openSegment_subset_segment ℝ _ _ hz)
  have hznot : z ∉ ({B 0, B 1, B 2} : Set ℂ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl | rfl)
    · have h0 := B.coord_apply_ne (by decide : (2 : Fin 3) ≠ 0)
      exact (ne_of_gt hzcoords.2.2) h0
    · have h1 := B.coord_apply_eq (1 : Fin 3)
      exact zero_ne_one (hzcoords.2.1.symm.trans h1)
    · have h0 := B.coord_apply_ne (by decide : (0 : Fin 3) ≠ 2)
      exact (ne_of_gt hzcoords.1) h0
  have hnotvertex (m : ℕ) (hm : m < c.points.length) : c.point m ≠ z := by
    intro heq
    apply hznot
    have hcases := hvertices m hm (by simpa only [heq, hrange] using hzT)
    exact heq ▸ hcases
  obtain ⟨j, hj, hzj⟩ : ∃ j, j + 1 < c.points.length ∧ z ∈ c.segmentAt j := by
    rcases hzi with hroot | ⟨j, hj, hzj⟩
    · exact False.elim (hnotvertex 0 (by omega)
        ((point_zero_eq_start c).trans (Set.mem_singleton_iff.mp hroot).symm))
    · exact ⟨j, hj, hzj⟩
  have hzopen : z ∈ openSegment ℝ (c.point j) (c.point (j + 1)) :=
    mem_openSegment_of_ne_left_right (hnotvertex j (by omega))
      (hnotvertex (j + 1) hj) hzj
  have hav : Disjoint (segment ℝ (c.point j) (c.point (j + 1)))
      (_root_.interior (convexHull ℝ (Set.range B))) := by
    apply Set.disjoint_left.mpr
    intro x hx hxT
    apply Set.disjoint_left.mp hdisj
      (by simpa only [hrange] using hxT) (c.segmentAt_subset_image hj hx)
  have hvert (m : ℕ) (hm : m < c.points.length)
      (hT : c.point m ∈ convexHull ℝ (Set.range B)) :
      c.point m ∈ ({B 0, B 1, B 2} : Set ℂ) :=
    hvertices m hm (by simpa only [hrange] using hT)
  have hboth := base_vertices_mem_segment_of_contact B _ _ z hzopen
    hzcoords.1 hzcoords.2.2 hzcoords.2.1 (hvert j (by omega)) (hvert (j + 1) hj) hav
  exact not_neighbors_mem_same_segmentAt_cyclic c hc hlen i j hi hj hboth

/-- Helper toward Proposition 5.16: the empty closed neighbour triangle at
a left supporting vertex is an ear. Its opposite open side is inside, and its
closed side meets the polygon image exactly at its two endpoints. The length
bound excludes the three-vertex polygon, whose opposite side is a boundary edge. -/
theorem ear_of_no_other_vertex (c : Polyline) (hc : c.IsCyclicSimple)
    (hlen : 5 ≤ c.points.length) (i : ℕ) (hi : i + 1 < c.points.length)
    (hbound : ∀ j, j < c.points.length → (c.point i).re ≤ (c.point j).re)
    (hnc : ¬ Collinear ℝ ({c.point (if i = 0 then c.points.length - 2 else i - 1),
      c.point i, c.point (i + 1)} : Set ℂ))
    (hvertices : ∀ j, j < c.points.length →
      c.point j ∈ convexHull ℝ
        ({c.point (if i = 0 then c.points.length - 2 else i - 1), c.point i,
          c.point (i + 1)} : Set ℂ) →
      c.point j ∈ ({c.point (if i = 0 then c.points.length - 2 else i - 1),
        c.point i, c.point (i + 1)} : Set ℂ)) :
    let u := c.point (if i = 0 then c.points.length - 2 else i - 1)
    let w := c.point (i + 1)
    openSegment ℝ u w ⊆ c.inside ∧ segment ℝ u w ∩ c.image = {u, w} := by
  let k := if i = 0 then c.points.length - 2 else i - 1
  let u := c.point k
  let v := c.point i
  let w := c.point (i + 1)
  have hk : k < c.points.length := by
    dsimp only [k]
    split_ifs <;> omega
  have hTin := triangle_interior_subset_inside_of_no_other_vertex c hc i hi hbound hnc hvertices
  have havoid := disjoint_openSegment_neighbors_image_of_no_other_vertex c hc hlen i hi hnc hvertices
  change openSegment ℝ u w ⊆ c.inside ∧ segment ℝ u w ∩ c.image = {u, w}
  constructor
  · intro z hz
    have hzT : z ∈ convexHull ℝ ({u, v, w} : Set ℂ) :=
      segment_subset_convexHull (by simp only [Set.mem_insert_iff, true_or])
        (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true])
        (openSegment_subset_segment ℝ _ _ hz)
    have hzclT : z ∈ closure (_root_.interior (convexHull ℝ ({u, v, w} : Set ℂ))) :=
      (closure_triangle_interior u v w hnc).symm ▸ hzT
    have hzcl : z ∈ closure c.inside := closure_mono hTin hzclT
    by_contra hzin
    have hfront : z ∈ frontier c.inside :=
      ⟨hzcl, fun hzint => hzin (interior_subset hzint)⟩
    have hzimage : z ∈ c.image := (frontier_inside_outside_eq_image_cyclic c hc).1 ▸ hfront
    exact Set.disjoint_left.mp havoid hz hzimage
  · ext z
    constructor
    · rintro ⟨hzseg, hzimage⟩
      by_cases hzu : z = u
      · exact Or.inl hzu
      by_cases hzw : z = w
      · exact Or.inr hzw
      exact False.elim (Set.disjoint_left.mp havoid
        (mem_openSegment_of_ne_left_right (Ne.symm hzu) (Ne.symm hzw) hzseg) hzimage)
    · rintro (rfl | rfl)
      · exact ⟨left_mem_segment ℝ _ _, c.point_mem_image hk⟩
      · exact ⟨right_mem_segment ℝ _ _, c.point_mem_image hi⟩

















































end Polyline
end DirectedDistances.PlanarMap

