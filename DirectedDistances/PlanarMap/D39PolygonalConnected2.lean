/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PolygonalConnected
public import DirectedDistances.PlanarMap.D39PolygonalSeparation7

/-! # Local component propagation at polygon vertices

Helpers toward Proposition 5.16. Local vertex regions give unordered component
propagation, exactly two complementary components, connected winding sides,
and their common frontier. The final theorem discharges the endpoint-glued
polygonal separation obligation; it does not assert Proposition 5.16. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
namespace Polyline

open Topology
/-- Helper toward Proposition 5.16: the transverse coordinate is alternating. -/
theorem transverse_swap (d e : ℂ) :
    (star d * e).im = -(star e * d).im := by
  simp only [Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Helper toward Proposition 5.16: transverse coordinates of a segment
from its initial vertex are nonnegative when that of its endpoint is. -/
theorem transverse_nonneg_segment (v a d z : ℂ)
    (ha : 0 ≤ (star d * (a - v)).im) (hz : z ∈ segment ℝ v a) :
    0 ≤ (star d * (z - v)).im := by
  rw [segment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  simp only [add_sub_cancel_left, RCLike.real_smul_eq_coe_mul]
  have heq : (star d * ((t : ℂ) * (a - v))).im =
      t * (star d * (a - v)).im := by
    rw [show star d * ((t : ℂ) * (a - v)) =
      (t : ℂ) * (star d * (a - v)) by ring]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  exact heq.symm ▸ mul_nonneg ht.1 ha

/-- Helper toward Proposition 5.16: the complement of a nondegenerate
supporting line is dense. -/
theorem dense_compl_edgeLine (v d : ℂ) (hd : d ≠ 0) :
    Dense (edgeLine v d)ᶜ := by
  apply dense_iff_inter_open.mpr
  intro O hO hOne
  obtain ⟨x, hx⟩ := hOne
  by_cases hline : x ∈ edgeLine v d
  · obtain ⟨y, hyO, hy⟩ := mem_closure_iff.mp
      (mem_closure_leftHalfDisc x d 1 hd (by norm_num)) O hO hx
    refine ⟨y, hyO, ?_⟩
    intro hyline
    have heq : (star d * (y - x)).im = 0 := by
      have halg : star d * (y - x) = star d * (y - v) - star d * (x - v) := by ring
      rw [halg, Complex.sub_im, hyline, hline, sub_self]
    exact (ne_of_gt hy.2) heq
  · exact ⟨x, hx, hline⟩

/-- Helper toward Proposition 5.16: every nonempty open set contains a
point away from either of two nondegenerate supporting lines. -/
theorem exists_mem_open_off_two_edgeLines (O : Set ℂ) (hO : IsOpen O)
    (hOne : O.Nonempty) (v d e : ℂ) (hd : d ≠ 0) (he : e ≠ 0) :
    ∃ z ∈ O, z ∉ edgeLine v d ∧ z ∉ edgeLine v e := by
  have hopen : IsOpen (edgeLine v d)ᶜ := by
    have hcont : Continuous (fun z : ℂ => (star d * (z - v)).im) := by fun_prop
    exact (isClosed_eq hcont continuous_const).isOpen_compl
  obtain ⟨z, hzO, hzd⟩ := (dense_compl_edgeLine v d hd).inter_open_nonempty O hO hOne
  obtain ⟨w, ⟨hwO, hwd⟩, hwe⟩ := (dense_compl_edgeLine v e he).inter_open_nonempty
    (O ∩ (edgeLine v d)ᶜ) (hO.inter hopen) ⟨z, hzO, hzd⟩
  exact ⟨w, hwO, hwd, hwe⟩


/-- Helper toward Proposition 5.16: transverse coordinates commute with real scaling. -/
theorem transverse_smul (d z : ℂ) (t : ℝ) :
    (star d * (t • z)).im = t * (star d * z).im := by
  rw [mul_smul_comm, Complex.smul_im, smul_eq_mul]
/-- Helper toward Proposition 5.16: a positive angle between two rays gives
nonempty opposite sectors in every positive-radius vertex ball. -/
theorem halfDisc_sector_intersections_nonempty (v u e : ℂ) (r : ℝ)
    (hr : 0 < r) (hcross : 0 < (star u * e).im) :
    (leftHalfDisc v u r ∩ rightHalfDisc v e r).Nonempty ∧
      (rightHalfDisc v u r ∩ leftHalfDisc v e r).Nonempty := by
  obtain ⟨t, ht, htr⟩ := exists_pos_mul_lt hr ‖u + e‖
  have hnorm : ‖t • (u + e)‖ < r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_comm]
    exact htr
  have hu : (star u * (u + e)).im = (star u * e).im := by
    rw [mul_add, Complex.add_im]
    have hzero : (star u * u).im = 0 := by
      have h := transverse_swap u u
      linarith
    rw [hzero, zero_add]
  have he : (star e * (u + e)).im = -(star u * e).im := by
    rw [mul_add, Complex.add_im, transverse_swap e u]
    have hzero : (star e * e).im = 0 := by
      have h := transverse_swap e e
      linarith
    rw [hzero, add_zero]
  constructor
  · refine ⟨v + t • (u + e), ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using hnorm
    · change 0 < (star u * (v + t • (u + e) - v)).im
      rw [add_sub_cancel_left, transverse_smul, hu]
      exact mul_pos ht hcross
    · simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using hnorm
    · change (star e * (v + t • (u + e) - v)).im < 0
      rw [add_sub_cancel_left, transverse_smul, he]
      exact mul_neg_of_pos_of_neg ht (neg_neg_of_pos hcross)
  · refine ⟨v - t • (u + e), ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simpa only [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg] using hnorm
    · change (star u * (v - t • (u + e) - v)).im < 0
      rw [sub_sub_cancel_left, mul_neg, Complex.neg_im, transverse_smul, hu]
      exact neg_neg_of_pos (mul_pos ht hcross)
    · simpa only [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg] using hnorm
    · change 0 < (star e * (v - t • (u + e) - v)).im
      rw [sub_sub_cancel_left, mul_neg, Complex.neg_im, transverse_smul, he, mul_neg,
        neg_neg]
      exact mul_pos ht hcross

/-- Helper toward Proposition 5.16: two positively ordered rays have two
connected vertex regions, disjoint from both incident segments, which cover
every point of the ball away from their supporting lines. -/
theorem exists_connected_vertex_regions_of_cross_pos (v a b : ℂ) (r : ℝ)
    (hr : 0 < r) (hcross : 0 < (star (a - v) * (b - v)).im) :
    ∃ L R : Set ℂ, IsConnected L ∧ IsConnected R ∧
      L ⊆ (segment ℝ v a ∪ segment ℝ v b)ᶜ ∧
      R ⊆ (segment ℝ v a ∪ segment ℝ v b)ᶜ ∧
      L ⊆ Metric.ball v r ∧ R ⊆ Metric.ball v r ∧
      ∀ z ∈ Metric.ball v r,
        z ∉ edgeLine v (a - v) → z ∉ edgeLine v (b - v) → z ∈ L ∪ R := by
  let u := a - v
  let e := b - v
  let L := leftHalfDisc v u r ∩ rightHalfDisc v e r
  let R := rightHalfDisc v u r ∪ leftHalfDisc v e r
  obtain ⟨hLne, hRinter⟩ := halfDisc_sector_intersections_nonempty v u e r hr hcross
  have hLconn : IsConnected L :=
    ((convex_leftHalfDisc v u r).inter (convex_rightHalfDisc v e r)).isConnected hLne
  have hRconn : IsConnected R :=
    (isConnected_rightHalfDisc v u r (hRinter.mono Set.inter_subset_left)).union hRinter
      (isConnected_leftHalfDisc v e r (hRinter.mono Set.inter_subset_right))
  have haLine : segment ℝ v a ⊆ edgeLine v u :=
    segment_subset_edgeLine v a v (left_mem_segment ℝ v a)
  have hbLine : segment ℝ v b ⊆ edgeLine v e :=
    segment_subset_edgeLine v b v (left_mem_segment ℝ v b)
  have hcross' : (star e * (a - v)).im ≤ 0 := by
    rw [transverse_swap]
    exact (neg_neg_of_pos hcross).le
  refine ⟨L, R, hLconn, hRconn, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz hzseg
    rcases hzseg with hza | hzb
    · exact (ne_of_gt hz.1.2) (haLine hza)
    · exact (ne_of_lt hz.2.2) (hbLine hzb)
  · intro z hz hzseg
    rcases hz with hzu | hze
    · rcases hzseg with hza | hzb
      · exact (ne_of_lt hzu.2) (haLine hza)
      · exact (not_lt_of_ge (transverse_nonneg_segment v b u z hcross.le hzb)) hzu.2
    · rcases hzseg with hza | hzb
      · have hnonneg := transverse_nonneg_segment v a (-e) z (by
          simpa only [star_neg, neg_mul, Complex.neg_im, neg_nonneg] using hcross') hza
        have hnonpos : (star e * (z - v)).im ≤ 0 := by
          simpa only [star_neg, neg_mul, Complex.neg_im, neg_nonneg] using hnonneg
        exact (not_lt_of_ge hnonpos) hze.2
      · exact (ne_of_gt hze.2) (hbLine hzb)
  · intro z hz
    exact hz.1.1
  · rintro z (hz | hz)
    · exact hz.1
    · exact hz.1
  · intro z hz hzu hze
    have hu0 : (star u * (z - v)).im ≠ 0 := hzu
    have he0 : (star e * (z - v)).im ≠ 0 := hze
    rcases hu0.lt_or_gt with hu | hu
    · exact Or.inr (Or.inl ⟨hz, hu⟩)
    · rcases he0.lt_or_gt with he | he
      · exact Or.inl ⟨⟨hz, hu⟩, ⟨hz, he⟩⟩
      · exact Or.inr (Or.inr ⟨hz, he⟩)

/-- Helper toward Proposition 5.16: a segment with zero endpoint transverse
coordinate lies on the supporting line through its initial vertex. -/
theorem segment_subset_edgeLine_of_transverse_zero (v a d : ℂ)
    (ha : (star d * (a - v)).im = 0) :
    segment ℝ v a ⊆ edgeLine v d := by
  intro z hz
  have hp := transverse_nonneg_segment v a d z ha.ge hz
  have hn := transverse_nonneg_segment v a (-d) z (by
    simp only [star_neg, neg_mul, Complex.neg_im, ha, neg_zero, le_refl]) hz
  have hn' : (star d * (z - v)).im ≤ 0 := by
    simpa only [star_neg, neg_mul, Complex.neg_im, neg_nonneg] using hn
  exact le_antisymm hn' hp

/-- Helper toward Proposition 5.16: all configurations of two nondegenerate
incident segments, including collinear ones, admit two connected regions
covering the vertex ball away from their supporting lines. -/
theorem exists_connected_vertex_regions (v a b : ℂ) (r : ℝ)
    (ha : a ≠ v) (_hb : b ≠ v) (hr : 0 < r) :
    ∃ L R : Set ℂ, IsConnected L ∧ IsConnected R ∧
      L ⊆ (segment ℝ v a ∪ segment ℝ v b)ᶜ ∧
      R ⊆ (segment ℝ v a ∪ segment ℝ v b)ᶜ ∧
      L ⊆ Metric.ball v r ∧ R ⊆ Metric.ball v r ∧
      ∀ z ∈ Metric.ball v r,
        z ∉ edgeLine v (a - v) → z ∉ edgeLine v (b - v) → z ∈ L ∪ R := by
  rcases lt_trichotomy 0 (star (a - v) * (b - v)).im with hp | heq | hn
  · exact exists_connected_vertex_regions_of_cross_pos v a b r hr hp
  · have hzero : (star (a - v) * (b - v)).im = 0 := heq.symm
    have hself : (star (a - v) * (a - v)).im = 0 := by
      have h := transverse_swap (a - v) (a - v)
      linarith
    have hline : segment ℝ v a ∪ segment ℝ v b ⊆ edgeLine v (a - v) :=
      Set.union_subset
        (segment_subset_edgeLine_of_transverse_zero v a (a - v) hself)
        (segment_subset_edgeLine_of_transverse_zero v b (a - v) hzero)
    have hd : a - v ≠ 0 := sub_ne_zero.mpr ha
    refine ⟨leftHalfDisc v (a - v) r, rightHalfDisc v (a - v) r,
      isConnected_leftHalfDisc _ _ _ (leftHalfDisc_nonempty _ _ _ hd hr),
      isConnected_rightHalfDisc _ _ _ (rightHalfDisc_nonempty _ _ _ hd hr),
      ?_, ?_, Set.inter_subset_left, Set.inter_subset_left, ?_⟩
    · intro z hz hzseg
      exact (ne_of_gt hz.2) (hline hzseg)
    · intro z hz hzseg
      exact (ne_of_lt hz.2) (hline hzseg)
    · intro z hz hzline _
      have hne : (star (a - v) * (z - v)).im ≠ 0 := hzline
      rcases hne.lt_or_gt with hneg | hpos
      · exact Or.inr ⟨hz, hneg⟩
      · exact Or.inl ⟨hz, hpos⟩
  · have hpos : 0 < (star (b - v) * (a - v)).im := by
      rw [transverse_swap]
      exact neg_pos.mpr hn
    obtain ⟨L, R, hLc, hRc, hLa, hRa, hLb, hRb, hcover⟩ :=
      exists_connected_vertex_regions_of_cross_pos v b a r hr hpos
    refine ⟨L, R, hLc, hRc, ?_, ?_, hLb, hRb, ?_⟩
    · simpa only [Set.union_comm] using hLa
    · simpa only [Set.union_comm] using hRa
    · intro z hz hza hzb
      exact hcover z hz hzb hza

/-- Helper toward Proposition 5.16: if the polygon in a vertex ball consists
of two nondegenerate incident segments, that ball meets at most two global
complementary components. -/
theorem exists_two_components_of_local_incident_segments (c : Polyline)
    (v a b : ℂ) (r : ℝ) (ha : a ≠ v) (hb : b ≠ v) (hr : 0 < r)
    (himage : ∀ y ∈ Metric.ball v r,
      y ∈ c.image ↔ y ∈ segment ℝ v a ∪ segment ℝ v b) :
    ∃ u w : ℂ, u ∉ c.image ∧ w ∉ c.image ∧
      ∀ z ∈ Metric.ball v r, z ∉ c.image →
        connectedComponentIn c.imageᶜ z = connectedComponentIn c.imageᶜ u ∨
        connectedComponentIn c.imageᶜ z = connectedComponentIn c.imageᶜ w := by
  obtain ⟨L, R, hLc, hRc, hLa, hRa, hLb, hRb, hcover⟩ :=
    exists_connected_vertex_regions v a b r ha hb hr
  have hL : L ⊆ c.imageᶜ := fun y hy hyimage => hLa hy ((himage y (hLb hy)).mp hyimage)
  have hR : R ⊆ c.imageᶜ := fun y hy hyimage => hRa hy ((himage y (hRb hy)).mp hyimage)
  obtain ⟨u, hu⟩ := hLc.nonempty
  obtain ⟨w, hw⟩ := hRc.nonempty
  have hLC : L ⊆ connectedComponentIn c.imageᶜ u :=
    hLc.isPreconnected.subset_connectedComponentIn hu hL
  have hRC : R ⊆ connectedComponentIn c.imageᶜ w :=
    hRc.isPreconnected.subset_connectedComponentIn hw hR
  refine ⟨u, w, hL hu, hR hw, ?_⟩
  intro z hz hzim
  let O := connectedComponentIn c.imageᶜ z ∩ Metric.ball v r
  have hopen : IsOpen O :=
    c.isCompact_image.isClosed.isOpen_compl.connectedComponentIn.inter Metric.isOpen_ball
  obtain ⟨y, hy, hya, hyb⟩ := exists_mem_open_off_two_edgeLines O hopen
    ⟨z, mem_connectedComponentIn hzim, hz⟩ v (a - v) (b - v)
    (sub_ne_zero.mpr ha) (sub_ne_zero.mpr hb)
  have hzy := connectedComponentIn_eq hy.1
  rcases hcover y hy.2 hya hyb with hyL | hyR
  · exact Or.inl (hzy.trans (connectedComponentIn_eq (hLC hyL)).symm)
  · exact Or.inr (hzy.trans (connectedComponentIn_eq (hRC hyR)).symm)

/-- Helper toward Proposition 5.16: a vertex ball of a cyclically simple
polygon meets at most two complementary components, with cyclic root incidence. -/
theorem exists_two_components_near_vertex_cyclic (c : Polyline)
    (hc : c.IsCyclicSimple) (i : ℕ) (hi : i + 1 < c.points.length) :
    ∃ r : ℝ, 0 < r ∧ ∃ u w : ℂ, u ∉ c.image ∧ w ∉ c.image ∧
      ∀ z ∈ Metric.ball (c.point i) r, z ∉ c.image →
        connectedComponentIn c.imageᶜ z = connectedComponentIn c.imageᶜ u ∨
        connectedComponentIn c.imageᶜ z = connectedComponentIn c.imageᶜ w := by
  let k := if i = 0 then c.points.length - 2 else i - 1
  have hk : k + 1 < c.points.length := by
    dsimp [k]
    split_ifs <;> omega
  have hkv : c.point (k + 1) = c.point i := by
    dsimp [k]
    split_ifs with h
    · rw [h, show c.points.length - 2 + 1 = c.points.length - 1 by have := hc.1; omega]
      exact hc.2.1.symm
    · congr 1
      omega
  have ha : c.point k ≠ c.point i := by
    rw [← hkv]
    exact hc.2.2.1 k hk
  have hb : c.point (i + 1) ≠ c.point i := (hc.2.2.1 i hi).symm
  obtain ⟨r, hr, himage⟩ := exists_pos_ball_image_eq_incident_segments_cyclic c hc i hi
  refine ⟨r, hr, ?_⟩
  apply exists_two_components_of_local_incident_segments c (c.point i)
    (c.point k) (c.point (i + 1)) r ha hb hr
  intro y hy
  have h := himage y hy
  change (y ∈ c.image ↔ y ∈ c.segmentAt k ∪ c.segmentAt i) at h
  simpa only [segmentAt, hkv, segment_symm ℝ (c.point k) (c.point i)] using h

/-- Helper toward Proposition 5.16: an edge-interior ball of a cyclically
simple polygon meets at most two global complementary components. -/
theorem exists_two_components_near_edge_interior_cyclic (c : Polyline)
    (hc : c.IsCyclicSimple) (i : ℕ) (hi : i + 1 < c.points.length)
    (x : ℂ) (hx : x ∈ c.segmentAt i) (hxa : x ≠ c.point i)
    (hxb : x ≠ c.point (i + 1)) :
    ∃ r : ℝ, 0 < r ∧ ∃ u w : ℂ, u ∉ c.image ∧ w ∉ c.image ∧
      ∀ z ∈ Metric.ball x r, z ∉ c.image →
        connectedComponentIn c.imageᶜ z = connectedComponentIn c.imageᶜ u ∨
        connectedComponentIn c.imageᶜ z = connectedComponentIn c.imageᶜ w := by
  obtain ⟨r, hr, _, _, hLne, hRne, hLc, hRc, hLd, hRd⟩ :=
    exists_connected_edge_sides_cyclic c hc i hi x hx hxa hxb
  let d := c.point (i + 1) - c.point i
  have hd : d ≠ 0 := sub_ne_zero.mpr (hc.2.2.1 i hi).symm
  obtain ⟨u, hu⟩ := hLne
  obtain ⟨w, hw⟩ := hRne
  have hL : leftHalfDisc x d r ⊆ c.imageᶜ := fun _ hy him =>
    Set.disjoint_left.mp hLd hy him
  have hR : rightHalfDisc x d r ⊆ c.imageᶜ := fun _ hy him =>
    Set.disjoint_left.mp hRd hy him
  have hLC := hLc.isPreconnected.subset_connectedComponentIn hu hL
  have hRC := hRc.isPreconnected.subset_connectedComponentIn hw hR
  refine ⟨r, hr, u, w, hL hu, hR hw, ?_⟩
  intro z hz hzim
  let O := connectedComponentIn c.imageᶜ z ∩ Metric.ball x r
  have hopen : IsOpen O :=
    c.isCompact_image.isClosed.isOpen_compl.connectedComponentIn.inter Metric.isOpen_ball
  obtain ⟨y, hy, hyline⟩ := (dense_compl_edgeLine x d hd).inter_open_nonempty O hopen
    ⟨z, mem_connectedComponentIn hzim, hz⟩
  have hzy := connectedComponentIn_eq hy.1
  have hne : (star d * (y - x)).im ≠ 0 := hyline
  rcases hne.lt_or_gt with hn | hp
  · exact Or.inr (hzy.trans (connectedComponentIn_eq (hRC ⟨hy.2, hn⟩)).symm)
  · exact Or.inl (hzy.trans (connectedComponentIn_eq (hLC ⟨hy.2, hp⟩)).symm)

/-- Helper toward Proposition 5.16: every image point has a neighborhood
meeting at most two complementary components. -/
theorem exists_two_components_near_image_cyclic (c : Polyline)
    (hc : c.IsCyclicSimple) (x : ℂ) (hx : x ∈ c.image) :
    ∃ r : ℝ, 0 < r ∧ ∃ u w : ℂ, u ∉ c.image ∧ w ∉ c.image ∧
      ∀ z ∈ Metric.ball x r, z ∉ c.image →
        connectedComponentIn c.imageᶜ z = connectedComponentIn c.imageᶜ u ∨
        connectedComponentIn c.imageᶜ z = connectedComponentIn c.imageᶜ w := by
  rcases hx with hxroot | ⟨i, hi, hxi⟩
  · have hx0 : x = c.point 0 := by
      simpa only [Set.mem_singleton_iff, point_zero_eq_start] using hxroot
    rw [hx0]
    exact exists_two_components_near_vertex_cyclic c hc 0 (by have := hc.1; omega)
  · by_cases hxa : x = c.point i
    · rw [hxa]
      exact exists_two_components_near_vertex_cyclic c hc i hi
    by_cases hxb : x = c.point (i + 1)
    · by_cases hlast : i + 2 < c.points.length
      · rw [hxb]
        exact exists_two_components_near_vertex_cyclic c hc (i + 1) (by omega)
      · have hx0 : x = c.point 0 := by
          rw [hxb, show i + 1 = c.points.length - 1 by omega]
          exact hc.2.1.symm
        rw [hx0]
        exact exists_two_components_near_vertex_cyclic c hc 0 (by have := hc.1; omega)
    · exact exists_two_components_near_edge_interior_cyclic c hc i hi x hxi hxa hxb

/-- Helper toward Proposition 5.16: at most two global complementary
components can have a given image point in their closure. -/
theorem exists_two_components_closure_at_image_cyclic (c : Polyline)
    (hc : c.IsCyclicSimple) (x : ℂ) (hx : x ∈ c.image) :
    ∃ u v : ℂ, u ∉ c.image ∧ v ∉ c.image ∧
      ∀ z : ℂ, x ∈ closure (connectedComponentIn c.imageᶜ z) →
        connectedComponentIn c.imageᶜ z = connectedComponentIn c.imageᶜ u ∨
        connectedComponentIn c.imageᶜ z = connectedComponentIn c.imageᶜ v := by
  obtain ⟨r, hr, u, v, hu, hv, hcover⟩ := exists_two_components_near_image_cyclic c hc x hx
  refine ⟨u, v, hu, hv, ?_⟩
  intro z hz
  obtain ⟨w, hwb, hwc⟩ := mem_closure_iff.mp hz (Metric.ball x r) Metric.isOpen_ball
    (by simpa only [Metric.mem_ball, dist_self] using hr)
  have hzw := connectedComponentIn_eq hwc
  rcases hcover w hwb (connectedComponentIn_subset _ _ hwc) with hwu | hwv
  · exact Or.inl (hzw.trans hwu)
  · exact Or.inr (hzw.trans hwv)

/-- Helper toward Proposition 5.16: any two distinct components approaching
an image point exhaust all components approaching that point. This is the
unordered vertex gluing principle. -/
theorem component_eq_or_eq_of_closure_cyclic (c : Polyline)
    (hc : c.IsCyclicSimple) (x : ℂ) (hx : x ∈ c.image) (u v z : ℂ)
    (hne : connectedComponentIn c.imageᶜ u ≠ connectedComponentIn c.imageᶜ v)
    (hu : x ∈ closure (connectedComponentIn c.imageᶜ u))
    (hv : x ∈ closure (connectedComponentIn c.imageᶜ v))
    (hz : x ∈ closure (connectedComponentIn c.imageᶜ z)) :
    connectedComponentIn c.imageᶜ z = connectedComponentIn c.imageᶜ u ∨
      connectedComponentIn c.imageᶜ z = connectedComponentIn c.imageᶜ v := by
  obtain ⟨p, q, _, _, h⟩ := exists_two_components_closure_at_image_cyclic c hc x hx
  rcases h u hu with hup | huq
  · rcases h v hv with hvp | hvq
    · exact False.elim (hne (hup.trans hvp.symm))
    · rcases h z hz with hzp | hzq
      · exact Or.inl (hzp.trans hup.symm)
      · exact Or.inr (hzq.trans hvq.symm)
  · rcases h v hv with hvp | hvq
    · rcases h z hz with hzp | hzq
      · exact Or.inr (hzp.trans hvp.symm)
      · exact Or.inl (hzq.trans huq.symm)
    · exact False.elim (hne (huq.trans hvq.symm))

/-- Helper toward Proposition 5.16: the same two distinct complementary
components approach every edge and every vertex of a cyclically simple polygon. -/
theorem exists_distinct_components_closure_image_cyclic (c : Polyline)
    (hc : c.IsCyclicSimple) :
    ∃ u v : ℂ, u ∉ c.image ∧ v ∉ c.image ∧
      connectedComponentIn c.imageᶜ u ≠ connectedComponentIn c.imageᶜ v ∧
      c.image ⊆ closure (connectedComponentIn c.imageᶜ u) ∩
        closure (connectedComponentIn c.imageᶜ v) := by
  have h0 : 0 + 1 < c.points.length := by have := hc.1; omega
  obtain ⟨u, v, hu, hv, hne, hcl0⟩ :=
    exists_distinct_components_adjacent_to_edge_cyclic c hc 0 h0
  have hedge : ∀ i, i + 1 < c.points.length →
      c.segmentAt i ⊆ closure (connectedComponentIn c.imageᶜ u) ∩
        closure (connectedComponentIn c.imageᶜ v) := by
    intro i
    induction i with
    | zero => exact fun _ => hcl0
    | succ i ih =>
      intro hi
      have hip : i + 1 < c.points.length := by omega
      have hvertex : c.point (i + 1) ∈ c.image :=
        c.segmentAt_subset_image hip (right_mem_segment ℝ _ _)
      have hprev := ih hip (right_mem_segment ℝ (c.point i) (c.point (i + 1)))
      obtain ⟨a, b, _, _, hab, hcl⟩ :=
        exists_distinct_components_adjacent_to_edge_cyclic c hc (i + 1) hi
      have hnext := hcl (left_mem_segment ℝ (c.point (i + 1)) (c.point (i + 1 + 1)))
      have haeq := component_eq_or_eq_of_closure_cyclic c hc _ hvertex u v a hne
        hprev.1 hprev.2 hnext.1
      have hbeq := component_eq_or_eq_of_closure_cyclic c hc _ hvertex u v b hne
        hprev.1 hprev.2 hnext.2
      rcases haeq with haeq | haeq <;> rcases hbeq with hbeq | hbeq
      · exact False.elim (hab (haeq.trans hbeq.symm))
      · simpa only [haeq, hbeq] using hcl
      · intro y hy
        have h := hcl hy
        exact ⟨by simpa only [hbeq] using h.2, by simpa only [haeq] using h.1⟩
      · exact False.elim (hab (haeq.trans hbeq.symm))
  refine ⟨u, v, hu, hv, hne, ?_⟩
  intro x hx
  rcases hx with hxroot | ⟨i, hi, hxi⟩
  · have hx0 : x = c.point 0 := by
      simpa only [Set.mem_singleton_iff, point_zero_eq_start] using hxroot
    rw [hx0]
    exact hcl0 (left_mem_segment ℝ _ _)
  · exact hedge i hi hxi

/-- Helper toward Proposition 5.16: the complement of a cyclically simple
polygon has exactly two components, represented by distinct complementary
points. No separation theorem is assumed. -/
theorem exists_exactly_two_components_cyclic (c : Polyline)
    (hc : c.IsCyclicSimple) :
    ∃ u v : ℂ, u ∉ c.image ∧ v ∉ c.image ∧
      connectedComponentIn c.imageᶜ u ≠ connectedComponentIn c.imageᶜ v ∧
      c.image ⊆ closure (connectedComponentIn c.imageᶜ u) ∩
        closure (connectedComponentIn c.imageᶜ v) ∧
      ∀ z : ℂ, z ∉ c.image →
        connectedComponentIn c.imageᶜ z = connectedComponentIn c.imageᶜ u ∨
        connectedComponentIn c.imageᶜ z = connectedComponentIn c.imageᶜ v := by
  obtain ⟨u, v, hu, hv, hne, hcl⟩ := exists_distinct_components_closure_image_cyclic c hc
  refine ⟨u, v, hu, hv, hne, hcl, ?_⟩
  intro z hz
  obtain ⟨x, hx, hxcl⟩ := exists_image_mem_closure_component c z hz
  exact component_eq_or_eq_of_closure_cyclic c hc x hx u v z hne
    (hcl hx).1 (hcl hx).2 hxcl

/-- Helper toward Proposition 5.16: the winding inside and outside are the
two complementary components, and both approach the entire polygon image. -/
theorem exists_inside_outside_components_cyclic (c : Polyline)
    (hc : c.IsCyclicSimple) :
    ∃ a b : ℂ, a ∈ c.inside ∧ b ∈ c.outside ∧
      c.inside = connectedComponentIn c.imageᶜ a ∧
      c.outside = connectedComponentIn c.imageᶜ b ∧
      c.image ⊆ closure c.inside ∩ closure c.outside := by
  have hclosed : c.start = c.finish := by
    rw [← point_zero_eq_start c, ← point_last_eq_finish c]
    exact hc.2.1
  obtain ⟨u, v, hu, hv, _, hcl, hclass⟩ := exists_exactly_two_components_cyclic c hc
  obtain ⟨a, ha⟩ := inside_nonempty_cyclic c hc
  obtain ⟨b, hb, _⟩ := outside_unbounded c hclosed 0
  have hab : connectedComponentIn c.imageᶜ a ≠ connectedComponentIn c.imageᶜ b := by
    intro heq
    have hbcomp : b ∈ connectedComponentIn c.imageᶜ a :=
      heq.symm ▸ mem_connectedComponentIn hb.1
    have hbin := component_subset_inside c hclosed a ha hbcomp
    exact hbin.2 hb.2
  have hau := hclass a ha.1
  have hbu := hclass b hb.1
  have hclass' : ∀ z : ℂ, z ∉ c.image →
      connectedComponentIn c.imageᶜ z = connectedComponentIn c.imageᶜ a ∨
      connectedComponentIn c.imageᶜ z = connectedComponentIn c.imageᶜ b := by
    intro z hz
    rcases hau with hau | hav
    · rcases hbu with hbu | hbv
      · exact False.elim (hab (hau.trans hbu.symm))
      · rcases hclass z hz with hzu | hzv
        · exact Or.inl (hzu.trans hau.symm)
        · exact Or.inr (hzv.trans hbv.symm)
    · rcases hbu with hbu | hbv
      · rcases hclass z hz with hzu | hzv
        · exact Or.inr (hzu.trans hbu.symm)
        · exact Or.inl (hzv.trans hav.symm)
      · exact False.elim (hab (hav.trans hbv.symm))
  have hinside : c.inside = connectedComponentIn c.imageᶜ a := by
    apply Set.Subset.antisymm ?_ (component_subset_inside c hclosed a ha)
    intro z hz
    rcases hclass' z hz.1 with hza | hzb
    · exact hza.symm ▸ mem_connectedComponentIn hz.1
    · have hzbmem : z ∈ connectedComponentIn c.imageᶜ b :=
        hzb ▸ mem_connectedComponentIn hz.1
      have hzout := component_subset_outside c hclosed b hb hzbmem
      exact False.elim (hz.2 hzout.2)
  have houtside : c.outside = connectedComponentIn c.imageᶜ b := by
    apply Set.Subset.antisymm ?_ (component_subset_outside c hclosed b hb)
    intro z hz
    rcases hclass' z hz.1 with hza | hzb
    · have hzamem : z ∈ connectedComponentIn c.imageᶜ a :=
        hza ▸ mem_connectedComponentIn hz.1
      have hzin := component_subset_inside c hclosed a ha hzamem
      exact False.elim (hzin.2 hz.2)
    · exact hzb.symm ▸ mem_connectedComponentIn hz.1
  refine ⟨a, b, ha, hb, hinside, houtside, ?_⟩
  intro x hx
  have hxa : x ∈ closure (connectedComponentIn c.imageᶜ a) := by
    rcases hau with hau | hav
    · rw [hau]
      exact (hcl hx).1
    · rw [hav]
      exact (hcl hx).2
  have hxb : x ∈ closure (connectedComponentIn c.imageᶜ b) := by
    rcases hbu with hbu | hbv
    · rw [hbu]
      exact (hcl hx).1
    · rw [hbv]
      exact (hcl hx).2
  simpa only [hinside, houtside, Set.mem_inter_iff] using And.intro hxa hxb

/-- Helper toward Proposition 5.16: both winding sides of a cyclically simple
polygon are connected. -/
theorem isConnected_inside_outside_cyclic (c : Polyline)
    (hc : c.IsCyclicSimple) : IsConnected c.inside ∧ IsConnected c.outside := by
  obtain ⟨a, b, ha, hb, hin, hout, _⟩ := exists_inside_outside_components_cyclic c hc
  rw [hin, hout]
  exact ⟨isConnected_connectedComponentIn_iff.mpr ha.1,
    isConnected_connectedComponentIn_iff.mpr hb.1⟩

/-- Helper toward Proposition 5.16: the frontiers of both winding sides are
exactly the image of a cyclically simple polygon. -/
theorem frontier_inside_outside_eq_image_cyclic (c : Polyline)
    (hc : c.IsCyclicSimple) : frontier c.inside = c.image ∧ frontier c.outside = c.image := by
  have hclosed : c.start = c.finish := by
    rw [← point_zero_eq_start c, ← point_last_eq_finish c]
    exact hc.2.1
  obtain ⟨_, _, _, _, _, _, hcl⟩ := exists_inside_outside_components_cyclic c hc
  constructor
  · apply Set.Subset.antisymm (frontier_inside_subset_image c hclosed)
    intro z hz
    rw [frontier, (isOpen_inside c hclosed).interior_eq]
    exact ⟨(hcl hz).1, fun hzin => hzin.1 hz⟩
  · apply Set.Subset.antisymm (frontier_outside_subset_image c hclosed)
    intro z hz
    rw [frontier, (isOpen_outside c hclosed).interior_eq]
    exact ⟨(hcl hz).2, fun hzout => hzout.1 hz⟩

/-- Helper toward Proposition 5.16: the endpoint-glued polygon formed by
two simple arcs meeting only at their distinct common endpoints has connected
bounded and unbounded complementary regions with the prescribed common frontier. -/
theorem exists_polygonal_separation (p q : Polyline)
    (hp : p.IsSimple) (hq : q.IsSimple)
    (hlenp : 2 ≤ p.points.length) (hlenq : 2 ≤ q.points.length)
    (hstart : p.start = q.start) (hfinish : p.finish = q.finish)
    (hne : p.start ≠ p.finish)
    (hint : p.image ∩ q.image = {p.start, p.finish}) :
    ∃ B U : Set ℂ, IsOpen B ∧ IsOpen U ∧ IsConnected B ∧ IsConnected U ∧
      Disjoint B U ∧ B ∪ U = (p.image ∪ q.image)ᶜ ∧
      Bornology.IsBounded B ∧ (∀ R : ℝ, ∃ z ∈ U, R < ‖z‖) ∧
      frontier B = p.image ∪ q.image ∧ frontier U = p.image ∪ q.image := by
  let c := closedConcat p q
  have hc : c.IsCyclicSimple :=
    closedConcat_isCyclicSimple p q hp hq hlenp hlenq hstart hfinish hne hint
  have hclosed : c.start = c.finish := closedConcat_closed p q hlenq hstart
  have himage : c.image = p.image ∪ q.image := image_closedConcat p q hfinish
  obtain ⟨hcin, hcout⟩ := isConnected_inside_outside_cyclic c hc
  obtain ⟨hfin, hfout⟩ := frontier_inside_outside_eq_image_cyclic c hc
  refine ⟨c.inside, c.outside, isOpen_inside c hclosed, isOpen_outside c hclosed,
    hcin, hcout, disjoint_inside_outside c, ?_, isBounded_inside c hclosed,
    outside_unbounded c hclosed, ?_, ?_⟩
  · rw [inside_union_outside, himage]
  · exact hfin.trans himage
  · exact hfout.trans himage

end Polyline
end DirectedDistances.PlanarMap
end

