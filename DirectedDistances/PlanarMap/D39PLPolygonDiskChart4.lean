/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLPolygonDiskChart3

/-! # Clipped neighbour triangles and visibility

these geometric results do not assert completion of that proposition. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
namespace Polyline
open Topology

/-- Helper toward Proposition 5.16: an edge entering the part of a triangle
strictly above a nonnegative coordinate level crosses an incident side, provided
its endpoints in the triangle are at or below that level. -/
theorem exists_incident_side_mem_openSegment_above (B : AffineBasis (Fin 3) ℝ ℂ)
    (h : ℝ) (hh : 0 ≤ h) (p q z : ℂ)
    (hp : p ∈ convexHull ℝ (Set.range B) → B.coord 1 p ≤ h)
    (hq : q ∈ convexHull ℝ (Set.range B) → B.coord 1 q ≤ h)
    (hzseg : z ∈ segment ℝ p q)
    (hz : z ∈ _root_.interior (convexHull ℝ (Set.range B)))
    (hzh : h < B.coord 1 z) :
    ∃ y ∈ openSegment ℝ p q,
      y ∈ segment ℝ (B 0) (B 1) ∪ segment ℝ (B 1) (B 2) := by
  have hzpos : ∀ i, 0 < B.coord i z := by
    rwa [B.interior_convexHull] at hz
  have main (p q : ℂ)
      (hp : p ∈ convexHull ℝ (Set.range B) → B.coord 1 p ≤ h)
      (hq : q ∈ convexHull ℝ (Set.range B) → B.coord 1 q ≤ h)
      (hzseg : z ∈ segment ℝ p q) (hpβ : h < B.coord 1 p) :
      ∃ y ∈ openSegment ℝ p q,
        y ∈ segment ℝ (B 0) (B 1) ∪ segment ℝ (B 1) (B 2) := by
    have hpnot : p ∉ convexHull ℝ (Set.range B) :=
      fun hpT => (not_lt_of_ge (hp hpT)) hpβ
    have hpmin : min (B.coord 0 p) (B.coord 2 p) < 0 := by
      apply lt_of_not_ge
      intro hm
      apply hpnot
      rw [B.convexHull_eq_nonneg_coord]
      intro i
      fin_cases i
      · exact (le_min_iff.mp hm).1
      · exact hh.trans hpβ.le
      · exact (le_min_iff.mp hm).2
    have hzmin : 0 < min (B.coord 0 z) (B.coord 2 z) := lt_min (hzpos 0) (hzpos 2)
    have hf : Continuous (fun x : ℂ => min (B.coord 0 x) (B.coord 2 x)) :=
      ((B.coord 0).continuous_of_finiteDimensional).min
        ((B.coord 2).continuous_of_finiteDimensional)
    obtain ⟨y, hyseg, hyzero⟩ := (convex_segment p z).isPreconnected.intermediate_value
      (left_mem_segment ℝ p z) (right_mem_segment ℝ p z) hf.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (min (B.coord 0 p) (B.coord 2 p))
        (min (B.coord 0 z) (B.coord 2 z)) from ⟨hpmin.le, hzmin.le⟩)
    change min (B.coord 0 y) (B.coord 2 y) = 0 at hyzero
    have hyβ : h < B.coord 1 y :=
      ((convex_Ioi h).affine_preimage (B.coord 1)).segment_subset hpβ hzh hyseg
    have hy0 : 0 ≤ B.coord 0 y := (le_min_iff.mp hyzero.ge).1
    have hy2 : 0 ≤ B.coord 2 y := (le_min_iff.mp hyzero.ge).2
    have hyT : y ∈ convexHull ℝ (Set.range B) := by
      rw [B.convexHull_eq_nonneg_coord]
      intro i
      fin_cases i
      · exact hy0
      · exact hh.trans hyβ.le
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
      refine ⟨B.coord 1 y, B.coord 2 y, hh.trans hyβ.le, hy2, ?_, ?_⟩
      · linarith only [hsum, hy0eq]
      · simpa only [hy0eq, zero_smul, zero_add] using hrep
    · have hy2eq : B.coord 2 y = 0 := by rwa [min_eq_right hle] at hyzero
      left
      refine ⟨B.coord 0 y, B.coord 1 y, hy0, hh.trans hyβ.le, ?_, ?_⟩
      · linarith only [hsum, hy2eq]
      · simpa only [hy2eq, zero_smul, add_zero] using hrep
  have hend : h < B.coord 1 p ∨ h < B.coord 1 q := by
    by_contra hn
    push Not at hn
    have hznon : B.coord 1 z ≤ h :=
      ((convex_Iic h).affine_preimage (B.coord 1)).segment_subset hn.1 hn.2 hzseg
    exact (not_lt_of_ge hznon) hzh
  rcases hend with hpβ | hqβ
  · exact main p q hp hq hzseg hpβ
  · simpa only [openSegment_symm] using main q p hq hp
      (by simpa only [segment_symm] using hzseg) hqβ

/-- Helper toward Proposition 5.16: the open cap above a coordinate bound
for all vertices other than the tip misses the whole polygon image. -/
theorem disjoint_triangle_cap_image (c : Polyline) (hc : c.IsCyclicSimple)
    (i : ℕ) (hi : i + 1 < c.points.length)
    (B : AffineBasis (Fin 3) ℝ ℂ)
    (hB0 : B 0 = c.point (if i = 0 then c.points.length - 2 else i - 1))
    (hB1 : B 1 = c.point i) (hB2 : B 2 = c.point (i + 1))
    (h : ℝ) (hh : 0 ≤ h)
    (hvertices : ∀ m, m < c.points.length →
      c.point m ∈ convexHull ℝ (Set.range B) → c.point m ≠ B 1 →
      B.coord 1 (c.point m) ≤ h) :
    Disjoint {z ∈ _root_.interior (convexHull ℝ (Set.range B)) | h < B.coord 1 z}
      c.image := by
  let k := if i = 0 then c.points.length - 2 else i - 1
  have hk : k + 1 < c.points.length := by
    dsimp only [k]
    split_ifs <;> have := hc.1 <;> omega
  have hkv : c.point (k + 1) = c.point i := by
    dsimp only [k]
    split_ifs with h0
    · rw [show c.points.length - 2 + 1 = c.points.length - 1 by have := hc.1; omega]
      exact hc.2.1.symm.trans (congrArg c.point h0.symm)
    · congr 1
      omega
  have hside : Disjoint (_root_.interior (convexHull ℝ (Set.range B)))
      (segment ℝ (B 0) (B 1) ∪ segment ℝ (B 1) (B 2)) := by
    apply Set.disjoint_left.mpr
    intro z hz hzs
    have hp : ∀ n, 0 < B.coord n z := by rwa [B.interior_convexHull] at hz
    rcases hzs with hzs | hzs
    · obtain ⟨s, t, hs, ht, hst, heq⟩ := hzs
      have hz2 : B.coord 2 z = 0 := by
        rw [← heq, Convex.combo_affine_apply hst]
        simp only [B.coord_apply_ne (by decide : (2 : Fin 3) ≠ 0),
          B.coord_apply_ne (by decide : (2 : Fin 3) ≠ 1), smul_zero, add_zero]
      exact (ne_of_gt (hp 2)) hz2
    · obtain ⟨s, t, hs, ht, hst, heq⟩ := hzs
      have hz0 : B.coord 0 z = 0 := by
        rw [← heq, Convex.combo_affine_apply hst]
        simp only [B.coord_apply_ne (by decide : (0 : Fin 3) ≠ 1),
          B.coord_apply_ne (by decide : (0 : Fin 3) ≠ 2), smul_zero, add_zero]
      exact (ne_of_gt (hp 0)) hz0
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
  · apply Set.disjoint_left.mp hside hz.1
    right
    rw [hB1, hB2]
    exact hji ▸ hzj
  by_cases hjk : j = k
  · apply Set.disjoint_left.mp hside hz.1
    left
    rw [hB0, hB1]
    change z ∈ segment ℝ (c.point k) (c.point i)
    rw [← hkv]
    exact hjk ▸ hzj
  have hvnot : c.point i ∉ c.segmentAt j := by
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
  have hcoord (m : ℕ) (hm : m < c.points.length) (hmj : c.point m ∈ c.segmentAt j)
      (hmT : c.point m ∈ convexHull ℝ (Set.range B)) : B.coord 1 (c.point m) ≤ h := by
    apply hvertices m hm hmT
    intro heq
    exact hvnot (by simpa only [heq, hB1] using hmj)
  obtain ⟨y, hyopen, hysides⟩ := exists_incident_side_mem_openSegment_above B h hh
    (c.point j) (c.point (j + 1)) z
    (hcoord j (by omega) (left_mem_segment ℝ _ _))
    (hcoord (j + 1) hj (right_mem_segment ℝ _ _)) hzj hz.1 hz.2
  rcases hysides with hyav | hyvb
  · have hyk : y ∈ c.segmentAt k := by
      simpa only [hB0, hB1, segmentAt, hkv] using hyav
    exact Set.disjoint_left.mp (disjoint_openSegment_segmentAt_cyclic c hc j k hj hk hjk)
      hyopen hyk
  · have hyi : y ∈ c.segmentAt i := by
      change y ∈ segment ℝ (c.point i) (c.point (i + 1))
      simpa only [hB1, hB2] using hyvb
    exact Set.disjoint_left.mp (disjoint_openSegment_segmentAt_cyclic c hc j i hj hi hji)
      hyopen hyi

/-- Helper toward Proposition 5.16: every strict convex combination of the
tip and a point strictly between the incident sides is in the open cap above
that point's level. This includes a point on the opposite open side. -/
theorem openSegment_tip_subset_cap (B : AffineBasis (Fin 3) ℝ ℂ) (x : ℂ)
    (hx0 : 0 < B.coord 0 x) (hx2 : 0 < B.coord 2 x) (hx1 : 0 ≤ B.coord 1 x) :
    openSegment ℝ (B 1) x ⊆
      {z ∈ _root_.interior (convexHull ℝ (Set.range B)) | B.coord 1 x < B.coord 1 z} := by
  have hsum : B.coord 0 x + B.coord 1 x + B.coord 2 x = 1 := by
    simpa only [Fin.sum_univ_three] using B.sum_coord_apply_eq_one x
  have hxlt : B.coord 1 x < 1 := by linarith only [hsum, hx0, hx2]
  rintro z ⟨s, t, hs, ht, hst, rfl⟩
  have hh : B.coord 1 x < B.coord 1 (s • B 1 + t • x) := by
    rw [Convex.combo_affine_apply hst, B.coord_apply_eq, smul_eq_mul, smul_eq_mul, mul_one]
    calc
      B.coord 1 x = (s + t) * B.coord 1 x := by rw [hst, one_mul]
      _ < s + t * B.coord 1 x := by nlinarith only [mul_pos hs (sub_pos.mpr hxlt)]
  refine ⟨?_, hh⟩
  rw [B.interior_convexHull]
  intro j
  fin_cases j
  · change 0 < B.coord 0 (s • B 1 + t • x)
    rw [Convex.combo_affine_apply hst,
      B.coord_apply_ne (by decide : (0 : Fin 3) ≠ 1), smul_zero, zero_add]
    exact mul_pos ht hx0
  · exact lt_of_le_of_lt hx1 hh
  · change 0 < B.coord 2 (s • B 1 + t • x)
    rw [Convex.combo_affine_apply hst,
      B.coord_apply_ne (by decide : (2 : Fin 3) ≠ 1), smul_zero, zero_add]
    exact mul_pos ht hx2

/-- Helper toward Proposition 5.16: a maximal-level point between the
incident sides is visible from a left supporting tip. No tie-breaking condition
is needed: the open segment lies strictly above the selected level. -/
theorem openSegment_tip_subset_inside_of_coord_max (c : Polyline)
    (hc : c.IsCyclicSimple) (i : ℕ) (hi : i + 1 < c.points.length)
    (B : AffineBasis (Fin 3) ℝ ℂ)
    (hB0 : B 0 = c.point (if i = 0 then c.points.length - 2 else i - 1))
    (hB1 : B 1 = c.point i) (hB2 : B 2 = c.point (i + 1))
    (hbound : ∀ m, m < c.points.length → (c.point i).re ≤ (c.point m).re)
    (x : ℂ) (hx0 : 0 < B.coord 0 x) (hx2 : 0 < B.coord 2 x)
    (hx1 : 0 ≤ B.coord 1 x)
    (hvertices : ∀ m, m < c.points.length →
      c.point m ∈ convexHull ℝ (Set.range B) → c.point m ≠ B 1 →
      B.coord 1 (c.point m) ≤ B.coord 1 x) :
    openSegment ℝ (B 1) x ⊆ c.inside := by
  let k := if i = 0 then c.points.length - 2 else i - 1
  have hk : k + 1 < c.points.length := by
    dsimp only [k]
    split_ifs <;> have := hc.1 <;> omega
  have hkv : c.point (k + 1) = c.point i := by
    dsimp only [k]
    split_ifs with h0
    · rw [show c.points.length - 2 + 1 = c.points.length - 1 by have := hc.1; omega]
      exact hc.2.1.symm.trans (congrArg c.point h0.symm)
    · congr 1
      omega
  have hnc : ¬ Collinear ℝ ({B 0, B 1, B 2} : Set ℂ) := by
    apply affineIndependent_iff_not_collinear_set.mp
    convert B.ind' using 1
    ext j
    fin_cases j <;> rfl
  have hclosed : c.start = c.finish := by
    rw [← point_zero_eq_start c, ← point_last_eq_finish c]
    exact hc.2.1
  obtain ⟨r, hr, hlocal⟩ := exists_pos_ball_image_eq_incident_segments_cyclic c hc i hi
  have hlocal' : ∀ z ∈ Metric.ball (B 1) r,
      z ∈ c.image ↔ z ∈ segment ℝ (B 1) (B 0) ∪ segment ℝ (B 1) (B 2) := by
    intro z hz
    have hh := hlocal z (by simpa only [Metric.mem_ball, hB1] using hz)
    change z ∈ c.image ↔ z ∈ c.segmentAt k ∪ c.segmentAt i at hh
    simpa only [segmentAt, hkv, segment_symm ℝ (c.point k) (c.point i),
      hB0, hB1, hB2] using hh
  have hsector := triangle_sector_subset_inside_of_support c hc (B 1) (B 0) (B 2)
    (hB1.symm ▸ c.point_mem_image (by omega)) r hr hnc
    (by rw [hB0, hB1]; exact hbound k (by omega))
    (by rw [hB1, hB2]; exact hbound (i + 1) hi)
    (by rw [hB1]; exact fun z hz => re_le_of_mem_image c _ hbound hz) hlocal'
  have hcap := disjoint_triangle_cap_image c hc i hi B hB0 hB1 hB2
    (B.coord 1 x) hx1 hvertices
  have hseg := openSegment_tip_subset_cap B x hx0 hx2 hx1
  have hrange : Set.range B = ({B 0, B 1, B 2} : Set ℂ) := by
    ext z
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j <;> tauto
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  have hvcl : B 1 ∈ closure (openSegment ℝ (B 1) x) :=
    segment_subset_closure_openSegment (left_mem_segment ℝ _ _)
  obtain ⟨z, hz, hd⟩ := Metric.mem_closure_iff.mp hvcl r hr
  have hzin : z ∈ c.inside := hsector ⟨by
    simpa only [Metric.mem_ball, dist_comm] using hd,
    by simpa only [hrange] using (hseg hz).1⟩
  rcases subset_inside_or_outside_of_isPreconnected c hclosed _
      (convex_openSegment (B 1) x).isPreconnected
      (fun y hy => Set.disjoint_left.mp hcap (hseg hy)) with hin | hout
  · exact hin
  · exact False.elim (hzin.2 (hout hz).2)

/-- Helper toward Proposition 5.16: a listed polygon vertex on an edge is
one of its endpoints, including the duplicated root vertex. -/
theorem point_eq_endpoint_of_mem_segmentAt_cyclic (c : Polyline)
    (hc : c.IsCyclicSimple) (m j : ℕ) (hm : m < c.points.length)
    (hj : j + 1 < c.points.length) (hmem : c.point m ∈ c.segmentAt j) :
    c.point m = c.point j ∨ c.point m = c.point (j + 1) := by
  have main (m : ℕ) (hm : m + 1 < c.points.length)
      (hmem : c.point m ∈ c.segmentAt j) :
      c.point m = c.point j ∨ c.point m = c.point (j + 1) := by
    by_cases h : j = m
    · exact Or.inl (congrArg c.point h.symm)
    by_cases hprev : j + 1 = m
    · exact Or.inr (congrArg c.point hprev.symm)
    by_cases hwrap : m = 0 ∧ j + 2 = c.points.length
    · right
      rw [hwrap.1, hc.2.1]
      congr 1
      omega
    · exact False.elim
        (not_mem_segmentAt_of_ne_vertex_cyclic c hc m j hm hj h hprev hwrap hmem)
  by_cases hm' : m + 1 < c.points.length
  · exact main m hm' hmem
  · have heq : c.point m = c.point 0 := by
      rw [show m = c.points.length - 1 by omega, ← hc.2.1]
    rw [heq] at hmem ⊢
    exact main 0 (by have := hc.1; omega) hmem

/-- Helper toward Proposition 5.16: a triangle point outside its two
incident sides has strictly positive coordinates at both base vertices. -/
theorem triangle_pos_coords_of_not_mem_incident_sides
    (B : AffineBasis (Fin 3) ℝ ℂ) (x : ℂ)
    (hx : x ∈ convexHull ℝ (Set.range B))
    (hside : x ∉ segment ℝ (B 0) (B 1) ∪ segment ℝ (B 1) (B 2)) :
    0 < B.coord 0 x ∧ 0 < B.coord 2 x := by
  have hnon : ∀ j, 0 ≤ B.coord j x := by rwa [B.convexHull_eq_nonneg_coord] at hx
  have hsum : B.coord 0 x + B.coord 1 x + B.coord 2 x = 1 := by
    simpa only [Fin.sum_univ_three] using B.sum_coord_apply_eq_one x
  have hrep : B.coord 0 x • B 0 + B.coord 1 x • B 1 + B.coord 2 x • B 2 = x := by
    simpa only [Fin.sum_univ_three] using B.linear_combination_coord_eq_self x
  constructor
  · apply lt_of_le_of_ne (hnon 0)
    intro heq
    apply hside
    right
    refine ⟨B.coord 1 x, B.coord 2 x, hnon 1, hnon 2, ?_, ?_⟩
    · linarith only [hsum, heq]
    · simpa only [← heq, zero_smul, zero_add] using hrep
  · apply lt_of_le_of_ne (hnon 2)
    intro heq
    apply hside
    left
    refine ⟨B.coord 0 x, B.coord 1 x, hnon 0, hnon 1, ?_, ?_⟩
    · linarith only [hsum, heq]
    · simpa only [← heq, zero_smul, add_zero] using hrep

/-- Helper toward Proposition 5.16: an extra polygon vertex in the closed
neighbour triangle is strictly between the two incident sides. -/
theorem extra_vertex_triangle_pos_coords (c : Polyline) (hc : c.IsCyclicSimple)
    (i : ℕ) (hi : i + 1 < c.points.length)
    (B : AffineBasis (Fin 3) ℝ ℂ)
    (hB0 : B 0 = c.point (if i = 0 then c.points.length - 2 else i - 1))
    (hB1 : B 1 = c.point i) (hB2 : B 2 = c.point (i + 1))
    (m : ℕ) (hm : m < c.points.length)
    (hmT : c.point m ∈ convexHull ℝ (Set.range B))
    (hmne : c.point m ∉ ({B 0, B 1, B 2} : Set ℂ)) :
    0 < B.coord 0 (c.point m) ∧ 0 < B.coord 2 (c.point m) := by
  let k := if i = 0 then c.points.length - 2 else i - 1
  have hk : k + 1 < c.points.length := by
    dsimp only [k]
    split_ifs <;> have := hc.1 <;> omega
  have hkv : c.point (k + 1) = c.point i := by
    dsimp only [k]
    split_ifs with h0
    · rw [show c.points.length - 2 + 1 = c.points.length - 1 by have := hc.1; omega]
      exact hc.2.1.symm.trans (congrArg c.point h0.symm)
    · congr 1
      omega
  apply triangle_pos_coords_of_not_mem_incident_sides B _ hmT
  intro hside
  apply hmne
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hside with hs | hs
  · have hs' : c.point m ∈ c.segmentAt k := by
      simpa only [hB0, hB1, segmentAt, hkv] using hs
    rcases point_eq_endpoint_of_mem_segmentAt_cyclic c hc m k hm hk hs' with heq | heq
    · exact Or.inl (heq.trans hB0.symm)
    · exact Or.inr (Or.inl (heq.trans (hkv.trans hB1.symm)))
  · have hs' : c.point m ∈ c.segmentAt i := by
      change c.point m ∈ segment ℝ (c.point i) (c.point (i + 1))
      simpa only [hB1, hB2] using hs
    rcases point_eq_endpoint_of_mem_segmentAt_cyclic c hc m i hm hi hs' with heq | heq
    · exact Or.inr (Or.inl (heq.trans hB1.symm))
    · exact Or.inr (Or.inr (heq.trans hB2.symm))

/-- Helper toward Proposition 5.16: nonnegative tip coordinate and positive
base coordinates characterize the triangle interior together with its open base. -/
theorem mem_triangle_interior_union_openSegment_of_coords
    (B : AffineBasis (Fin 3) ℝ ℂ) (x : ℂ)
    (hx0 : 0 < B.coord 0 x) (hx2 : 0 < B.coord 2 x) (hx1 : 0 ≤ B.coord 1 x) :
    x ∈ _root_.interior (convexHull ℝ (Set.range B)) ∪ openSegment ℝ (B 0) (B 2) := by
  rcases hx1.eq_or_lt with hzero | hpos
  · right
    have hsum : B.coord 0 x + B.coord 1 x + B.coord 2 x = 1 := by
      simpa only [Fin.sum_univ_three] using B.sum_coord_apply_eq_one x
    have hrep : B.coord 0 x • B 0 + B.coord 1 x • B 1 + B.coord 2 x • B 2 = x := by
      simpa only [Fin.sum_univ_three] using B.linear_combination_coord_eq_self x
    refine ⟨B.coord 0 x, B.coord 2 x, hx0, hx2, ?_, ?_⟩
    · linarith only [hsum, hzero]
    · simpa only [← hzero, zero_smul, add_zero] using hrep
  · left
    rw [B.interior_convexHull]
    intro j
    fin_cases j
    · exact hx0
    · exact hpos
    · exact hx2

/-- Helper toward Proposition 5.16: a point in the triangle interior or open
base has positive base coordinates and nonnegative tip coordinate. -/
theorem coords_of_mem_triangle_interior_union_openSegment
    (B : AffineBasis (Fin 3) ℝ ℂ) (x : ℂ)
    (hx : x ∈ _root_.interior (convexHull ℝ (Set.range B)) ∪
      openSegment ℝ (B 0) (B 2)) :
    0 < B.coord 0 x ∧ 0 ≤ B.coord 1 x ∧ 0 < B.coord 2 x := by
  rcases hx with hx | hx
  · have hp : ∀ j, 0 < B.coord j x := by rwa [B.interior_convexHull] at hx
    exact ⟨hp 0, (hp 1).le, hp 2⟩
  · obtain ⟨s, t, hs, ht, hst, rfl⟩ := hx
    simp only [Convex.combo_affine_apply hst, B.coord_apply_eq,
      B.coord_apply_ne (by decide : (0 : Fin 3) ≠ 2),
      B.coord_apply_ne (by decide : (1 : Fin 3) ≠ 0),
      B.coord_apply_ne (by decide : (1 : Fin 3) ≠ 2),
      B.coord_apply_ne (by decide : (2 : Fin 3) ≠ 0),
      smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
    exact ⟨hs, le_rfl, ht⟩

/-- Helper toward Proposition 5.16: the base line of an affine triangle is
exactly the zero set of its tip coordinate. -/
theorem mem_base_line_iff_coord_eq_zero (B : AffineBasis (Fin 3) ℝ ℂ) (x : ℂ) :
    x ∈ (line[ℝ, B 0, B 2] : Set ℂ) ↔ B.coord 1 x = 0 := by
  constructor
  · intro hx
    obtain ⟨t, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hx
    rw [AffineMap.lineMap_apply_module]
    rw [Convex.combo_affine_apply (show (1 - t) + t = 1 by ring)]
    simp only [B.coord_apply_ne (by decide : (1 : Fin 3) ≠ 0),
      B.coord_apply_ne (by decide : (1 : Fin 3) ≠ 2), smul_zero, add_zero]
  · intro hx
    have hsum : B.coord 0 x + B.coord 1 x + B.coord 2 x = 1 := by
      simpa only [Fin.sum_univ_three] using B.sum_coord_apply_eq_one x
    have hrep : B.coord 0 x • B 0 + B.coord 1 x • B 1 + B.coord 2 x • B 2 = x := by
      simpa only [Fin.sum_univ_three] using B.linear_combination_coord_eq_self x
    apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
    refine ⟨B.coord 2 x, ?_⟩
    rw [AffineMap.lineMap_apply_module]
    have h0 : 1 - B.coord 2 x = B.coord 0 x := by linarith only [hsum, hx]
    simpa only [h0, hx, zero_smul, add_zero] using hrep

/-- Helper toward Proposition 5.16: on the nonnegative side of the base,
distance to its line is monotone in the affine tip coordinate. The proof uses
a contraction parallel to that line and does not require a projection API. -/
theorem infDist_base_le_of_coord_le (B : AffineBasis (Fin 3) ℝ ℂ) (x y : ℂ)
    (hx : 0 ≤ B.coord 1 x) (hxy : B.coord 1 x ≤ B.coord 1 y) :
    Metric.infDist x (line[ℝ, B 0, B 2] : Set ℂ) ≤
      Metric.infDist y (line[ℝ, B 0, B 2] : Set ℂ) := by
  let L : Set ℂ := (line[ℝ, B 0, B 2] : Set ℂ)
  have hL : L.Nonempty := ⟨B 0, left_mem_affineSpan_pair ℝ _ _⟩
  by_cases hy : B.coord 1 y = 0
  · have hx0 : B.coord 1 x = 0 := by linarith only [hx, hxy, hy]
    rw [Metric.infDist_zero_of_mem ((mem_base_line_iff_coord_eq_zero B x).mpr hx0)]
    exact Metric.infDist_nonneg
  have hypos : 0 < B.coord 1 y := lt_of_le_of_ne (hx.trans hxy) (Ne.symm hy)
  let t : ℝ := B.coord 1 x / B.coord 1 y
  have ht0 : 0 ≤ t := div_nonneg hx hypos.le
  have ht1 : t ≤ 1 := (div_le_one hypos).mpr hxy
  have hteq : t * B.coord 1 y = B.coord 1 x := div_mul_cancel₀ _ hy
  apply (Metric.le_infDist hL).mpr
  intro q hq
  have hq0 := (mem_base_line_iff_coord_eq_zero B q).mp hq
  let qx : ℂ := -(t • (y - q)) + x
  have hqx0 : B.coord 1 qx = 0 := by
    change B.coord 1 (-(t • (y - q)) +ᵥ x) = 0
    rw [AffineMap.map_vadd, map_neg, map_smul]
    have hlin : (B.coord 1).linear (y - q) = B.coord 1 y - B.coord 1 q :=
      (B.coord 1).linear_apply_vsub y q
    rw [hlin, hq0, sub_zero]
    change -(t * B.coord 1 y) + B.coord 1 x = 0
    rw [hteq, neg_add_cancel]
  have hqx : qx ∈ L := (mem_base_line_iff_coord_eq_zero B qx).mpr hqx0
  have hdist : dist x qx = t * dist y q := by
    rw [dist_eq_norm, dist_eq_norm]
    have heq : x - qx = t • (y - q) := by dsimp only [qx]; abel
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  calc
    Metric.infDist x L ≤ dist x qx := Metric.infDist_le_dist_of_mem hqx
    _ = t * dist y q := hdist
    _ ≤ dist y q := mul_le_of_le_one_left dist_nonneg ht1

/-- Helper toward Proposition 5.16: if a neighbour triangle at a supporting
tip contains an extra polygon vertex, a vertex in its interior or open base is
visible from the tip. The segment meets the polygon exactly at its endpoints. -/
theorem exists_visible_vertex_of_extra_vertex (c : Polyline) (hc : c.IsCyclicSimple)
    (i : ℕ) (hi : i + 1 < c.points.length)
    (hbound : ∀ m, m < c.points.length → (c.point i).re ≤ (c.point m).re)
    (hnc : ¬ Collinear ℝ ({c.point (if i = 0 then c.points.length - 2 else i - 1),
      c.point i, c.point (i + 1)} : Set ℂ))
    (hextra : ∃ m, m < c.points.length ∧
      c.point m ∈ convexHull ℝ
        ({c.point (if i = 0 then c.points.length - 2 else i - 1), c.point i,
          c.point (i + 1)} : Set ℂ) ∧
      c.point m ∉ ({c.point (if i = 0 then c.points.length - 2 else i - 1),
        c.point i, c.point (i + 1)} : Set ℂ)) :
    let u := c.point (if i = 0 then c.points.length - 2 else i - 1)
    let v := c.point i
    let w := c.point (i + 1)
    ∃ j : ℕ, j + 1 < c.points.length ∧
      c.point j ∈ _root_.interior (convexHull ℝ ({u, v, w} : Set ℂ)) ∪
        openSegment ℝ u w ∧
      c.point j ∉ ({u, v, w} : Set ℂ) ∧
      openSegment ℝ v (c.point j) ⊆ c.inside ∧
      segment ℝ v (c.point j) ∩ c.image = {v, c.point j} ∧
      (∀ l : ℕ, l + 1 < c.points.length →
        c.point l ∈ _root_.interior (convexHull ℝ ({u, v, w} : Set ℂ)) ∪
          openSegment ℝ u w →
        Metric.infDist (c.point l) (line[ℝ, u, w] : Set ℂ) ≤
          Metric.infDist (c.point j) (line[ℝ, u, w] : Set ℂ)) := by
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
  let s : Set ℂ := (c.point '' {m : ℕ | m < c.points.length}) ∩
    (convexHull ℝ (Set.range B) \ ({B 0, B 1, B 2} : Set ℂ))
  have hs : s.Finite := ((Set.finite_lt_nat c.points.length).image c.point).subset
    (fun _ hx => hx.1)
  have hsne : s.Nonempty := by
    obtain ⟨m, hm, hmT, hmne⟩ := hextra
    exact ⟨c.point m, ⟨m, hm, rfl⟩,
      by simpa only [hrange] using hmT, hmne⟩
  obtain ⟨x, hx, hxmax⟩ := Set.exists_min_image s (fun z => -(B.coord 1 z)) hs hsne
  obtain ⟨m, hm, hmx⟩ := hx.1
  change m < c.points.length at hm
  have hxpos := extra_vertex_triangle_pos_coords c hc i hi B rfl rfl rfl m hm
    (by simpa only [hmx] using hx.2.1) (by simpa only [hmx] using hx.2.2)
  rw [hmx] at hxpos
  have hxnon : ∀ j, 0 ≤ B.coord j x := by
    have hxT := hx.2.1
    rwa [B.convexHull_eq_nonneg_coord] at hxT
  have hvertices (l : ℕ) (hl : l < c.points.length)
      (hlT : c.point l ∈ convexHull ℝ (Set.range B)) (hlne : c.point l ≠ B 1) :
      B.coord 1 (c.point l) ≤ B.coord 1 x := by
    by_cases hla : c.point l = B 0
    · rw [hla, B.coord_apply_ne (by decide : (1 : Fin 3) ≠ 0)]
      exact hxnon 1
    by_cases hlb : c.point l = B 2
    · rw [hlb, B.coord_apply_ne (by decide : (1 : Fin 3) ≠ 2)]
      exact hxnon 1
    have hls : c.point l ∈ s := by
      refine ⟨⟨l, hl, rfl⟩, hlT, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact fun h => h.elim hla (fun h => h.elim hlne hlb)
    have hmax := hxmax (c.point l) hls
    linarith only [hmax]
  have hinside := openSegment_tip_subset_inside_of_coord_max c hc i hi B rfl rfl rfl
    hbound x hxpos.1 hxpos.2 (hxnon 1) hvertices
  obtain ⟨j, hj, hjx⟩ : ∃ j, j + 1 < c.points.length ∧ c.point j = x := by
    by_cases hm' : m + 1 < c.points.length
    · exact ⟨m, hm', hmx⟩
    · refine ⟨0, by have := hc.1; omega, ?_⟩
      rw [hc.2.1, ← hmx]
      congr 1
      omega
  change ∃ j, j + 1 < c.points.length ∧
    c.point j ∈ _root_.interior (convexHull ℝ ({a, v, b} : Set ℂ)) ∪
      openSegment ℝ a b ∧
    c.point j ∉ ({a, v, b} : Set ℂ) ∧
    openSegment ℝ v (c.point j) ⊆ c.inside ∧
    segment ℝ v (c.point j) ∩ c.image = {v, c.point j} ∧
    (∀ l : ℕ, l + 1 < c.points.length →
      c.point l ∈ _root_.interior (convexHull ℝ ({a, v, b} : Set ℂ)) ∪
        openSegment ℝ a b →
      Metric.infDist (c.point l) (line[ℝ, a, b] : Set ℂ) ≤
        Metric.infDist (c.point j) (line[ℝ, a, b] : Set ℂ))
  refine ⟨j, hj, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hjx]
    simpa only [hrange, show B 0 = a from rfl, show B 2 = b from rfl] using
      mem_triangle_interior_union_openSegment_of_coords B x
      hxpos.1 hxpos.2 (hxnon 1)
  · rw [hjx]
    exact hx.2.2
  · rw [hjx]
    exact hinside
  · rw [hjx]
    ext z
    constructor
    · rintro ⟨hzseg, hzimage⟩
      by_cases hzv : z = v
      · exact Or.inl hzv
      by_cases hzx : z = x
      · exact Or.inr hzx
      have hzopen := mem_openSegment_of_ne_left_right (Ne.symm hzv) (Ne.symm hzx) hzseg
      exact False.elim ((hinside hzopen).1 hzimage)
    · rintro (rfl | rfl)
      · exact ⟨left_mem_segment ℝ _ _, c.point_mem_image (by omega)⟩
      · exact ⟨right_mem_segment ℝ _ _, hjx ▸ c.point_mem_image (by omega)⟩
  · intro l hl hlT
    rw [hjx]
    have hlcoords := coords_of_mem_triangle_interior_union_openSegment B (c.point l)
      (by simpa only [hrange, show B 0 = a from rfl, show B 2 = b from rfl] using hlT)
    have hlclosed : c.point l ∈ convexHull ℝ (Set.range B) := by
      rw [B.convexHull_eq_nonneg_coord]
      intro n
      fin_cases n
      · exact hlcoords.1.le
      · exact hlcoords.2.1
      · exact hlcoords.2.2.le
    have hlne : c.point l ≠ B 1 := by
      intro heq
      have hz := B.coord_apply_ne (by decide : (0 : Fin 3) ≠ 1)
      rw [heq, hz] at hlcoords
      exact (lt_irrefl 0) hlcoords.1
    exact infDist_base_le_of_coord_le B _ _ hlcoords.2.1
      (hvertices l (by omega) hlclosed hlne)

/-- Helper toward Proposition 5.16: at a supporting noncollinear tip, either
the opposite side is an ear diagonal or the tip sees an extra triangle vertex. -/
theorem ear_or_exists_visible_vertex (c : Polyline) (hc : c.IsCyclicSimple)
    (hlen : 5 ≤ c.points.length) (i : ℕ) (hi : i + 1 < c.points.length)
    (hbound : ∀ m, m < c.points.length → (c.point i).re ≤ (c.point m).re)
    (hnc : ¬ Collinear ℝ ({c.point (if i = 0 then c.points.length - 2 else i - 1),
      c.point i, c.point (i + 1)} : Set ℂ)) :
    let u := c.point (if i = 0 then c.points.length - 2 else i - 1)
    let v := c.point i
    let w := c.point (i + 1)
    (openSegment ℝ u w ⊆ c.inside ∧ segment ℝ u w ∩ c.image = {u, w}) ∨
      ∃ j : ℕ, j + 1 < c.points.length ∧
        c.point j ∈ _root_.interior (convexHull ℝ ({u, v, w} : Set ℂ)) ∪
          openSegment ℝ u w ∧
        c.point j ∉ ({u, v, w} : Set ℂ) ∧
        openSegment ℝ v (c.point j) ⊆ c.inside ∧
        segment ℝ v (c.point j) ∩ c.image = {v, c.point j} ∧
        (∀ l : ℕ, l + 1 < c.points.length →
          c.point l ∈ _root_.interior (convexHull ℝ ({u, v, w} : Set ℂ)) ∪
            openSegment ℝ u w →
          Metric.infDist (c.point l) (line[ℝ, u, w] : Set ℂ) ≤
            Metric.infDist (c.point j) (line[ℝ, u, w] : Set ℂ)) := by
  classical
  by_cases hvertices : ∀ m, m < c.points.length →
      c.point m ∈ convexHull ℝ
        ({c.point (if i = 0 then c.points.length - 2 else i - 1), c.point i,
          c.point (i + 1)} : Set ℂ) →
      c.point m ∈ ({c.point (if i = 0 then c.points.length - 2 else i - 1),
        c.point i, c.point (i + 1)} : Set ℂ)
  · exact Or.inl (ear_of_no_other_vertex c hc hlen i hi hbound hnc hvertices)
  · push Not at hvertices
    exact Or.inr (exists_visible_vertex_of_extra_vertex c hc i hi hbound hnc hvertices)

/-- Helper toward Proposition 5.16: the full maximal-distance visibility
alternative at a lexicographically least polygon vertex, in the exact form
recorded as open in Chart3. Equal maximal heights require no angular choice. -/
theorem ear_or_exists_maximal_visible_vertex (c : Polyline) (hc : c.IsCyclicSimple)
    (hlen : 5 ≤ c.points.length) (i : ℕ) (hi : i + 1 < c.points.length)
    (hmin : ∀ j : ℕ, j + 1 < c.points.length → c.point j ≠ c.point i →
      (c.point i).re < (c.point j).re ∨
        (c.point i).re = (c.point j).re ∧ (c.point i).im < (c.point j).im)
    (hnc : ¬ Collinear ℝ
      ({c.point (if i = 0 then c.points.length - 2 else i - 1),
        c.point i, c.point (i + 1)} : Set ℂ)) :
    let u := c.point (if i = 0 then c.points.length - 2 else i - 1)
    let v := c.point i
    let w := c.point (i + 1)
    let T := convexHull ℝ ({u, v, w} : Set ℂ)
    (openSegment ℝ u w ⊆ c.inside ∧ segment ℝ u w ∩ c.image = {u, w}) ∨
      ∃ j : ℕ, j + 1 < c.points.length ∧
        c.point j ∈ _root_.interior T ∪ openSegment ℝ u w ∧
        (∀ l : ℕ, l + 1 < c.points.length →
          c.point l ∈ _root_.interior T ∪ openSegment ℝ u w →
          Metric.infDist (c.point l) (line[ℝ, u, w] : Set ℂ) ≤
            Metric.infDist (c.point j) (line[ℝ, u, w] : Set ℂ)) ∧
        openSegment ℝ v (c.point j) ⊆ c.inside ∧
        segment ℝ v (c.point j) ∩ c.image = {v, c.point j} := by
  have hbound (m : ℕ) (hm : m < c.points.length) :
      (c.point i).re ≤ (c.point m).re := by
    have main (m : ℕ) (hm : m + 1 < c.points.length) :
        (c.point i).re ≤ (c.point m).re := by
      by_cases heq : c.point m = c.point i
      · exact heq ▸ le_rfl
      · exact (hmin m hm heq).elim le_of_lt (fun h => h.1.le)
    by_cases hm' : m + 1 < c.points.length
    · exact main m hm'
    · rw [show m = c.points.length - 1 by omega, ← hc.2.1]
      exact main 0 (by have := hc.1; omega)
  rcases ear_or_exists_visible_vertex c hc hlen i hi hbound hnc with hear | hvis
  · exact Or.inl hear
  · obtain ⟨j, hj, hjT, hjne, hin, hinter, hmax⟩ := hvis
    exact Or.inr ⟨j, hj, hjT, hmax, hin, hinter⟩

/-- Helper toward Proposition 5.16: a visible vertex other than a tip and
its cyclic neighbours gives the increasing-index form of a polygon diagonal. -/
theorem exists_diagonal_of_visible_nonincident_vertex (c : Polyline)
    (hc : c.IsCyclicSimple) (i j : ℕ)
    (hi : i + 1 < c.points.length) (hj : j + 1 < c.points.length)
    (hne : c.point j ∉
      ({c.point (if i = 0 then c.points.length - 2 else i - 1),
        c.point i, c.point (i + 1)} : Set ℂ))
    (hinside : openSegment ℝ (c.point i) (c.point j) ⊆ c.inside) :
    ∃ a b : ℕ, a + 1 < c.points.length ∧ b + 1 < c.points.length ∧
      a + 1 < b ∧ ¬ (a = 0 ∧ b + 2 = c.points.length) ∧
      openSegment ℝ (c.point a) (c.point b) ⊆ c.inside := by
  have hne0 : c.point j ≠ c.point (if i = 0 then c.points.length - 2 else i - 1) :=
    fun h => hne (Or.inl h)
  have hne1 : c.point j ≠ c.point i := fun h => hne (Or.inr (Or.inl h))
  have hne2 : c.point j ≠ c.point (i + 1) := fun h => hne (Or.inr (Or.inr h))
  have hji : j ≠ i := fun h => hne1 (congrArg c.point h)
  rcases lt_or_gt_of_ne hji with hlt | hgt
  · refine ⟨j, i, hj, hi, ?_, ?_, ?_⟩
    · by_contra hn
      have hij : j = i - 1 := by omega
      apply hne0
      rw [ite_eq_right (by omega : i ≠ 0), hij]
    · rintro ⟨hj0, hilast⟩
      apply hne2
      rw [hj0, show i + 1 = c.points.length - 1 by omega]
      exact hc.2.1
    · simpa only [openSegment_symm] using hinside
  · refine ⟨i, j, hi, hj, ?_, ?_, hinside⟩
    · by_contra hn
      exact hne2 (congrArg c.point (by omega : j = i + 1))
    · rintro ⟨hi0, hjlast⟩
      apply hne0
      rw [ite_eq_left hi0]
      congr 1
      omega

/-- Helper toward Proposition 5.16: every cyclically simple polygon with
at least four distinct cyclic vertices has an interior diagonal. -/
theorem exists_diagonal_cyclic (c : Polyline) (hc : c.IsCyclicSimple)
    (hlen : 5 ≤ c.points.length) :
    ∃ i j : ℕ, i + 1 < c.points.length ∧ j + 1 < c.points.length ∧
      i + 1 < j ∧ ¬ (i = 0 ∧ j + 2 = c.points.length) ∧
      openSegment ℝ (c.point i) (c.point j) ⊆ c.inside := by
  obtain ⟨i, hi, hmin, hnc⟩ := exists_noncollinear_lexicographic_min_vertex c hc
  have hbound (m : ℕ) (hm : m < c.points.length) :
      (c.point i).re ≤ (c.point m).re := by
    have main (m : ℕ) (hm : m + 1 < c.points.length) :
        (c.point i).re ≤ (c.point m).re := by
      by_cases heq : c.point m = c.point i
      · exact heq ▸ le_rfl
      · exact (hmin m hm heq).elim le_of_lt (fun h => h.1.le)
    by_cases hm' : m + 1 < c.points.length
    · exact main m hm'
    · rw [show m = c.points.length - 1 by omega, ← hc.2.1]
      exact main 0 (by omega)
  rcases ear_or_exists_visible_vertex c hc hlen i hi hbound hnc with hear | hvis
  · have hin := hear.1
    by_cases hi0 : i = 0
    · refine ⟨1, c.points.length - 2, by omega, by omega, by omega, by omega, ?_⟩
      simpa only [hi0, ite_true, zero_add, openSegment_symm] using hin
    · simp only [ite_eq_right hi0] at hin
      by_cases hn : i + 2 < c.points.length
      · refine ⟨i - 1, i + 1, by omega, by omega, by omega, ?_, hin⟩
        omega
      · refine ⟨0, i - 1, by omega, by omega, by omega, by omega, ?_⟩
        have heq : c.point (i + 1) = c.point 0 := by
          rw [show i + 1 = c.points.length - 1 by omega, ← hc.2.1]
        simpa only [heq, openSegment_symm] using hin
  · obtain ⟨j, hj, hjT, hjne, hin, hinter, hmax⟩ := hvis
    exact exists_diagonal_of_visible_nonincident_vertex c hc i j hi hj hjne hin

end Polyline
end DirectedDistances.PlanarMap
