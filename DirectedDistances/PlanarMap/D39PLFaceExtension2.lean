/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLFaceExtension




public section
noncomputable section
namespace DirectedDistances.PlanarMap
namespace Polyline
open Set Topology

/-- Helper toward Proposition 5.16: the closed inside and boundary fit strictly
inside an axis-parallel square. This is a coordinate bound, not yet a polygonal
square construction or a chart of the intervening annulus. -/
theorem exists_square_bound_closed_inside (c : Polyline) (hc : c.IsCyclicSimple) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ closure c.inside,
      |z.re| < R ∧ |z.im| < R := by
  have hclosed : c.start = c.finish := by
    rw [← c.point_zero_eq_start, ← c.point_last_eq_finish]
    exact hc.2.1
  obtain ⟨R, hR⟩ := (c.isBounded_inside hclosed).closure.exists_norm_le
  refine ⟨max R 0 + 1, by positivity, fun z hz => ?_⟩
  have hn : ‖z‖ < max R 0 + 1 :=
    lt_of_le_of_lt (hR z hz) (lt_of_le_of_lt (le_max_left R 0) (lt_add_one _))
  exact ⟨(Complex.abs_re_le_norm z).trans_lt hn, (Complex.abs_im_le_norm z).trans_lt hn⟩

/-- Helper toward Proposition 5.16: an upper bound on the real coordinates
of vertices also bounds every point of every edge. -/
theorem re_le_of_mem_image_upper (c : Polyline) (a : ℝ)
    (hpoints : ∀ j, j < c.points.length → (c.point j).re ≤ a)
    {z : ℂ} (hz : z ∈ c.image) : z.re ≤ a := by
  rcases hz with hz | ⟨j, hj, hz⟩
  · rw [Set.mem_singleton_iff] at hz
    rw [hz, ← point_zero_eq_start c]
    exact hpoints 0 (List.length_pos_iff.mpr c.nonempty)
  · obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    calc
      s * (c.point j).re + t * (c.point (j + 1)).re ≤ s * a + t * a :=
        add_le_add (mul_le_mul_of_nonneg_left (hpoints j (by omega)) hs)
          (mul_le_mul_of_nonneg_left (hpoints (j + 1) hj) ht)
      _ = a := by rw [← add_mul, hst, one_mul]

/-- Helper toward Proposition 5.16: the open half-plane to the right of a
supporting vertical line belongs to the outside, even with vertical edges. -/
theorem re_gt_subset_outside (c : Polyline) (hclosed : c.start = c.finish)
    (a : ℝ) (hbound : ∀ z ∈ c.image, z.re ≤ a) :
    {z : ℂ | a < z.re} ⊆ c.outside := by
  let s : Set ℂ := {z : ℂ | a < z.re}
  have havoid : s ⊆ c.imageᶜ := fun z hz hzi => (not_le_of_gt hz) (hbound z hzi)
  obtain ⟨R, hR⟩ := c.exists_radius_exterior_subset_outside hclosed
  let q : ℂ := (a + (|a| + |R| + 1) : ℝ)
  have hqre : q.re = a + (|a| + |R| + 1) := Complex.ofReal_re _
  have hqs : q ∈ s := by
    change a < q.re
    rw [hqre]
    linarith only [abs_nonneg a, abs_nonneg R]
  have hqnorm : R < ‖q‖ := by
    have hn := Complex.re_le_norm q
    rw [hqre] at hn
    linarith only [hn, neg_le_abs a, le_abs_self R]
  rcases c.subset_inside_or_outside_of_isPreconnected hclosed s
      (convex_halfSpace_re_gt a).isPreconnected havoid with hin | hout
  · exact False.elim ((hin hqs).2 (hR q hqnorm).2)
  · exact hout

/-- Helper toward Proposition 5.16: a finite polyline has real-coordinate
extremal vertices, and their bounds hold on its whole geometric image. -/
theorem exists_real_extremal_vertices (c : Polyline) :
    ∃ i j : ℕ, i < c.points.length ∧ j < c.points.length ∧
      ∀ z ∈ c.image, (c.point i).re ≤ z.re ∧ z.re ≤ (c.point j).re := by
  let s : Set ℂ := c.point '' {k : ℕ | k < c.points.length}
  have hs : s.Finite := (Set.finite_lt_nat c.points.length).image c.point
  have hne : s.Nonempty :=
    ⟨c.point 0, 0, List.length_pos_iff.mpr c.nonempty, rfl⟩
  obtain ⟨_, ⟨i, hi, rfl⟩, hmin⟩ := Set.exists_min_image s Complex.re hs hne
  obtain ⟨_, ⟨j, hj, rfl⟩, hmax⟩ := Set.exists_max_image s Complex.re hs hne
  refine ⟨i, j, hi, hj, fun z hz => ⟨?_, ?_⟩⟩
  · exact c.re_le_of_mem_image _ (fun k hk => hmin _ ⟨k, hk, rfl⟩) hz
  · exact c.re_le_of_mem_image_upper _ (fun k hk => hmax _ ⟨k, hk, rfl⟩) hz

/-- Helper toward Proposition 5.16: a cyclically simple polygon has positive
horizontal width; a vertical line cannot contain its entire boundary. -/
theorem real_bounds_strict_cyclic (c : Polyline) (hc : c.IsCyclicSimple)
    (a b : ℝ) (hbound : ∀ z ∈ c.image, a ≤ z.re ∧ z.re ≤ b) : a < b := by
  have hclosed : c.start = c.finish := by
    rw [← c.point_zero_eq_start, ← c.point_last_eq_finish]
    exact hc.2.1
  have hleft := c.re_lt_subset_outside hclosed a (fun z hz => (hbound z hz).1)
  have hright := c.re_gt_subset_outside hclosed b (fun z hz => (hbound z hz).2)
  obtain ⟨z, hz⟩ := c.inside_nonempty_cyclic hc
  have hzlo : a ≤ z.re := le_of_not_gt (fun h => hz.2 (hleft h).2)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (c.isOpen_inside hclosed) z hz
  let w : ℂ := z + (ε / 2 : ℝ)
  have hw : w ∈ c.inside := by
    apply hball
    change dist (z + (ε / 2 : ℝ)) z < ε
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  have hwup : w.re ≤ b := le_of_not_gt (fun h => hw.2 (hright h).2)
  have hwre : w.re = z.re + ε / 2 := by simp only [w, Complex.add_re, Complex.ofReal_re]
  rw [hwre] at hwup
  linarith only [hwup, hzlo, hε]

/-- Helper toward Proposition 5.16: a segment directed strictly left from
its initial point lies strictly left except at that initial point. -/
theorem segment_re_lt_of_ne_left (a b : ℂ) (hab : b.re < a.re)
    {z : ℂ} (hz : z ∈ segment ℝ a b) (hne : z ≠ a) : z.re < a.re := by
  rw [segment_eq_image' ℝ a b] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have htpos : 0 < t := by
    apply lt_of_le_of_ne ht.1
    intro h
    apply hne
    simp only [← h, zero_smul, add_zero]
  simp only [Complex.add_re, Complex.smul_re, Complex.sub_re, smul_eq_mul]
  have hprod := mul_neg_of_pos_of_neg htpos (sub_neg.mpr hab)
  linarith only [hprod]

/-- Helper toward Proposition 5.16: a segment directed strictly right from
its initial point lies strictly right except at that initial point. -/
theorem segment_re_gt_of_ne_left (a b : ℂ) (hab : a.re < b.re)
    {z : ℂ} (hz : z ∈ segment ℝ a b) (hne : z ≠ a) : a.re < z.re := by
  rw [segment_eq_image' ℝ a b] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have htpos : 0 < t := by
    apply lt_of_le_of_ne ht.1
    intro h
    apply hne
    simp only [← h, zero_smul, add_zero]
  simp only [Complex.add_re, Complex.smul_re, Complex.sub_re, smul_eq_mul]
  have hprod := mul_pos htpos (sub_pos.mpr hab)
  linarith only [hprod]

/-- Helper toward Proposition 5.16: any straight slit from a leftmost
boundary point to a strictly leftward point meets the polygon only at its
initial point and lies in the closed outside. -/
theorem left_supporting_slit (c : Polyline) (hc : c.IsCyclicSimple)
    (a b : ℂ) (ha : a ∈ c.image) (hab : b.re < a.re)
    (hbound : ∀ z ∈ c.image, a.re ≤ z.re) :
    segment ℝ a b ∩ c.image = {a} ∧ segment ℝ a b ⊆ closure c.outside := by
  have hclosed : c.start = c.finish := by
    rw [← c.point_zero_eq_start, ← c.point_last_eq_finish]
    exact hc.2.1
  have hout {z : ℂ} (hz : z ∈ segment ℝ a b) (hne : z ≠ a) : z ∈ c.outside :=
    c.re_lt_subset_outside hclosed a.re hbound (segment_re_lt_of_ne_left a b hab hz hne)
  constructor
  · ext z
    constructor
    · intro hz
      apply Set.mem_singleton_iff.mpr
      by_contra hne
      exact (hout hz.1 hne).1 hz.2
    · rintro rfl
      exact ⟨left_mem_segment ℝ _ _, ha⟩
  · intro z hz
    by_cases hza : z = a
    · exact hza ▸ c.image_subset_closure_outside_cyclic hc ha
    · exact subset_closure (hout hz hza)

/-- Helper toward Proposition 5.16: a rightward slit from a rightmost
boundary point also has exactly one boundary contact and lies in the closed
outside. -/
theorem right_supporting_slit (c : Polyline) (hc : c.IsCyclicSimple)
    (a b : ℂ) (ha : a ∈ c.image) (hab : a.re < b.re)
    (hbound : ∀ z ∈ c.image, z.re ≤ a.re) :
    segment ℝ a b ∩ c.image = {a} ∧ segment ℝ a b ⊆ closure c.outside := by
  have hclosed : c.start = c.finish := by
    rw [← c.point_zero_eq_start, ← c.point_last_eq_finish]
    exact hc.2.1
  have hout {z : ℂ} (hz : z ∈ segment ℝ a b) (hne : z ≠ a) : z ∈ c.outside :=
    c.re_gt_subset_outside hclosed a.re hbound (segment_re_gt_of_ne_left a b hab hz hne)
  constructor
  · ext z
    constructor
    · intro hz
      apply Set.mem_singleton_iff.mpr
      by_contra hne
      exact (hout hz.1 hne).1 hz.2
    · rintro rfl
      exact ⟨left_mem_segment ℝ _ _, ha⟩
  · intro z hz
    by_cases hza : z = a
    · exact hza ▸ c.image_subset_closure_outside_cyclic hc ha
    · exact subset_closure (hout hz hza)

/-- Helper toward Proposition 5.16: the closed axis-parallel square is convex. -/
theorem convex_closed_square (R : ℝ) :
    Convex ℝ {z : ℂ | |z.re| ≤ R ∧ |z.im| ≤ R} := by
  have heq : {z : ℂ | |z.re| ≤ R ∧ |z.im| ≤ R} =
      ({z : ℂ | -R ≤ z.re} ∩ {z : ℂ | z.re ≤ R}) ∩
      ({z : ℂ | -R ≤ z.im} ∩ {z : ℂ | z.im ≤ R}) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, abs_le]
  rw [heq]
  exact ((convex_halfSpace_re_ge (-R)).inter (convex_halfSpace_re_le R)).inter
    ((convex_halfSpace_im_ge (-R)).inter (convex_halfSpace_im_le R))

/-- Helper toward Proposition 5.16: there are two disjoint simple straight
slits from real-extremal vertices to opposite sides of a common enclosing
square. Each slit meets the polygon only at its initial vertex, stays in the
closed outside, and stays in the closed square. The far endpoints lie on the
vertical sides, away from the square's corners. -/
theorem exists_disjoint_horizontal_exterior_slits (c : Polyline)
    (hc : c.IsCyclicSimple) :
    ∃ R : ℝ, ∃ i j : ℕ, 0 < R ∧ i < c.points.length ∧ j < c.points.length ∧
      (∀ z ∈ closure c.inside, |z.re| < R ∧ |z.im| < R) ∧
      let a := c.point i
      let b := c.point j
      let l : ℂ := ⟨-R, a.im⟩
      let r : ℂ := ⟨R, b.im⟩
      a.re < b.re ∧ |a.im| < R ∧ |b.im| < R ∧
      (diagonalArc a l).IsSimple ∧ (diagonalArc b r).IsSimple ∧
      (diagonalArc a l).image ∩ c.image = {a} ∧
      (diagonalArc b r).image ∩ c.image = {b} ∧
      Disjoint (diagonalArc a l).image (diagonalArc b r).image ∧
      (diagonalArc a l).image ∪ (diagonalArc b r).image ⊆
        closure c.outside ∩ {z : ℂ | |z.re| ≤ R ∧ |z.im| ≤ R} := by
  obtain ⟨R, hR, hbox⟩ := c.exists_square_bound_closed_inside hc
  obtain ⟨i, j, hi, hj, hbound⟩ := c.exists_real_extremal_vertices
  have ha := c.point_mem_image hi
  have hb := c.point_mem_image hj
  have hab := c.real_bounds_strict_cyclic hc _ _ hbound
  have haR := hbox _ (c.image_subset_closure_inside_cyclic hc ha)
  have hbR := hbox _ (c.image_subset_closure_inside_cyclic hc hb)
  let a := c.point i
  let b := c.point j
  let l : ℂ := ⟨-R, a.im⟩
  let r : ℂ := ⟨R, b.im⟩
  have hla : l.re < a.re := (abs_lt.mp haR.1).1
  have hbr : b.re < r.re := (abs_lt.mp hbR.1).2
  obtain ⟨hlint, hlout⟩ := c.left_supporting_slit hc a l ha hla
    (fun z hz => (hbound z hz).1)
  obtain ⟨hrint, hrout⟩ := c.right_supporting_slit hc b r hb hbr
    (fun z hz => (hbound z hz).2)
  have hlsq : segment ℝ a l ⊆ {z : ℂ | |z.re| ≤ R ∧ |z.im| ≤ R} := by
    apply (convex_closed_square R).segment_subset ⟨haR.1.le, haR.2.le⟩
    exact ⟨by change |-R| ≤ R; rw [abs_neg, abs_of_pos hR], haR.2.le⟩
  have hrsq : segment ℝ b r ⊆ {z : ℂ | |z.re| ≤ R ∧ |z.im| ≤ R} := by
    apply (convex_closed_square R).segment_subset ⟨hbR.1.le, hbR.2.le⟩
    exact ⟨by change |R| ≤ R; rw [abs_of_pos hR], hbR.2.le⟩
  have hdisj : Disjoint (segment ℝ a l) (segment ℝ b r) := by
    apply Set.disjoint_left.mpr
    intro z hzl hzr
    have hzlre : z.re ≤ a.re := by
      by_cases hza : z = a
      · exact hza ▸ le_rfl
      · exact (segment_re_lt_of_ne_left a l hla hzl hza).le
    have hzrre : b.re ≤ z.re := by
      by_cases hzb : z = b
      · exact hzb ▸ le_rfl
      · exact (segment_re_gt_of_ne_left b r hbr hzr hzb).le
    exact (not_le_of_gt hab) (hzrre.trans hzlre)
  refine ⟨R, i, j, hR, hi, hj, hbox, hab, haR.2, hbR.2,
    isSimple_diagonalArc a l (fun h => (ne_of_lt hla) (congrArg Complex.re h).symm),
    isSimple_diagonalArc b r (fun h => (ne_of_lt hbr) (congrArg Complex.re h)), ?_⟩
  rw [(diagonalArc_data a l).2.2.2, (diagonalArc_data b r).2.2.2]
  exact ⟨hlint, hrint, hdisj, fun z hz => hz.elim
    (fun h => ⟨hlout h, hlsq h⟩) (fun h => ⟨hrout h, hrsq h⟩)⟩

/-- Helper toward Proposition 5.16: coordinates of a horizontal segment. -/
theorem mem_horizontal_segment_iff (a b t : ℝ) (hab : a < b) (z : ℂ) :
    z ∈ segment ℝ (⟨a, t⟩ : ℂ) ⟨b, t⟩ ↔
      a ≤ z.re ∧ z.re ≤ b ∧ z.im = t := by
  constructor
  · intro hz
    obtain ⟨s, u, hs, hu, hsu, rfl⟩ := hz
    simp only [Complex.add_re, Complex.smul_re, Complex.add_im, Complex.smul_im,
      smul_eq_mul]
    constructor
    · nlinarith only [mul_nonneg hu (sub_nonneg.mpr hab.le), congrArg (fun x : ℝ => x * a) hsu]
    constructor
    · nlinarith only [mul_nonneg hs (sub_nonneg.mpr hab.le), congrArg (fun x : ℝ => x * b) hsu]
    · rw [← add_mul, hsu, one_mul]
  · rintro ⟨hzlo, hzhi, hzim⟩
    rw [segment_eq_image' ℝ]
    refine ⟨(z.re - a) / (b - a), ⟨div_nonneg (sub_nonneg.mpr hzlo)
      (sub_pos.mpr hab).le, (div_le_one (sub_pos.mpr hab)).mpr (by linarith)⟩, ?_⟩
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, Complex.sub_re, smul_eq_mul]
      field_simp
      ; ring
    · simp only [Complex.add_im, Complex.smul_im, Complex.sub_im, smul_eq_mul,
        sub_self, mul_zero, add_zero]
      exact hzim.symm

/-- Helper toward Proposition 5.16: coordinates of a vertical segment. -/
theorem mem_vertical_segment_iff (a b t : ℝ) (hab : a < b) (z : ℂ) :
    z ∈ segment ℝ (⟨t, a⟩ : ℂ) ⟨t, b⟩ ↔
      a ≤ z.im ∧ z.im ≤ b ∧ z.re = t := by
  constructor
  · intro hz
    obtain ⟨s, u, hs, hu, hsu, rfl⟩ := hz
    simp only [Complex.add_re, Complex.smul_re, Complex.add_im, Complex.smul_im,
      smul_eq_mul]
    constructor
    · nlinarith only [mul_nonneg hu (sub_nonneg.mpr hab.le), congrArg (fun x : ℝ => x * a) hsu]
    constructor
    · nlinarith only [mul_nonneg hs (sub_nonneg.mpr hab.le), congrArg (fun x : ℝ => x * b) hsu]
    · rw [← add_mul, hsu, one_mul]
  · rintro ⟨hzlo, hzhi, hzre⟩
    rw [segment_eq_image' ℝ]
    refine ⟨(z.im - a) / (b - a), ⟨div_nonneg (sub_nonneg.mpr hzlo)
      (sub_pos.mpr hab).le, (div_le_one (sub_pos.mpr hab)).mpr (by linarith)⟩, ?_⟩
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, Complex.sub_re, smul_eq_mul,
        sub_self, mul_zero, add_zero]
      exact hzre.symm
    · simp only [Complex.add_im, Complex.smul_im, Complex.sub_im, smul_eq_mul]
      field_simp
      ; ring

/-- Helper toward Proposition 5.16: the four-edge axis-parallel square with
corners at real and imaginary coordinates `±R`, including the repeated root. -/
@[expose] def enclosingSquare (R : ℝ) : Polyline :=
  ofHead (⟨-R, -R⟩ : ℂ) [⟨R, -R⟩, ⟨R, R⟩, ⟨-R, R⟩, ⟨-R, -R⟩]

/-- Helper toward Proposition 5.16: exact coordinates on the four edges of
the enclosing square, in their cyclic order. -/
theorem enclosingSquare_segmentAt (R : ℝ) (hR : 0 < R) (z : ℂ) :
    (z ∈ (enclosingSquare R).segmentAt 0 ↔ -R ≤ z.re ∧ z.re ≤ R ∧ z.im = -R) ∧
    (z ∈ (enclosingSquare R).segmentAt 1 ↔ -R ≤ z.im ∧ z.im ≤ R ∧ z.re = R) ∧
    (z ∈ (enclosingSquare R).segmentAt 2 ↔ -R ≤ z.re ∧ z.re ≤ R ∧ z.im = R) ∧
    (z ∈ (enclosingSquare R).segmentAt 3 ↔ -R ≤ z.im ∧ z.im ≤ R ∧ z.re = -R) := by
  have h : -R < R := by linarith only [hR]
  refine ⟨mem_horizontal_segment_iff (-R) R (-R) h z,
    mem_vertical_segment_iff (-R) R R h z, ?_, ?_⟩
  · change z ∈ segment ℝ (⟨R, R⟩ : ℂ) ⟨-R, R⟩ ↔ _
    rw [segment_symm]
    exact mem_horizontal_segment_iff (-R) R R h z
  · change z ∈ segment ℝ (⟨-R, R⟩ : ℂ) ⟨-R, -R⟩ ↔ _
    rw [segment_symm]
    exact mem_vertical_segment_iff (-R) R (-R) h z

/-- Helper toward Proposition 5.16: the enclosing square is cyclically simple. -/
theorem enclosingSquare_isCyclicSimple (R : ℝ) (hR : 0 < R) :
    (enclosingSquare R).IsCyclicSimple := by
  have h : -R < R := by linarith only [hR]
  have hle := h.le
  refine ⟨by change 4 ≤ 5; omega, rfl, ?_, ?_, ?_, ?_⟩
  · intro i hi
    change i + 1 < 5 at hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
    all_goals
      norm_num [enclosingSquare, ofHead, point, start, Complex.ext_iff]
      ; linarith only [hR]
  · intro i hi
    change i + 2 < 5 at hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · ext z
      rw [mem_inter_iff, (enclosingSquare_segmentAt R hR z).1,
        (enclosingSquare_segmentAt R hR z).2.1, mem_singleton_iff]
      change (_ ∧ _) ↔ z = (⟨R, -R⟩ : ℂ)
      rw [Complex.ext_iff]
      constructor
      · intro hz; exact ⟨hz.2.2.2, hz.1.2.2⟩
      · rintro ⟨hre, him⟩; rw [hre, him]; exact ⟨⟨hle, le_rfl, rfl⟩, ⟨le_rfl, hle, rfl⟩⟩
    · ext z
      rw [mem_inter_iff, (enclosingSquare_segmentAt R hR z).2.1,
        (enclosingSquare_segmentAt R hR z).2.2.1, mem_singleton_iff]
      change (_ ∧ _) ↔ z = (⟨R, R⟩ : ℂ)
      rw [Complex.ext_iff]
      constructor
      · intro hz; exact ⟨hz.1.2.2, hz.2.2.2⟩
      · rintro ⟨hre, him⟩; rw [hre, him]; exact ⟨⟨hle, le_rfl, rfl⟩, ⟨hle, le_rfl, rfl⟩⟩
    · ext z
      rw [mem_inter_iff, (enclosingSquare_segmentAt R hR z).2.2.1,
        (enclosingSquare_segmentAt R hR z).2.2.2, mem_singleton_iff]
      change (_ ∧ _) ↔ z = (⟨-R, R⟩ : ℂ)
      rw [Complex.ext_iff]
      constructor
      · intro hz; exact ⟨hz.2.2.2, hz.1.2.2⟩
      · rintro ⟨hre, him⟩; rw [hre, him]; exact ⟨⟨le_rfl, hle, rfl⟩, ⟨hle, le_rfl, rfl⟩⟩
  · intro i j hi hj hij hwrap
    change i + 1 < 5 at hi
    change j + 1 < 5 at hj
    have hpairs : (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 3) := by
      change ¬ (i = 0 ∧ j + 2 = 5) at hwrap
      omega
    rcases hpairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · apply Set.disjoint_left.mpr
      intro z hz hw
      have hz' := (enclosingSquare_segmentAt R hR z).1.mp hz
      have hw' := (enclosingSquare_segmentAt R hR z).2.2.1.mp hw
      linarith only [hz'.2.2, hw'.2.2, hR]
    · apply Set.disjoint_left.mpr
      intro z hz hw
      have hz' := (enclosingSquare_segmentAt R hR z).2.1.mp hz
      have hw' := (enclosingSquare_segmentAt R hR z).2.2.2.mp hw
      linarith only [hz'.2.2, hw'.2.2, hR]
  · change (enclosingSquare R).segmentAt 0 ∩ (enclosingSquare R).segmentAt 3 = _
    ext z
    rw [mem_inter_iff, (enclosingSquare_segmentAt R hR z).1,
      (enclosingSquare_segmentAt R hR z).2.2.2, mem_singleton_iff]
    change (_ ∧ _) ↔ z = (⟨-R, -R⟩ : ℂ)
    rw [Complex.ext_iff]
    constructor
    · intro hz; exact ⟨hz.2.2.2, hz.1.2.2⟩
    · rintro ⟨hre, him⟩; rw [hre, him]; exact ⟨⟨le_rfl, hle, rfl⟩, ⟨le_rfl, hle, rfl⟩⟩

/-- Helper toward Proposition 5.16: exact boundary of the enclosing square. -/
theorem mem_enclosingSquare_image_iff (R : ℝ) (hR : 0 < R) (z : ℂ) :
    z ∈ (enclosingSquare R).image ↔
      (-R ≤ z.re ∧ z.re ≤ R) ∧ (-R ≤ z.im ∧ z.im ≤ R) ∧
        (z.re = -R ∨ z.re = R ∨ z.im = -R ∨ z.im = R) := by
  have hle : -R ≤ R := by linarith only [hR]
  constructor
  · rintro (hz | ⟨i, hi, hz⟩)
    · have hz' : z = (⟨-R, -R⟩ : ℂ) := hz
      subst z
      exact ⟨⟨le_rfl, hle⟩, ⟨le_rfl, hle⟩, Or.inl rfl⟩
    · change i + 1 < 5 at hi
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
      · have hh := (enclosingSquare_segmentAt R hR z).1.mp hz
        exact ⟨⟨hh.1, hh.2.1⟩, by rw [hh.2.2]; exact ⟨le_rfl, hle⟩,
          Or.inr (Or.inr (Or.inl hh.2.2))⟩
      · have hh := (enclosingSquare_segmentAt R hR z).2.1.mp hz
        exact ⟨by rw [hh.2.2]; exact ⟨hle, le_rfl⟩, ⟨hh.1, hh.2.1⟩,
          Or.inr (Or.inl hh.2.2)⟩
      · have hh := (enclosingSquare_segmentAt R hR z).2.2.1.mp hz
        exact ⟨⟨hh.1, hh.2.1⟩, by rw [hh.2.2]; exact ⟨hle, le_rfl⟩,
          Or.inr (Or.inr (Or.inr hh.2.2))⟩
      · have hh := (enclosingSquare_segmentAt R hR z).2.2.2.mp hz
        exact ⟨by rw [hh.2.2]; exact ⟨le_rfl, hle⟩, ⟨hh.1, hh.2.1⟩, Or.inl hh.2.2⟩
  · rintro ⟨hre, him, hside⟩
    rcases hside with hl | hr | hb | ht
    · exact Or.inr ⟨3, by change 4 < 5; omega,
        (enclosingSquare_segmentAt R hR z).2.2.2.mpr ⟨him.1, him.2, hl⟩⟩
    · exact Or.inr ⟨1, by change 2 < 5; omega,
        (enclosingSquare_segmentAt R hR z).2.1.mpr ⟨him.1, him.2, hr⟩⟩
    · exact Or.inr ⟨0, by change 1 < 5; omega,
        (enclosingSquare_segmentAt R hR z).1.mpr ⟨hre.1, hre.2, hb⟩⟩
    · exact Or.inr ⟨2, by change 3 < 5; omega,
        (enclosingSquare_segmentAt R hR z).2.2.1.mpr ⟨hre.1, hre.2, ht⟩⟩

/-- Helper toward Proposition 5.16: the lower open half-plane outside a
horizontal supporting line lies in the polygon's outside. -/
theorem im_lt_subset_outside (c : Polyline) (hclosed : c.start = c.finish)
    (a : ℝ) (hbound : ∀ z ∈ c.image, a ≤ z.im) :
    {z : ℂ | z.im < a} ⊆ c.outside := by
  let s : Set ℂ := {z : ℂ | z.im < a}
  have havoid : s ⊆ c.imageᶜ := fun z hz hzi => (not_le_of_gt hz) (hbound z hzi)
  obtain ⟨R, hR⟩ := c.exists_radius_exterior_subset_outside hclosed
  let q : ℂ := ⟨0, a - (|a| + |R| + 1)⟩
  have hqs : q ∈ s := by
    change a - (|a| + |R| + 1) < a
    linarith only [abs_nonneg a, abs_nonneg R]
  have hqnorm : R < ‖q‖ := by
    have hn := Complex.abs_im_le_norm q
    have hneg := neg_le_abs q.im
    change |a - (|a| + |R| + 1)| ≤ ‖q‖ at hn
    change -(a - (|a| + |R| + 1)) ≤ |a - (|a| + |R| + 1)| at hneg
    linarith only [hn, hneg, le_abs_self a, le_abs_self R]
  rcases c.subset_inside_or_outside_of_isPreconnected hclosed s
      (convex_halfSpace_im_lt a).isPreconnected havoid with hin | hout
  · exact False.elim ((hin hqs).2 (hR q hqnorm).2)
  · exact hout

/-- Helper toward Proposition 5.16: the upper open half-plane outside a
horizontal supporting line lies in the polygon's outside. -/
theorem im_gt_subset_outside (c : Polyline) (hclosed : c.start = c.finish)
    (a : ℝ) (hbound : ∀ z ∈ c.image, z.im ≤ a) :
    {z : ℂ | a < z.im} ⊆ c.outside := by
  let s : Set ℂ := {z : ℂ | a < z.im}
  have havoid : s ⊆ c.imageᶜ := fun z hz hzi => (not_le_of_gt hz) (hbound z hzi)
  obtain ⟨R, hR⟩ := c.exists_radius_exterior_subset_outside hclosed
  let q : ℂ := ⟨0, a + (|a| + |R| + 1)⟩
  have hqs : q ∈ s := by
    change a < a + (|a| + |R| + 1)
    linarith only [abs_nonneg a, abs_nonneg R]
  have hqnorm : R < ‖q‖ := by
    have hn := Complex.im_le_norm q
    change a + (|a| + |R| + 1) ≤ ‖q‖ at hn
    linarith only [hn, neg_le_abs a, le_abs_self R]
  rcases c.subset_inside_or_outside_of_isPreconnected hclosed s
      (convex_halfSpace_im_gt a).isPreconnected havoid with hin | hout
  · exact False.elim ((hin hqs).2 (hR q hqnorm).2)
  · exact hout

/-- Helper toward Proposition 5.16: the winding-defined inside of the
cyclic square is exactly its open coordinate square. -/
theorem enclosingSquare_inside (R : ℝ) (hR : 0 < R) :
    (enclosingSquare R).inside =
      {z : ℂ | (-R < z.re ∧ z.re < R) ∧ (-R < z.im ∧ z.im < R)} := by
  let q := enclosingSquare R
  have hq : q.IsCyclicSimple := enclosingSquare_isCyclicSimple R hR
  have hclosed : q.start = q.finish := rfl
  have himage (z : ℂ) (hz : z ∈ q.image) := (mem_enclosingSquare_image_iff R hR z).mp hz
  have hleft := q.re_lt_subset_outside hclosed (-R) (fun z hz => (himage z hz).1.1)
  have hright := q.re_gt_subset_outside hclosed R (fun z hz => (himage z hz).1.2)
  have hbottom := q.im_lt_subset_outside hclosed (-R) (fun z hz => (himage z hz).2.1.1)
  have htop := q.im_gt_subset_outside hclosed R (fun z hz => (himage z hz).2.1.2)
  let B : Set ℂ := {z : ℂ | (-R < z.re ∧ z.re < R) ∧ (-R < z.im ∧ z.im < R)}
  have hsub : q.inside ⊆ B := by
    intro z hz
    have hrelo : -R ≤ z.re := le_of_not_gt (fun h => hz.2 (hleft h).2)
    have hrehi : z.re ≤ R := le_of_not_gt (fun h => hz.2 (hright h).2)
    have himlo : -R ≤ z.im := le_of_not_gt (fun h => hz.2 (hbottom h).2)
    have himhi : z.im ≤ R := le_of_not_gt (fun h => hz.2 (htop h).2)
    have hn : ¬ (z.re = -R ∨ z.re = R ∨ z.im = -R ∨ z.im = R) := by
      intro h
      exact hz.1 ((mem_enclosingSquare_image_iff R hR z).mpr
        ⟨⟨hrelo, hrehi⟩, ⟨himlo, himhi⟩, h⟩)
    exact ⟨⟨lt_of_le_of_ne hrelo (fun h => hn (Or.inl h.symm)),
      lt_of_le_of_ne hrehi (fun h => hn (Or.inr (Or.inl h)))⟩,
      ⟨lt_of_le_of_ne himlo (fun h => hn (Or.inr (Or.inr (Or.inl h.symm)))),
      lt_of_le_of_ne himhi (fun h => hn (Or.inr (Or.inr (Or.inr h))))⟩⟩
  have hconv : Convex ℝ B :=
    ((convex_halfSpace_re_gt (-R)).inter (convex_halfSpace_re_lt R)).inter
      ((convex_halfSpace_im_gt (-R)).inter (convex_halfSpace_im_lt R))
  have havoid : B ⊆ q.imageᶜ := by
    intro z hz hzi
    rcases (himage z hzi).2.2 with hl | hr | hb | ht
    · exact (ne_of_gt hz.1.1) hl
    · exact (ne_of_lt hz.1.2) hr
    · exact (ne_of_gt hz.2.1) hb
    · exact (ne_of_lt hz.2.2) ht
  apply Set.Subset.antisymm hsub
  rcases q.subset_inside_or_outside_of_isPreconnected hclosed B hconv.isPreconnected havoid
      with hin | hout
  · exact hin
  · obtain ⟨z, hz⟩ := q.inside_nonempty_cyclic hq
    exact False.elim (hz.2 (hout (hsub hz)).2)

/-- Helper toward Proposition 5.16: every cyclically simple polygon has a
cyclically simple axis-parallel enclosing square, whose open inside contains
the original closed inside and hence the entire original boundary. -/
theorem exists_enclosingSquare (c : Polyline) (hc : c.IsCyclicSimple) :
    ∃ R : ℝ, 0 < R ∧ (enclosingSquare R).IsCyclicSimple ∧
      closure c.inside ⊆ (enclosingSquare R).inside := by
  obtain ⟨R, hR, hbox⟩ := c.exists_square_bound_closed_inside hc
  refine ⟨R, hR, enclosingSquare_isCyclicSimple R hR, ?_⟩
  intro z hz
  rw [enclosingSquare_inside R hR]
  exact ⟨abs_lt.mp (hbox z hz).1, abs_lt.mp (hbox z hz).2⟩

/-- Helper toward Proposition 5.16: a horizontal left slit from the open
square reaches its boundary only at the left endpoint; all other slit points
are in the square's inside. -/
theorem left_slit_inter_enclosingSquare (R : ℝ) (hR : 0 < R) (a : ℂ)
    (ha : a ∈ (enclosingSquare R).inside) :
    let l : ℂ := ⟨-R, a.im⟩
    segment ℝ a l ∩ (enclosingSquare R).image = {l} ∧
      segment ℝ a l \ {l} ⊆ (enclosingSquare R).inside := by
  rw [enclosingSquare_inside R hR] at ha
  let l : ℂ := ⟨-R, a.im⟩
  have hin {z : ℂ} (hz : z ∈ segment ℝ a l) (hne : z ≠ l) :
      z ∈ (enclosingSquare R).inside := by
    have hz' : z ∈ segment ℝ (⟨-R, a.im⟩ : ℂ) ⟨a.re, a.im⟩ := by
      rw [segment_symm]
      exact hz
    have hcoord := (mem_horizontal_segment_iff (-R) a.re a.im ha.1.1 z).mp hz'
    rw [enclosingSquare_inside R hR]
    refine ⟨⟨lt_of_le_of_ne hcoord.1 ?_, hcoord.2.1.trans_lt ha.1.2⟩, ?_⟩
    · intro h
      exact hne (Complex.ext h.symm hcoord.2.2)
    · rw [hcoord.2.2]
      exact ha.2
  constructor
  · ext z
    constructor
    · rintro ⟨hz, hzi⟩
      apply mem_singleton_iff.mpr
      by_contra hne
      exact (hin hz hne).1 hzi
    · intro hz
      have hzl := mem_singleton_iff.mp hz
      subst z
      refine ⟨right_mem_segment ℝ a l, ?_⟩
      apply (mem_enclosingSquare_image_iff R hR l).mpr
      exact ⟨⟨le_rfl, by change -R ≤ R; linarith only [hR]⟩,
        ⟨ha.2.1.le, ha.2.2.le⟩, Or.inl rfl⟩
  · intro z hz
    exact hin hz.1 hz.2

/-- Helper toward Proposition 5.16: a horizontal right slit from the open
square has exactly its right endpoint on the square boundary. -/
theorem right_slit_inter_enclosingSquare (R : ℝ) (hR : 0 < R) (a : ℂ)
    (ha : a ∈ (enclosingSquare R).inside) :
    let r : ℂ := ⟨R, a.im⟩
    segment ℝ a r ∩ (enclosingSquare R).image = {r} ∧
      segment ℝ a r \ {r} ⊆ (enclosingSquare R).inside := by
  rw [enclosingSquare_inside R hR] at ha
  let r : ℂ := ⟨R, a.im⟩
  have hin {z : ℂ} (hz : z ∈ segment ℝ a r) (hne : z ≠ r) :
      z ∈ (enclosingSquare R).inside := by
    have hz' : z ∈ segment ℝ (⟨a.re, a.im⟩ : ℂ) ⟨R, a.im⟩ := hz
    have hcoord := (mem_horizontal_segment_iff a.re R a.im ha.1.2 z).mp hz'
    rw [enclosingSquare_inside R hR]
    refine ⟨⟨ha.1.1.trans_le hcoord.1, lt_of_le_of_ne hcoord.2.1 ?_⟩, ?_⟩
    · intro h
      exact hne (Complex.ext h hcoord.2.2)
    · rw [hcoord.2.2]
      exact ha.2
  constructor
  · ext z
    constructor
    · rintro ⟨hz, hzi⟩
      apply mem_singleton_iff.mpr
      by_contra hne
      exact (hin hz hne).1 hzi
    · intro hz
      have hzr := mem_singleton_iff.mp hz
      subst z
      refine ⟨right_mem_segment ℝ a r, ?_⟩
      apply (mem_enclosingSquare_image_iff R hR r).mpr
      exact ⟨⟨by change -R ≤ R; linarith only [hR], le_rfl⟩,
        ⟨ha.2.1.le, ha.2.2.le⟩, Or.inr (Or.inl rfl)⟩
  · intro z hz
    exact hin hz.1 hz.2

/-- Helper toward Proposition 5.16: complete enclosing-square and two-slit
geometry for an arbitrary cyclically simple polygon. Both slits are simple and
disjoint, meet the inner and outer boundaries only at the indicated endpoints,
and lie in the closed annulus. Their open parts lie in both open regions. -/
theorem exists_enclosingSquare_disjoint_exterior_slits (c : Polyline)
    (hc : c.IsCyclicSimple) :
    ∃ (R : ℝ) (s t : Polyline), 0 < R ∧
      (enclosingSquare R).IsCyclicSimple ∧
      closure c.inside ⊆ (enclosingSquare R).inside ∧
      s.IsSimple ∧ t.IsSimple ∧ s.start ≠ t.start ∧
      s.image ∩ c.image = {s.start} ∧ t.image ∩ c.image = {t.start} ∧
      s.image ∩ (enclosingSquare R).image = {s.finish} ∧
      t.image ∩ (enclosingSquare R).image = {t.finish} ∧
      Disjoint s.image t.image ∧
      s.image ∪ t.image ⊆ closure c.outside ∩ closure (enclosingSquare R).inside ∧
      s.interior ∪ t.interior ⊆ c.outside ∩ (enclosingSquare R).inside := by
  obtain ⟨R, i, j, hR, hi, hj, hbox, hdata⟩ :=
    c.exists_disjoint_horizontal_exterior_slits hc
  dsimp only at hdata
  obtain ⟨hab, haim, hbim, hs, ht, hsinter, htinter, hdisj, hcontain⟩ := hdata
  let a := c.point i
  let b := c.point j
  let l : ℂ := ⟨-R, a.im⟩
  let r : ℂ := ⟨R, b.im⟩
  let s := diagonalArc a l
  let t := diagonalArc b r
  have hinner : closure c.inside ⊆ (enclosingSquare R).inside := by
    intro z hz
    rw [enclosingSquare_inside R hR]
    exact ⟨abs_lt.mp (hbox z hz).1, abs_lt.mp (hbox z hz).2⟩
  have ha : a ∈ (enclosingSquare R).inside :=
    hinner (c.image_subset_closure_inside_cyclic hc (c.point_mem_image hi))
  have hb : b ∈ (enclosingSquare R).inside :=
    hinner (c.image_subset_closure_inside_cyclic hc (c.point_mem_image hj))
  have hsl := left_slit_inter_enclosingSquare R hR a ha
  have htr := right_slit_inter_enclosingSquare R hR b hb
  have hsdata := diagonalArc_data a l
  have htdata := diagonalArc_data b r
  have hsouter : s.image ∩ (enclosingSquare R).image = {s.finish} := by
    rw [hsdata.2.2.2, hsdata.2.1]
    exact hsl.1
  have htouter : t.image ∩ (enclosingSquare R).image = {t.finish} := by
    rw [htdata.2.2.2, htdata.2.1]
    exact htr.1
  have hclosedcontain : s.image ∪ t.image ⊆
      closure c.outside ∩ closure (enclosingSquare R).inside := by
    intro z hz
    refine ⟨(hcontain hz).1, ?_⟩
    by_cases hzin : z ∈ (enclosingSquare R).inside
    · exact subset_closure hzin
    · have hsq : |z.re| ≤ R ∧ |z.im| ≤ R := (hcontain hz).2
      have hside : z.re = -R ∨ z.re = R ∨ z.im = -R ∨ z.im = R := by
        rw [enclosingSquare_inside R hR] at hzin
        have hre := abs_le.mp hsq.1
        have him := abs_le.mp hsq.2
        by_contra hn
        apply hzin
        exact ⟨⟨lt_of_le_of_ne hre.1 (fun h => hn (Or.inl h.symm)),
          lt_of_le_of_ne hre.2 (fun h => hn (Or.inr (Or.inl h)))⟩,
          ⟨lt_of_le_of_ne him.1 (fun h => hn (Or.inr (Or.inr (Or.inl h.symm)))),
          lt_of_le_of_ne him.2 (fun h => hn (Or.inr (Or.inr (Or.inr h))))⟩⟩
      exact (enclosingSquare R).image_subset_closure_inside_cyclic
        (enclosingSquare_isCyclicSimple R hR)
        ((mem_enclosingSquare_image_iff R hR z).mpr
          ⟨abs_le.mp hsq.1, abs_le.mp hsq.2, hside⟩)
  have hopen (p : Polyline) (hp : p.image ∩ c.image = {p.start})
      (hpout : p.image ⊆ closure c.outside)
      (hpin : p.image \ {p.finish} ⊆ (enclosingSquare R).inside) :
      p.interior ⊆ c.outside ∩ (enclosingSquare R).inside := by
    intro z hz
    have hzstart : z ≠ p.start := by
      intro h
      exact hz.2 (Or.inl h)
    have hzfinish : z ≠ p.finish := by
      intro h
      exact hz.2 (Or.inr h)
    have hznot : z ∉ c.image := by
      intro hzi
      exact hzstart (mem_singleton_iff.mp (hp ▸ ⟨hz.1, hzi⟩))
    have hzout := hpout hz.1
    rw [c.closure_outside_eq_union_image_cyclic hc] at hzout
    exact ⟨hzout.resolve_right hznot, hpin ⟨hz.1, hzfinish⟩⟩
  have hsopen : s.interior ⊆ c.outside ∩ (enclosingSquare R).inside := by
    apply hopen s hsinter (fun z hz => (hcontain (Or.inl hz)).1)
    rw [hsdata.2.2.2, hsdata.2.1]
    exact hsl.2
  have htopen : t.interior ⊆ c.outside ∩ (enclosingSquare R).inside := by
    apply hopen t htinter (fun z hz => (hcontain (Or.inr hz)).1)
    rw [htdata.2.2.2, htdata.2.1]
    exact htr.2
  refine ⟨R, s, t, hR, enclosingSquare_isCyclicSimple R hR, hinner,
    hs, ht, ?_, hsinter, htinter, hsouter, htouter, hdisj, hclosedcontain,
    Set.union_subset hsopen htopen⟩
  intro heq
  exact (ne_of_lt hab) (congrArg Complex.re heq)

/-- Helper toward Proposition 5.16: the closed annulus between two polygon
boundaries is compact whenever the outer polygon is cyclically simple. -/
theorem isCompact_closed_annulus (c q : Polyline) (hq : q.IsCyclicSimple) :
    IsCompact (closure c.outside ∩ closure q.inside) := by
  have hclosed : q.start = q.finish := by
    rw [← q.point_zero_eq_start, ← q.point_last_eq_finish]
    exact hq.2.1
  exact (q.isBounded_inside hclosed).isCompact_closure.inter_left isClosed_closure

/-- Helper toward Proposition 5.16: for strictly nested cyclic polygons,
the inner closed disk, closed annulus and outer closed outside cover the plane.
The two successive overlaps are exactly the respective polygon boundaries;
the inner disk and outer closed outside are disjoint. -/
theorem nested_closed_annulus_cover (c q : Polyline)
    (hc : c.IsCyclicSimple) (hq : q.IsCyclicSimple)
    (hnest : closure c.inside ⊆ q.inside) :
    (closure c.inside ∪ (closure c.outside ∩ closure q.inside)) ∪
        closure q.outside = univ ∧
      closure c.inside ∩ (closure c.outside ∩ closure q.inside) = c.image ∧
      (closure c.outside ∩ closure q.inside) ∩ closure q.outside = q.image ∧
      Disjoint (closure c.inside) (closure q.outside) := by
  have hqclosed : q.start = q.finish := by
    rw [← q.point_zero_eq_start, ← q.point_last_eq_finish]
    exact hq.2.1
  have hcfaces := c.closed_faces_union_inter_cyclic hc
  have hqfaces := q.closed_faces_union_inter_cyclic hq
  have hdisj : Disjoint (closure c.inside) (closure q.outside) := by
    apply Set.disjoint_left.mpr
    intro z hzc hzq
    exact (q.closure_sides_avoid hqclosed).2 hzq (hnest hzc)
  have hqimage : q.image ⊆ closure c.outside := by
    intro z hz
    have hznot : z ∉ closure c.inside := by
      intro hzi
      exact (hnest hzi).1 hz
    have hzfaces : z ∈ closure c.inside ∪ closure c.outside :=
      hcfaces.1.symm ▸ mem_univ z
    exact hzfaces.resolve_left hznot
  refine ⟨?_, ?_, ?_, hdisj⟩
  · apply Set.Subset.antisymm (Set.subset_univ _)
    intro z _
    have hzc : z ∈ closure c.inside ∪ closure c.outside := hcfaces.1.symm ▸ mem_univ z
    have hzq : z ∈ closure q.inside ∪ closure q.outside := hqfaces.1.symm ▸ mem_univ z
    rcases hzc with hzc | hzc
    · exact Or.inl (Or.inl hzc)
    · rcases hzq with hzq | hzq
      · exact Or.inl (Or.inr ⟨hzc, hzq⟩)
      · exact Or.inr hzq
  · apply Set.Subset.antisymm
    · intro z hz
      exact hcfaces.2 ▸ ⟨hz.1, hz.2.1⟩
    · intro z hz
      have hzi := c.image_subset_closure_inside_cyclic hc hz
      exact ⟨hzi, c.image_subset_closure_outside_cyclic hc hz, subset_closure (hnest hzi)⟩
  · apply Set.Subset.antisymm
    · intro z hz
      exact hqfaces.2 ▸ ⟨hz.1.2, hz.2⟩
    · intro z hz
      exact ⟨⟨hqimage hz, q.image_subset_closure_inside_cyclic hq hz⟩,
        q.image_subset_closure_outside_cyclic hq hz⟩


































































end Polyline
end DirectedDistances.PlanarMap
