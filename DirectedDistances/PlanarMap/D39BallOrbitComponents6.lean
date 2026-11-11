/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39BallOrbitComponents5

/-! # Bend neighborhoods for insertion of simple arcs

Helpers toward Proposition 5.16. These supporting results concern the local
the coordinator; no numbered paper result is asserted here. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
namespace Polyline

open Set Topology

/-- Helper toward Proposition 5.16: in a simple open arc, a bend belongs
only to its incoming and outgoing segments. -/
theorem not_mem_segmentAt_of_ne_bend (c : Polyline) (hc : c.IsSimple)
    (i j : ℕ) (hi : i + 2 < c.points.length) (hj : j + 1 < c.points.length)
    (hji : j ≠ i) (hjnext : j ≠ i + 1) :
    c.point (i + 1) ∉ c.segmentAt j := by
  intro hmem
  have hown : c.point (i + 1) ∈ c.segmentAt i := right_mem_segment ℝ _ _
  by_cases hbefore : j < i
  · by_cases hadj : j + 1 = i
    · have hmeet : c.point (i + 1) = c.point i := by
        have hm : c.point (i + 1) ∈ c.segmentAt j ∩ c.segmentAt (j + 1) :=
          ⟨hmem, hadj.symm ▸ hown⟩
        rw [hc.2.1 j (by omega)] at hm
        simpa only [mem_singleton_iff, hadj] using hm
      exact hc.1 i (by omega) hmeet.symm
    · exact Set.disjoint_left.mp (hc.2.2 j i hj (by omega) (by omega)) hmem hown
  · have hnext : c.point (i + 1) ∈ c.segmentAt (i + 1) := left_mem_segment ℝ _ _
    by_cases hadj : j = i + 2
    · have hmeet : c.point (i + 1) = c.point (i + 2) := by
        have hm : c.point (i + 1) ∈ c.segmentAt (i + 1) ∩ c.segmentAt (i + 1 + 1) :=
          ⟨hnext, by simpa only [hadj, Nat.add_assoc] using hmem⟩
        rw [hc.2.1 (i + 1) (by omega)] at hm
        simpa only [mem_singleton_iff, Nat.add_assoc] using hm
      exact hc.1 (i + 1) hi hmeet
    · exact Set.disjoint_left.mp (hc.2.2 (i + 1) j hi hj (by omega)) hnext hmem

/-- Helper toward Proposition 5.16: a sufficiently small ball at an
interior bend of a simple arc meets exactly its two incident segments. -/
theorem exists_pos_ball_image_eq_incident_segments (c : Polyline) (hc : c.IsSimple)
    (i : ℕ) (hi : i + 2 < c.points.length) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Metric.ball (c.point (i + 1)) r,
      (y ∈ c.image ↔ y ∈ c.segmentAt i ∪ c.segmentAt (i + 1)) := by
  classical
  let J := (Finset.range (c.points.length - 1)).filter (fun j => j ≠ i ∧ j ≠ i + 1)
  have hcompact (j : ℕ) : IsCompact (c.segmentAt j) := by
    rw [segmentAt, segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)
  have hclosed : IsClosed (⋃ j ∈ J, c.segmentAt j) :=
    isClosed_biUnion_finset (fun j _ => (hcompact j).isClosed)
  have hnot : c.point (i + 1) ∉ ⋃ j ∈ J, c.segmentAt j := by
    intro hm
    obtain ⟨j, hjJ, hjmem⟩ := mem_iUnion₂.mp hm
    obtain ⟨hjrange, hji, hjnext⟩ := Finset.mem_filter.mp hjJ
    have hjlt : j + 1 < c.points.length := by
      simp only [Finset.mem_range] at hjrange
      omega
    exact c.not_mem_segmentAt_of_ne_bend hc i j hi hjlt hji hjnext hjmem
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hnot)
  refine ⟨r, hr, ?_⟩
  intro y hy
  constructor
  · intro hym
    obtain ⟨j, hj, hyj⟩ : ∃ j, j + 1 < c.points.length ∧ y ∈ c.segmentAt j := by
      rcases hym with hyroot | ⟨j, hj, hyj⟩
      · refine ⟨0, by omega, ?_⟩
        rw [show y = c.point 0 by simpa only [mem_singleton_iff, point_zero_eq_start] using hyroot]
        exact left_mem_segment ℝ _ _
      · exact ⟨j, hj, hyj⟩
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hyj)
    by_cases hjnext : j = i + 1
    · exact Or.inr (hjnext ▸ hyj)
    exact (hball hy (mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr
      ⟨by simp only [Finset.mem_range]; omega, hji, hjnext⟩, hyj⟩)).elim
  · rintro (hyj | hyj)
    · exact c.segmentAt_subset_image (by omega) hyj
    · exact c.segmentAt_subset_image hi hyj

/-- Helper toward Proposition 5.16: a bend ball contained in an open
region meets at most two components of that region minus the arc. -/
theorem exists_two_components_of_local_incident_segments_diff (c : Polyline)
    (U : Set ℂ) (hU : IsOpen U) (v a b : ℂ) (r : ℝ)
    (ha : a ≠ v) (hb : b ≠ v) (hr : 0 < r)
    (hball : Metric.ball v r ⊆ U)
    (himage : ∀ y ∈ Metric.ball v r,
      y ∈ c.image ↔ y ∈ segment ℝ v a ∪ segment ℝ v b) :
    ∃ u w : ℂ, u ∈ U \ c.image ∧ w ∈ U \ c.image ∧
      ∀ z ∈ Metric.ball v r, z ∈ U \ c.image →
        connectedComponentIn (U \ c.image) z = connectedComponentIn (U \ c.image) u ∨
        connectedComponentIn (U \ c.image) z = connectedComponentIn (U \ c.image) w := by
  obtain ⟨L, R, hLc, hRc, hLa, hRa, hLb, hRb, hcover⟩ :=
    exists_connected_vertex_regions v a b r ha hb hr
  have hL : L ⊆ U \ c.image := fun y hy =>
    ⟨hball (hLb hy), fun hym => hLa hy ((himage y (hLb hy)).mp hym)⟩
  have hR : R ⊆ U \ c.image := fun y hy =>
    ⟨hball (hRb hy), fun hym => hRa hy ((himage y (hRb hy)).mp hym)⟩
  obtain ⟨u, hu⟩ := hLc.nonempty
  obtain ⟨w, hw⟩ := hRc.nonempty
  have hLC := hLc.isPreconnected.subset_connectedComponentIn hu hL
  have hRC := hRc.isPreconnected.subset_connectedComponentIn hw hR
  refine ⟨u, w, hL hu, hR hw, ?_⟩
  intro z hz hzU
  let O := connectedComponentIn (U \ c.image) z ∩ Metric.ball v r
  have hopen : IsOpen O :=
    (hU.inter c.isCompact_image.isClosed.isOpen_compl).connectedComponentIn.inter
      Metric.isOpen_ball
  obtain ⟨y, hy, hya, hyb⟩ := exists_mem_open_off_two_edgeLines O hopen
    ⟨z, mem_connectedComponentIn hzU, hz⟩ v (a - v) (b - v)
    (sub_ne_zero.mpr ha) (sub_ne_zero.mpr hb)
  have hzy := connectedComponentIn_eq hy.1
  rcases hcover y hy.2 hya hyb with hyL | hyR
  · exact Or.inl (hzy.trans (connectedComponentIn_eq (hLC hyL)).symm)
  · exact Or.inr (hzy.trans (connectedComponentIn_eq (hRC hyR)).symm)

/-- Helper toward Proposition 5.16: translating the origin along a
supporting line leaves its transverse coordinate unchanged. -/
theorem transverse_sub_eq_of_mem_edgeLine (v x d z : ℂ) (hx : x ∈ edgeLine v d) :
    (star d * (z - x)).im = (star d * (z - v)).im := by
  have heq : star d * (z - x) = star d * (z - v) - star d * (x - v) := by ring
  rw [heq, Complex.sub_im, hx, sub_zero]

/-- Helper toward Proposition 5.16: a strict transverse sign at an
endpoint persists along the open segment from the coordinate origin. -/
theorem transverse_pos_openSegment (v a d x : ℂ)
    (ha : 0 < (star d * (a - v)).im) (hx : x ∈ openSegment ℝ v a) :
    0 < (star d * (x - v)).im := by
  rw [openSegment_eq_image'] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  rw [add_sub_cancel_left, transverse_smul]
  exact mul_pos ht.1 ha

/-- Helper toward Proposition 5.16: for a positive transverse turn of
the two outward rays, connected bend sectors contain matching left and
right germs of the oriented incoming and outgoing segments. -/
theorem exists_bend_sectors_of_cross_pos (v a b : ℂ) (r : ℝ)
    (hr : 0 < r) (hcross : 0 < (star (a - v) * (b - v)).im) :
    ∃ L R : Set ℂ, IsConnected L ∧ IsConnected R ∧
      L ⊆ Metric.ball v r \ (segment ℝ v a ∪ segment ℝ v b) ∧
      R ⊆ Metric.ball v r \ (segment ℝ v a ∪ segment ℝ v b) ∧
      (∀ x ∈ openSegment ℝ v a, x ∈ Metric.ball v r → ∃ s : ℝ, 0 < s ∧
        leftHalfDisc x (v - a) s ⊆ L ∧ rightHalfDisc x (v - a) s ⊆ R) ∧
      (∀ x ∈ openSegment ℝ v b, x ∈ Metric.ball v r → ∃ s : ℝ, 0 < s ∧
        leftHalfDisc x (b - v) s ⊆ L ∧ rightHalfDisc x (b - v) s ⊆ R) := by
  let u := a - v
  let e := b - v
  let L := rightHalfDisc v u r ∪ leftHalfDisc v e r
  let R := leftHalfDisc v u r ∩ rightHalfDisc v e r
  obtain ⟨hRne, hLinter⟩ := halfDisc_sector_intersections_nonempty v u e r hr hcross
  have hLc : IsConnected L :=
    (isConnected_rightHalfDisc v u r (hLinter.mono inter_subset_left)).union hLinter
      (isConnected_leftHalfDisc v e r (hLinter.mono inter_subset_right))
  have hRc : IsConnected R :=
    ((convex_leftHalfDisc v u r).inter (convex_rightHalfDisc v e r)).isConnected hRne
  have haLine : segment ℝ v a ⊆ edgeLine v u :=
    segment_subset_edgeLine v a v (left_mem_segment ℝ _ _)
  have hbLine : segment ℝ v b ⊆ edgeLine v e :=
    segment_subset_edgeLine v b v (left_mem_segment ℝ _ _)
  have hneg : (star e * (a - v)).im < 0 := by
    rw [transverse_swap]
    exact neg_neg_of_pos hcross
  have hLsub : L ⊆ Metric.ball v r \ (segment ℝ v a ∪ segment ℝ v b) := by
    intro z hz
    rcases hz with hzu | hze
    · refine ⟨hzu.1, ?_⟩
      rintro (hza | hzb)
      · exact (ne_of_lt hzu.2) (haLine hza)
      · exact (not_lt_of_ge (transverse_nonneg_segment v b u z hcross.le hzb)) hzu.2
    · refine ⟨hze.1, ?_⟩
      rintro (hza | hzb)
      · have hn := transverse_nonneg_segment v a (-e) z (by
          simpa only [star_neg, neg_mul, Complex.neg_im, neg_nonneg] using hneg.le) hza
        have hn' : (star e * (z - v)).im ≤ 0 := by
          simpa only [star_neg, neg_mul, Complex.neg_im, neg_nonneg] using hn
        exact (not_lt_of_ge hn') hze.2
      · exact (ne_of_gt hze.2) (hbLine hzb)
  have hRsub : R ⊆ Metric.ball v r \ (segment ℝ v a ∪ segment ℝ v b) := by
    intro z hz
    refine ⟨hz.1.1, ?_⟩
    rintro (hza | hzb)
    · exact (ne_of_gt hz.1.2) (haLine hza)
    · exact (ne_of_lt hz.2.2) (hbLine hzb)
  refine ⟨L, R, hLc, hRc, hLsub, hRsub, ?_, ?_⟩
  · intro x hx hxb
    have hxline : x ∈ edgeLine v u := haLine (openSegment_subset_segment ℝ _ _ hx)
    have hxneg : (star e * (x - v)).im < 0 := by
      have hp := transverse_pos_openSegment v a (-e) x (by
        simpa only [star_neg, neg_mul, Complex.neg_im, neg_pos] using hneg) hx
      simpa only [star_neg, neg_mul, Complex.neg_im, neg_pos] using hp
    have hopen : IsOpen (Metric.ball v r ∩ {z : ℂ | (star e * (z - v)).im < 0}) :=
      Metric.isOpen_ball.inter (isOpen_lt (by fun_prop) continuous_const)
    obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds ⟨hxb, hxneg⟩)
    refine ⟨s, hs, ?_, ?_⟩
    · intro z hz
      apply Or.inl
      refine ⟨(hball hz.1).1, ?_⟩
      have hp : 0 < -(star u * (z - x)).im := by
        simpa only [show v - a = -u by dsimp [u]; abel,
          star_neg, neg_mul, Complex.neg_im, mem_ofPred_eq] using hz.2
      rw [transverse_sub_eq_of_mem_edgeLine v x u z hxline] at hp
      exact neg_pos.mp hp
    · intro z hz
      refine ⟨⟨(hball hz.1).1, ?_⟩, hball hz.1⟩
      have hn : -(star u * (z - x)).im < 0 := by
        simpa only [show v - a = -u by dsimp [u]; abel,
          star_neg, neg_mul, Complex.neg_im, mem_ofPred_eq] using hz.2
      rw [transverse_sub_eq_of_mem_edgeLine v x u z hxline] at hn
      exact neg_neg_iff_pos.mp hn
  · intro x hx hxb
    have hxline : x ∈ edgeLine v e := hbLine (openSegment_subset_segment ℝ _ _ hx)
    have hxpos := transverse_pos_openSegment v b u x hcross hx
    have hopen : IsOpen (Metric.ball v r ∩ {z : ℂ | 0 < (star u * (z - v)).im}) :=
      Metric.isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))
    obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds ⟨hxb, hxpos⟩)
    refine ⟨s, hs, ?_, ?_⟩
    · intro z hz
      apply Or.inr
      refine ⟨(hball hz.1).1, ?_⟩
      change 0 < (star e * (z - v)).im
      rw [← transverse_sub_eq_of_mem_edgeLine v x e z hxline]
      exact hz.2
    · intro z hz
      refine ⟨hball hz.1, ⟨(hball hz.1).1, ?_⟩⟩
      change (star e * (z - v)).im < 0
      rw [← transverse_sub_eq_of_mem_edgeLine v x e z hxline]
      exact hz.2

/-- Helper toward Proposition 5.16: two collinear incident segments
meeting only at their common endpoint point in opposite directions. -/
theorem exists_neg_smul_of_incident_segments (v a b : ℂ)
    (ha : a ≠ v) (hb : b ≠ v)
    (hcross : (star (a - v) * (b - v)).im = 0)
    (hmeet : segment ℝ v a ∩ segment ℝ v b = {v}) :
    ∃ t : ℝ, 0 < t ∧ b - v = -(t • (a - v)) := by
  let u := a - v
  let e := b - v
  have hu : u ≠ 0 := sub_ne_zero.mpr ha
  have he : e ≠ 0 := sub_ne_zero.mpr hb
  have hqim : (e / u).im = 0 := by
    rw [Complex.div_im]
    have hc : u.re * e.im - u.im * e.re = 0 := by
      simpa only [Complex.star_def, Complex.mul_im, Complex.conj_re,
        Complex.conj_im, neg_mul, ← sub_eq_add_neg] using hcross
    rw [← sub_div, show e.im * u.re - e.re * u.im = 0 by nlinarith only [hc], zero_div]
  let t : ℝ := (e / u).re
  have heq : e = t • u := by
    have hq : e / u = (t : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im] using hqim
    calc
      e = (e / u) * u := (div_mul_cancel₀ e hu).symm
      _ = (t : ℂ) * u := congrArg (fun z : ℂ => z * u) hq
      _ = t • u := (RCLike.real_smul_eq_coe_mul t u).symm
  have htne : t ≠ 0 := by
    intro ht
    exact he (by rw [heq, ht, zero_smul])
  have htneg : t < 0 := by
    by_contra ht
    have htpos : 0 < t := lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm htne)
    by_cases htle : t ≤ 1
    · have hbm : b ∈ segment ℝ v a := by
        rw [segment_eq_image']
        refine ⟨t, ⟨htpos.le, htle⟩, ?_⟩
        change v + t • u = b
        rw [← heq]
        dsimp [e]
        abel
      have hm : b ∈ ({v} : Set ℂ) := hmeet ▸ ⟨hbm, right_mem_segment ℝ _ _⟩
      exact hb hm
    · have ham : a ∈ segment ℝ v b := by
        rw [segment_eq_image']
        refine ⟨t⁻¹, ⟨inv_nonneg.mpr htpos.le, inv_le_one_of_one_le₀ (le_of_lt (lt_of_not_ge htle))⟩, ?_⟩
        change v + t⁻¹ • e = a
        rw [heq, smul_smul, inv_mul_cancel₀ htne, one_smul]
        dsimp [u]
        abel
      have hm : a ∈ ({v} : Set ℂ) := hmeet ▸ ⟨right_mem_segment ℝ _ _, ham⟩
      exact ha hm
  refine ⟨-t, neg_pos.mpr htneg, ?_⟩
  simpa only [neg_smul, neg_neg] using heq

/-- Helper toward Proposition 5.16: scaling the direction scales its
transverse coordinate by the same real factor. -/
theorem transverse_smul_left (d z : ℂ) (t : ℝ) :
    (star (t • d) * z).im = t * (star d * z).im := by
  simp only [star_smul, star_trivial, smul_mul_assoc, Complex.smul_im, smul_eq_mul]

/-- Helper toward Proposition 5.16: at a collinear simple bend, the two
half-discs match the incoming and outgoing oriented side germs. -/
theorem exists_bend_sectors_of_cross_zero (v a b : ℂ) (r : ℝ)
    (ha : a ≠ v) (hb : b ≠ v) (hr : 0 < r)
    (hcross : (star (a - v) * (b - v)).im = 0)
    (hmeet : segment ℝ v a ∩ segment ℝ v b = {v}) :
    ∃ L R : Set ℂ, IsConnected L ∧ IsConnected R ∧
      L ⊆ Metric.ball v r \ (segment ℝ v a ∪ segment ℝ v b) ∧
      R ⊆ Metric.ball v r \ (segment ℝ v a ∪ segment ℝ v b) ∧
      (∀ x ∈ openSegment ℝ v a, x ∈ Metric.ball v r → ∃ s : ℝ, 0 < s ∧
        leftHalfDisc x (v - a) s ⊆ L ∧ rightHalfDisc x (v - a) s ⊆ R) ∧
      (∀ x ∈ openSegment ℝ v b, x ∈ Metric.ball v r → ∃ s : ℝ, 0 < s ∧
        leftHalfDisc x (b - v) s ⊆ L ∧ rightHalfDisc x (b - v) s ⊆ R) := by
  let u := a - v
  let e := b - v
  have hu : u ≠ 0 := sub_ne_zero.mpr ha
  obtain ⟨t, ht, he⟩ := exists_neg_smul_of_incident_segments v a b ha hb hcross hmeet
  have hself : (star u * u).im = 0 := by
    have hh := transverse_swap u u
    linarith only [hh]
  have hline : segment ℝ v a ∪ segment ℝ v b ⊆ edgeLine v u :=
    union_subset (segment_subset_edgeLine_of_transverse_zero v a u hself)
      (segment_subset_edgeLine_of_transverse_zero v b u hcross)
  let L := rightHalfDisc v u r
  let R := leftHalfDisc v u r
  have hL : L ⊆ Metric.ball v r \ (segment ℝ v a ∪ segment ℝ v b) :=
    fun z hz => ⟨hz.1, fun hzm => (ne_of_lt hz.2) (hline hzm)⟩
  have hR : R ⊆ Metric.ball v r \ (segment ℝ v a ∪ segment ℝ v b) :=
    fun z hz => ⟨hz.1, fun hzm => (ne_of_gt hz.2) (hline hzm)⟩
  have hecoord (z x : ℂ) : (star e * (z - x)).im = -t * (star u * (z - x)).im := by
    change (star (b - v) * (z - x)).im = -t * (star u * (z - x)).im
    rw [he, star_neg, neg_mul, Complex.neg_im, transverse_smul_left, neg_mul]
  refine ⟨L, R,
    isConnected_rightHalfDisc _ _ _ (rightHalfDisc_nonempty _ _ _ hu hr),
    isConnected_leftHalfDisc _ _ _ (leftHalfDisc_nonempty _ _ _ hu hr), hL, hR, ?_, ?_⟩
  · intro x hx hxb
    have hxline := hline (Or.inl (openSegment_subset_segment ℝ _ _ hx))
    obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.mp (Metric.isOpen_ball.mem_nhds hxb)
    refine ⟨s, hs, ?_, ?_⟩
    · intro z hz
      refine ⟨hball hz.1, ?_⟩
      change (star u * (z - v)).im < 0
      have hp : 0 < -(star u * (z - x)).im := by
        simpa only [show v - a = -u by dsimp [u]; abel,
          star_neg, neg_mul, Complex.neg_im, mem_ofPred_eq] using hz.2
      rw [transverse_sub_eq_of_mem_edgeLine v x u z hxline] at hp
      exact neg_pos.mp hp
    · intro z hz
      refine ⟨hball hz.1, ?_⟩
      change 0 < (star u * (z - v)).im
      have hn : -(star u * (z - x)).im < 0 := by
        simpa only [show v - a = -u by dsimp [u]; abel,
          star_neg, neg_mul, Complex.neg_im, mem_ofPred_eq] using hz.2
      rw [transverse_sub_eq_of_mem_edgeLine v x u z hxline] at hn
      exact neg_neg_iff_pos.mp hn
  · intro x hx hxb
    have hxline := hline (Or.inr (openSegment_subset_segment ℝ _ _ hx))
    obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.mp (Metric.isOpen_ball.mem_nhds hxb)
    refine ⟨s, hs, ?_, ?_⟩
    · intro z hz
      refine ⟨hball hz.1, ?_⟩
      change (star u * (z - v)).im < 0
      have hp : 0 < (star e * (z - x)).im := hz.2
      rw [hecoord, transverse_sub_eq_of_mem_edgeLine v x u z hxline] at hp
      nlinarith only [ht, hp]
    · intro z hz
      refine ⟨hball hz.1, ?_⟩
      change 0 < (star u * (z - v)).im
      have hn : (star e * (z - x)).im < 0 := hz.2
      rw [hecoord, transverse_sub_eq_of_mem_edgeLine v x u z hxline] at hn
      nlinarith only [ht, hn]

/-- Helper toward Proposition 5.16: every simple bend, including a zero
turn, has connected sectors matching the side germs on both incident edges. -/
theorem exists_bend_sectors (v a b : ℂ) (r : ℝ)
    (ha : a ≠ v) (hb : b ≠ v) (hr : 0 < r)
    (hmeet : segment ℝ v a ∩ segment ℝ v b = {v}) :
    ∃ L R : Set ℂ, IsConnected L ∧ IsConnected R ∧
      L ⊆ Metric.ball v r \ (segment ℝ v a ∪ segment ℝ v b) ∧
      R ⊆ Metric.ball v r \ (segment ℝ v a ∪ segment ℝ v b) ∧
      (∀ x ∈ openSegment ℝ v a, x ∈ Metric.ball v r → ∃ s : ℝ, 0 < s ∧
        leftHalfDisc x (v - a) s ⊆ L ∧ rightHalfDisc x (v - a) s ⊆ R) ∧
      (∀ x ∈ openSegment ℝ v b, x ∈ Metric.ball v r → ∃ s : ℝ, 0 < s ∧
        leftHalfDisc x (b - v) s ⊆ L ∧ rightHalfDisc x (b - v) s ⊆ R) := by
  rcases lt_trichotomy 0 (star (a - v) * (b - v)).im with hp | hz | hn
  · exact exists_bend_sectors_of_cross_pos v a b r hr hp
  · exact exists_bend_sectors_of_cross_zero v a b r ha hb hr hz.symm hmeet
  · have hpos : 0 < (star (b - v) * (a - v)).im := by
      rw [transverse_swap]
      exact neg_pos.mpr hn
    obtain ⟨L, R, hLc, hRc, hLsub, hRsub, hin, hout⟩ :=
      exists_bend_sectors_of_cross_pos v b a r hr hpos
    refine ⟨R, L, hRc, hLc, ?_, ?_, ?_, ?_⟩
    · simpa only [union_comm] using hRsub
    · simpa only [union_comm] using hLsub
    · intro x hx hxb
      obtain ⟨s, hs, hL, hR⟩ := hout x hx hxb
      refine ⟨s, hs, ?_, ?_⟩
      · simpa only [rightHalfDisc_eq_leftHalfDisc_neg, neg_sub] using hR
      · simpa only [rightHalfDisc_eq_leftHalfDisc_neg, neg_sub] using hL
    · intro x hx hxb
      obtain ⟨s, hs, hL, hR⟩ := hin x hx hxb
      refine ⟨s, hs, ?_, ?_⟩
      · simpa only [rightHalfDisc_eq_leftHalfDisc_neg, neg_sub] using hR
      · simpa only [rightHalfDisc_eq_leftHalfDisc_neg, neg_sub] using hL

/-- Helper toward Proposition 5.16: a simple arc bend inside an open
region has connected left and right regions containing explicit nonempty
side germs from both incident oriented segments, also for collinear bends. -/
theorem exists_bend_sectors_diff (c : Polyline) (hc : c.IsSimple)
    (U : Set ℂ) (hU : IsOpen U) (i : ℕ) (hi : i + 2 < c.points.length)
    (hvU : c.point (i + 1) ∈ U) :
    ∃ L R : Set ℂ, IsConnected L ∧ IsConnected R ∧
      L ⊆ U \ c.image ∧ R ⊆ U \ c.image ∧
      ∃ x ∈ openSegment ℝ (c.point i) (c.point (i + 1)), ∃ s : ℝ, 0 < s ∧
        leftHalfDisc x (c.point (i + 1) - c.point i) s ⊆ L ∧
        rightHalfDisc x (c.point (i + 1) - c.point i) s ⊆ R ∧
      ∃ y ∈ openSegment ℝ (c.point (i + 1)) (c.point (i + 2)), ∃ t : ℝ, 0 < t ∧
        leftHalfDisc y (c.point (i + 2) - c.point (i + 1)) t ⊆ L ∧
        rightHalfDisc y (c.point (i + 2) - c.point (i + 1)) t ⊆ R := by
  obtain ⟨r₀, hr₀, himage⟩ := c.exists_pos_ball_image_eq_incident_segments hc i hi
  obtain ⟨r₁, hr₁, hUball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hvU)
  let r := min r₀ r₁
  have hr : 0 < r := lt_min hr₀ hr₁
  have hballU : Metric.ball (c.point (i + 1)) r ⊆ U :=
    (Metric.ball_subset_ball (min_le_right r₀ r₁)).trans hUball
  have hlocal (z : ℂ) (hz : z ∈ Metric.ball (c.point (i + 1)) r) :
      z ∈ c.image ↔ z ∈ segment ℝ (c.point (i + 1)) (c.point i) ∪
        segment ℝ (c.point (i + 1)) (c.point (i + 2)) := by
    simpa only [segmentAt, segment_symm ℝ (c.point i) (c.point (i + 1)), Nat.add_assoc]
      using himage z (Metric.ball_subset_ball (min_le_left r₀ r₁) hz)
  have hmeet : segment ℝ (c.point (i + 1)) (c.point i) ∩
      segment ℝ (c.point (i + 1)) (c.point (i + 2)) = {c.point (i + 1)} := by
    simpa only [segmentAt, segment_symm ℝ (c.point i) (c.point (i + 1)), Nat.add_assoc]
      using hc.2.1 i hi
  obtain ⟨L, R, hLc, hRc, hL, hR, hin, hout⟩ := exists_bend_sectors
    (c.point (i + 1)) (c.point i) (c.point (i + 2)) r
    (hc.1 i (by omega)) (hc.1 (i + 1) hi).symm hr hmeet
  have hLsub : L ⊆ U \ c.image := fun z hz =>
    ⟨hballU (hL hz).1, fun hzm => (hL hz).2 ((hlocal z (hL hz).1).mp hzm)⟩
  have hRsub : R ⊆ U \ c.image := fun z hz =>
    ⟨hballU (hR hz).1, fun hzm => (hR hz).2 ((hlocal z (hR hz).1).mp hzm)⟩
  have hvcl : c.point (i + 1) ∈ closure (openSegment ℝ (c.point (i + 1)) (c.point i)) :=
    segment_subset_closure_openSegment (left_mem_segment ℝ _ _)
  obtain ⟨x, hxb, hx⟩ := mem_closure_iff.mp hvcl _ Metric.isOpen_ball (Metric.mem_ball_self hr)
  obtain ⟨s, hs, hsL, hsR⟩ := hin x hx hxb
  have hvcl' : c.point (i + 1) ∈ closure (openSegment ℝ (c.point (i + 1)) (c.point (i + 2))) :=
    segment_subset_closure_openSegment (left_mem_segment ℝ _ _)
  obtain ⟨y, hyb, hy⟩ := mem_closure_iff.mp hvcl' _ Metric.isOpen_ball (Metric.mem_ball_self hr)
  obtain ⟨t, ht, htL, htR⟩ := hout y hy hyb
  refine ⟨L, R, hLc, hRc, hLsub, hRsub, x, ?_, s, hs, hsL, hsR, y, hy, t, ht, htL, htR⟩
  simpa only [openSegment_symm] using hx

/-- Helper toward Proposition 5.16: each full open segment of an inserted
arc has a fixed left component and a fixed right component, containing
positive-radius side germs at every point of that segment. -/
theorem exists_side_components_along_openSegment_diff
    (c : Polyline) (hc : c.IsSimple) (U : Set ℂ) (hU : IsOpen U)
    (i : ℕ) (hi : i + 1 < c.points.length)
    (hedge : openSegment ℝ (c.point i) (c.point (i + 1)) ⊆ U) :
    ∃ u v : ℂ, u ∈ U \ c.image ∧ v ∈ U \ c.image ∧
      ∀ x ∈ openSegment ℝ (c.point i) (c.point (i + 1)), ∃ r : ℝ, 0 < r ∧
        leftHalfDisc x (c.point (i + 1) - c.point i) r ⊆ connectedComponentIn (U \ c.image) u ∧
        rightHalfDisc x (c.point (i + 1) - c.point i) r ⊆ connectedComponentIn (U \ c.image) v := by
  classical
  let a := c.point i
  let b := c.point (i + 1)
  let d := b - a
  have hab : a ≠ b := hc.1 i hi
  have hd : d ≠ 0 := sub_ne_zero.mpr hab.symm
  have hex (x : ↥(openSegment ℝ a b)) : ∃ r : ℝ, 0 < r ∧
      Metric.ball (x : ℂ) r ⊆ U ∧ leftHalfDisc x d r ⊆ U \ c.image ∧
        rightHalfDisc x d r ⊆ U \ c.image := by
    have hxa : (x : ℂ) ≠ a := fun he => hab (left_mem_openSegment_iff.mp (he ▸ x.property))
    have hxb : (x : ℂ) ≠ b := fun he => hab (right_mem_openSegment_iff.mp (he ▸ x.property))
    exact c.exists_halfDiscs_subset_diff hc U hU i hi x
      (openSegment_subset_segment ℝ a b x.property) hxa hxb (hedge x.property)
  choose r hr _ hL hR using hex
  let L := ⋃ x : ↥(openSegment ℝ a b), leftHalfDisc x d (r x)
  let R := ⋃ x : ↥(openSegment ℝ a b), rightHalfDisc x d (r x)
  have hline (x y : ↥(openSegment ℝ a b)) : (y : ℂ) ∈ edgeLine x d :=
    segment_subset_edgeLine a b x (openSegment_subset_segment ℝ a b x.property)
      (openSegment_subset_segment ℝ a b y.property)
  have hLc : IsConnected L :=
    isConnected_iUnion_leftHalfDisc_openSegment a b d hd hline r hr
  have hRc : IsConnected R := by
    dsimp only [R]
    simp_rw [rightHalfDisc_eq_leftHalfDisc_neg]
    apply isConnected_iUnion_leftHalfDisc_openSegment a b (-d) (neg_ne_zero.mpr hd) ?_ r hr
    intro x y
    have hxy := hline x y
    change (star d * ((y : ℂ) - x)).im = 0 at hxy
    change (star (-d) * ((y : ℂ) - x)).im = 0
    simpa only [star_neg, neg_mul, Complex.neg_im, neg_eq_zero] using hxy
  have hLsub : L ⊆ U \ c.image := iUnion_subset fun x => hL x
  have hRsub : R ⊆ U \ c.image := iUnion_subset fun x => hR x
  obtain ⟨u, hu⟩ := hLc.nonempty
  obtain ⟨v, hv⟩ := hRc.nonempty
  have hLC := hLc.isPreconnected.subset_connectedComponentIn hu hLsub
  have hRC := hRc.isPreconnected.subset_connectedComponentIn hv hRsub
  refine ⟨u, v, hLsub hu, hRsub hv, ?_⟩
  intro x hx
  let x' : ↥(openSegment ℝ a b) := ⟨x, hx⟩
  exact ⟨r x', hr x', (subset_iUnion (fun x : ↥(openSegment ℝ a b) => leftHalfDisc x d (r x)) x').trans hLC,
    (subset_iUnion (fun x : ↥(openSegment ℝ a b) => rightHalfDisc x d (r x)) x').trans hRC⟩

/-- Helper toward Proposition 5.16: nonempty left germs at the same point
cannot be contained in different connected components. -/
theorem connectedComponentIn_eq_of_leftHalfDisc_subsets
    (S : Set ℂ) (x d u v : ℂ) (r s : ℝ) (hd : d ≠ 0) (hr : 0 < r) (hs : 0 < s)
    (hu : leftHalfDisc x d r ⊆ connectedComponentIn S u)
    (hv : leftHalfDisc x d s ⊆ connectedComponentIn S v) :
    connectedComponentIn S u = connectedComponentIn S v := by
  obtain ⟨z, hz⟩ := leftHalfDisc_nonempty x d (min r s) hd (lt_min hr hs)
  have hzu := hu ⟨Metric.ball_subset_ball (min_le_left r s) hz.1, hz.2⟩
  have hzv := hv ⟨Metric.ball_subset_ball (min_le_right r s) hz.1, hz.2⟩
  exact (connectedComponentIn_eq hzu).trans (connectedComponentIn_eq hzv).symm

/-- Helper toward Proposition 5.16: nonempty right germs at the same
point cannot be contained in different connected components. -/
theorem connectedComponentIn_eq_of_rightHalfDisc_subsets
    (S : Set ℂ) (x d u v : ℂ) (r s : ℝ) (hd : d ≠ 0) (hr : 0 < r) (hs : 0 < s)
    (hu : rightHalfDisc x d r ⊆ connectedComponentIn S u)
    (hv : rightHalfDisc x d s ⊆ connectedComponentIn S v) :
    connectedComponentIn S u = connectedComponentIn S v := by
  apply connectedComponentIn_eq_of_leftHalfDisc_subsets S x (-d) u v r s
    (neg_ne_zero.mpr hd) hr hs
  · simpa only [rightHalfDisc_eq_leftHalfDisc_neg] using hu
  · simpa only [rightHalfDisc_eq_leftHalfDisc_neg] using hv

/-- Helper toward Proposition 5.16: open segments of a simple arc lie
in its interior, including the first and last open segments. -/
theorem openSegment_subset_interior_of_isSimple (c : Polyline) (hc : c.IsSimple)
    (i : ℕ) (hi : i + 1 < c.points.length) :
    openSegment ℝ (c.point i) (c.point (i + 1)) ⊆ c.interior := by
  intro x hx
  have hxa : x ≠ c.point i := fun he => hc.1 i hi (left_mem_openSegment_iff.mp (he ▸ hx))
  have hxb : x ≠ c.point (i + 1) := fun he => hc.1 i hi (right_mem_openSegment_iff.mp (he ▸ hx))
  have hxseg := openSegment_subset_segment ℝ _ _ hx
  refine ⟨c.segmentAt_subset_image hi hxseg, ?_⟩
  intro hend
  rcases c.segmentAt_endpoint_of_arc_endpoint hc (by omega) i hi hxseg hend with ha | hb
  · exact hxa ha
  · exact hxb hb

/-- Helper toward Proposition 5.16: an interior bend vertex of a simple
arc lies in its interior, rather than at either arc endpoint. -/
theorem bend_mem_interior_of_isSimple (c : Polyline) (hc : c.IsSimple)
    (i : ℕ) (hi : i + 2 < c.points.length) : c.point (i + 1) ∈ c.interior := by
  have hm : c.point (i + 1) ∈ c.segmentAt i := right_mem_segment ℝ _ _
  refine ⟨c.segmentAt_subset_image (by omega) hm, ?_⟩
  rintro (hs | hf)
  · have hz := c.segmentAt_index_eq_zero_of_start_mem hc (by omega) (by omega)
      (show c.start ∈ c.segmentAt (i + 1) from hs ▸ left_mem_segment ℝ _ _)
    omega
  · have hz := c.segmentAt_index_last_of_finish_mem hc (by omega) (by omega)
      (show c.finish ∈ c.segmentAt i from hf ▸ hm)
    omega

/-- Helper toward Proposition 5.16: the left component and the right
component propagate through every bend of a simple inserted arc. Every
regular point admits side germs in the same two fixed components. -/
theorem exists_side_components_diff (c : Polyline) (hc : c.IsSimple)
    (hlen : 2 ≤ c.points.length) (U : Set ℂ) (hU : IsOpen U)
    (hinterior : c.interior ⊆ U) :
    ∃ u v : ℂ, u ∈ U \ c.image ∧ v ∈ U \ c.image ∧
      ∀ i : ℕ, i + 1 < c.points.length →
      ∀ x ∈ openSegment ℝ (c.point i) (c.point (i + 1)), ∃ r : ℝ, 0 < r ∧
        leftHalfDisc x (c.point (i + 1) - c.point i) r ⊆ connectedComponentIn (U \ c.image) u ∧
        rightHalfDisc x (c.point (i + 1) - c.point i) r ⊆ connectedComponentIn (U \ c.image) v := by
  classical
  let J := Fin (c.points.length - 1)
  have hex (j : J) : ∃ u v : ℂ, u ∈ U \ c.image ∧ v ∈ U \ c.image ∧
      ∀ x ∈ openSegment ℝ (c.point j.val) (c.point (j.val + 1)), ∃ r : ℝ, 0 < r ∧
        leftHalfDisc x (c.point (j.val + 1) - c.point j.val) r ⊆ connectedComponentIn (U \ c.image) u ∧
        rightHalfDisc x (c.point (j.val + 1) - c.point j.val) r ⊆ connectedComponentIn (U \ c.image) v := by
    apply c.exists_side_components_along_openSegment_diff hc U hU j.val (by have := j.isLt; omega)
    exact (c.openSegment_subset_interior_of_isSimple hc j.val (by have := j.isLt; omega)).trans hinterior
  choose u v hu hv hg using hex
  let j₀ : J := ⟨0, by omega⟩
  have heq : ∀ i : ℕ, ∀ hi : i + 1 < c.points.length,
      connectedComponentIn (U \ c.image) (u ⟨i, by omega⟩) = connectedComponentIn (U \ c.image) (u j₀) ∧
      connectedComponentIn (U \ c.image) (v ⟨i, by omega⟩) = connectedComponentIn (U \ c.image) (v j₀) := by
    intro i
    induction i with
    | zero => intro hi; exact ⟨rfl, rfl⟩
    | succ i ih =>
      intro hi
      let j : J := ⟨i, by omega⟩
      let k : J := ⟨i + 1, by omega⟩
      have hip := ih (by omega)
      obtain ⟨L, R, hLc, hRc, hLsub, hRsub, x, hx, s, hs, hsL, hsR,
        y, hy, t, ht, htL, htR⟩ := c.exists_bend_sectors_diff hc U hU i (by omega)
          (hinterior (c.bend_mem_interior_of_isSimple hc i (by omega)))
      obtain ⟨l, hl⟩ := hLc.nonempty
      obtain ⟨r, hr⟩ := hRc.nonempty
      have hLC := hLc.isPreconnected.subset_connectedComponentIn hl hLsub
      have hRC := hRc.isPreconnected.subset_connectedComponentIn hr hRsub
      obtain ⟨sx, hsx, hxL, hxR⟩ := hg j x hx
      obtain ⟨sy, hsy, hyL, hyR⟩ := hg k y hy
      have hdx : c.point (i + 1) - c.point i ≠ 0 := sub_ne_zero.mpr (hc.1 i (by omega)).symm
      have hdy : c.point (i + 2) - c.point (i + 1) ≠ 0 :=
        sub_ne_zero.mpr (hc.1 (i + 1) (by omega)).symm
      have hux := connectedComponentIn_eq_of_leftHalfDisc_subsets (U \ c.image)
        x _ (u j) l sx s hdx hsx hs hxL (hsL.trans hLC)
      have hvx := connectedComponentIn_eq_of_rightHalfDisc_subsets (U \ c.image)
        x _ (v j) r sx s hdx hsx hs hxR (hsR.trans hRC)
      have huy := connectedComponentIn_eq_of_leftHalfDisc_subsets (U \ c.image)
        y _ (u k) l sy t hdy hsy ht hyL (htL.trans hLC)
      have hvy := connectedComponentIn_eq_of_rightHalfDisc_subsets (U \ c.image)
        y _ (v k) r sy t hdy hsy ht hyR (htR.trans hRC)
      exact ⟨(huy.trans hux.symm).trans hip.1, (hvy.trans hvx.symm).trans hip.2⟩
  refine ⟨u j₀, v j₀, hu j₀, hv j₀, ?_⟩
  intro i hi x hx
  obtain ⟨r, hr, hL, hR⟩ := hg ⟨i, by omega⟩ x hx
  exact ⟨r, hr, (heq i hi).1 ▸ hL, (heq i hi).2 ▸ hR⟩

/-- Helper toward Proposition 5.16: an arbitrary bent simple arc whose
interior lies in a connected open region and whose endpoints lie outside
that region leaves at most two components. The representatives may coincide. -/
theorem exists_two_components_diff (c : Polyline) (hc : c.IsSimple)
    (hlen : 2 ≤ c.points.length) (U : Set ℂ) (hU : IsOpen U) (hUconn : IsConnected U)
    (hinterior : c.interior ⊆ U) (hstart : c.start ∉ U) (hfinish : c.finish ∉ U) :
    ∃ u v : ℂ, u ∈ U \ c.image ∧ v ∈ U \ c.image ∧
      ∀ z ∈ U \ c.image,
        connectedComponentIn (U \ c.image) z = connectedComponentIn (U \ c.image) u ∨
        connectedComponentIn (U \ c.image) z = connectedComponentIn (U \ c.image) v := by
  obtain ⟨u, v, hu, hv, hg⟩ := c.exists_side_components_diff hc hlen U hU hinterior
  refine ⟨u, v, hu, hv, ?_⟩
  intro z hz
  obtain ⟨i, hi, x, hx, _, s, hs, hside⟩ := c.exists_side_germ_subset_component_diff
    hc hlen U hU hUconn hinterior hstart hfinish z hz
  obtain ⟨r, hr, hL, hR⟩ := hg i hi x hx
  have hd : c.point (i + 1) - c.point i ≠ 0 := sub_ne_zero.mpr (hc.1 i hi).symm
  rcases hside with hside | hside
  · exact Or.inl (connectedComponentIn_eq_of_leftHalfDisc_subsets (U \ c.image)
      x _ z u s r hd hs hr hside hL)
  · exact Or.inr (connectedComponentIn_eq_of_rightHalfDisc_subsets (U \ c.image)
      x _ z v s r hd hs hr hside hR)

end Polyline

namespace PLDrawing

/-- Helper toward Proposition 5.16: insertion of an arbitrary simple PL
arc with vertex endpoints and interior in a geometric face leaves at most
two components of that face, with no restriction on the number of bends. -/
theorem exists_two_components_face_diff_arc
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (F : P.Face) (c : Polyline) (hc : c.IsSimple) (hlen : 2 ≤ c.points.length)
    (a b : V) (hstart : c.start = P.pos a) (hfinish : c.finish = P.pos b)
    (hinterior : c.interior ⊆ F.val) :
    ∃ u v : ℂ, u ∈ F.val \ c.image ∧ v ∈ F.val \ c.image ∧
      ∀ z ∈ F.val \ c.image,
        connectedComponentIn (F.val \ c.image) z = connectedComponentIn (F.val \ c.image) u ∨
        connectedComponentIn (F.val \ c.image) z = connectedComponentIn (F.val \ c.image) v := by
  apply c.exists_two_components_diff hc hlen F.val
    (P.face_open_frontier_subset_image hvert F).1
    (P.face_isPathConnected hvert F).isConnected hinterior
  · intro hs
    exact P.face_subset_compl F hs (Or.inl ⟨a, hstart.symm⟩)
  · intro hf
    exact P.face_subset_compl F hf (Or.inl ⟨b, hfinish.symm⟩)

end PLDrawing

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: adding precisely one dart pair,
preserving the old positions and arcs, adds exactly the new arc to the
geometric drawing image. -/
theorem plImage_eq_union_of_edge_insertion
    {V : Type*} (B' B : D39FiniteBall) (vert' : B'.D → V) (vert : B.D → V)
    (P' : PLDrawing B'.D V B'.map.edgeInv B'.map.rot vert')
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (newDart : B.D) (ι : B'.D ↪ B.D)
    (himage : ∀ d : B.D, d ∈ Set.range ι ↔ d ≠ newDart ∧ d ≠ B.map.edgeInv newDart)
    (hpos : ∀ v : V, P.pos v = P'.pos v)
    (harcs : ∀ d : B'.D, P.arc (ι d) = P'.arc d) :
    P.image = P'.image ∪ (P.arc newDart).image := by
  ext z
  constructor
  · rintro (⟨v, hv⟩ | ⟨d, hd⟩)
    · exact Or.inl (Or.inl ⟨v, (hpos v).symm.trans hv⟩)
    · by_cases he : d = newDart
      · exact Or.inr (he ▸ hd)
      by_cases hf : d = B.map.edgeInv newDart
      · apply Or.inr
        simpa only [hf, P.arc_flip, Polyline.image_reverse_transfer] using hd
      obtain ⟨e, rfl⟩ := (himage d).mpr ⟨he, hf⟩
      exact Or.inl (Or.inr ⟨e, (harcs e) ▸ hd⟩)
  · rintro ((⟨v, hv⟩ | ⟨d, hd⟩) | hd)
    · exact Or.inl ⟨v, (hpos v).trans hv⟩
    · exact Or.inr ⟨ι d, (harcs d).symm ▸ hd⟩
    · exact Or.inr ⟨newDart, hd⟩

end D39FiniteBall

namespace PLDrawing

/-- Helper toward Proposition 5.16: after an exact image insertion,
the components of an old face minus the inserted arc are actual new
drawing faces. This is equality of component sets, not only containment. -/
theorem exists_face_eq_component_face_diff
    {D' D V : Type*} {flip' : D' → D'} {rot' : Equiv.Perm D'} {vert' : D' → V}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P' : PLDrawing D' V flip' rot' vert') (P : PLDrawing D V flip rot vert)
    (hvert : Function.Surjective vert) (c : Polyline)
    (himage : P.image = P'.image ∪ c.image) (F : P'.Face)
    (z : ℂ) (hz : z ∈ F.val \ c.image) :
    ∃ H : P.Face, H.val = connectedComponentIn (F.val \ c.image) z := by
  have hS : F.val \ c.image ⊆ P.imageᶜ := by
    intro x hx hxP
    rw [himage] at hxP
    exact hxP.elim (P'.face_subset_compl F hx.1) hx.2
  obtain ⟨H, hzH⟩ := (P.faces_cover_compl z).mpr (hS hz)
  have hHconn := (P.face_isPathConnected hvert H).isConnected.isPreconnected
  have hHold : H.val ⊆ P'.imageᶜ := by
    intro x hx hxold
    apply P.face_subset_compl H hx
    rw [himage]
    exact Or.inl hxold
  have hHF : H.val ⊆ F.val := by
    obtain ⟨w, _, hF⟩ := F.property
    rw [hF] at hz ⊢
    rw [connectedComponentIn_eq hz.1]
    exact hHconn.subset_connectedComponentIn hzH hHold
  have hHS : H.val ⊆ F.val \ c.image := by
    intro x hx
    refine ⟨hHF hx, ?_⟩
    intro hxc
    apply P.face_subset_compl H hx
    rw [himage]
    exact Or.inr hxc
  refine ⟨H, Set.Subset.antisymm ?_ ?_⟩
  · exact hHconn.subset_connectedComponentIn hzH hHS
  · obtain ⟨w, _, hH⟩ := H.property
    rw [hH] at hzH ⊢
    rw [connectedComponentIn_eq hzH]
    exact connectedComponentIn_mono z hS

end PLDrawing

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: every component created inside the
old face by an edge insertion is exactly the left face of the new dart
or the left face of its reversal. These two faces may coincide here;
distinctness and rotation-orbit matching are separate obligations. -/
theorem component_face_diff_eq_plDartFace_or_flip_of_edge_insertion
    {V : Type*} (B' B : D39FiniteBall) (vert' : B'.D → V) (vert : B.D → V)
    (P' : PLDrawing B'.D V B'.map.edgeInv B'.map.rot vert')
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert' : Function.Surjective vert') (hvert : Function.Surjective vert)
    (newDart : B.D) (ι : B'.D ↪ B.D)
    (himage : ∀ d : B.D, d ∈ Set.range ι ↔ d ≠ newDart ∧ d ≠ B.map.edgeInv newDart)
    (hpos : ∀ v : V, P.pos v = P'.pos v)
    (harcs : ∀ d : B'.D, P.arc (ι d) = P'.arc d)
    (F : P'.Face) (hinterior : (P.arc newDart).interior ⊆ F.val)
    (z : ℂ) (hz : z ∈ F.val \ (P.arc newDart).image) :
    connectedComponentIn (F.val \ (P.arc newDart).image) z =
        (B.plDartFace vert P hvert newDart).val ∨
      connectedComponentIn (F.val \ (P.arc newDart).image) z =
        (B.plDartFace vert P hvert (B.map.edgeInv newDart)).val := by
  have him := plImage_eq_union_of_edge_insertion B' B vert' vert P' P newDart ι himage hpos harcs
  obtain ⟨H, hH⟩ := P'.exists_face_eq_component_face_diff P hvert (P.arc newDart) him F z hz
  have hstart : (P.arc newDart).start ∉ F.val := by
    intro hs
    apply P'.face_subset_compl F hs
    exact Or.inl ⟨vert newDart, (hpos _).symm.trans (P.arc_start newDart).symm⟩
  have hfinish : (P.arc newDart).finish ∉ F.val := by
    intro hf
    apply P'.face_subset_compl F hf
    exact Or.inl ⟨vert (B.map.edgeInv newDart), (hpos _).symm.trans (P.arc_finish newDart).symm⟩
  obtain ⟨i, hi, x, hx, _, hxcl⟩ := (P.arc newDart).exists_openSegment_mem_closure_component_diff
    (P.arc_simple newDart) F.val (P'.face_open_frontier_subset_image hvert' F).1
    (P'.face_isPathConnected hvert' F).isConnected hinterior
    ((P.arc newDart).interior_nonempty_of_isSimple (P.arc_simple newDart) (P.arc_length newDart))
    hstart hfinish z hz
  rw [← hH] at hxcl
  rcases (P.mem_closure_face_openSegment_iff_dartBorders hvert newDart H hi hx).mp hxcl with hd | hf
  · exact Or.inl (hH.symm.trans (congrArg Subtype.val ((B.plDartFace_eq_iff vert P hvert newDart H).mpr hd)).symm)
  · exact Or.inr (hH.symm.trans (congrArg Subtype.val
      ((B.plDartFace_eq_iff vert P hvert (B.map.edgeInv newDart) H).mpr hf)).symm)

/-- Helper toward Proposition 5.16: the old face minus an inserted arc
is exactly the union of the new dart's left face and its reversal's left
face. Both are actual components of that relative complement, although
their distinctness in the non-bridge case is not asserted here. -/
theorem face_diff_eq_union_plDartFaces_of_edge_insertion
    {V : Type*} (B' B : D39FiniteBall) (vert' : B'.D → V) (vert : B.D → V)
    (P' : PLDrawing B'.D V B'.map.edgeInv B'.map.rot vert')
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert' : Function.Surjective vert') (hvert : Function.Surjective vert)
    (newDart : B.D) (ι : B'.D ↪ B.D)
    (himage : ∀ d : B.D, d ∈ Set.range ι ↔ d ≠ newDart ∧ d ≠ B.map.edgeInv newDart)
    (hpos : ∀ v : V, P.pos v = P'.pos v)
    (harcs : ∀ d : B'.D, P.arc (ι d) = P'.arc d)
    (F : P'.Face) (hinterior : (P.arc newDart).interior ⊆ F.val) :
    F.val \ (P.arc newDart).image =
      (B.plDartFace vert P hvert newDart).val ∪
        (B.plDartFace vert P hvert (B.map.edgeInv newDart)).val := by
  have him := plImage_eq_union_of_edge_insertion B' B vert' vert P' P newDart ι himage hpos harcs
  have hsub (H : P.Face) (w : ℂ) (hwH : w ∈ H.val) (hwF : w ∈ F.val) :
      H.val ⊆ F.val \ (P.arc newDart).image := by
    have hHold : H.val ⊆ P'.imageᶜ := by
      intro x hx hxold
      apply P.face_subset_compl H hx
      rw [him]
      exact Or.inl hxold
    have hHF : H.val ⊆ F.val := by
      obtain ⟨q, _, hF⟩ := F.property
      rw [hF] at hwF ⊢
      rw [connectedComponentIn_eq hwF]
      exact (P.face_isPathConnected hvert H).isConnected.isPreconnected.subset_connectedComponentIn hwH hHold
    intro x hx
    refine ⟨hHF hx, ?_⟩
    intro hxc
    apply P.face_subset_compl H hx
    rw [him]
    exact Or.inr hxc
  let c := P.arc newDart
  have hi : 0 + 1 < c.points.length := by
    have hh : 2 ≤ c.points.length := P.arc_length newDart
    omega
  let x := midpoint ℝ (c.point 0) (c.point 1)
  have hx : x ∈ openSegment ℝ (c.point 0) (c.point 1) := midpoint_mem_openSegment _ _
  have hxF := hinterior (c.openSegment_subset_interior_of_isSimple (P.arc_simple newDart) 0 hi hx)
  obtain ⟨s, hs, hFball⟩ := Metric.mem_nhds_iff.mp
    ((P'.face_open_frontier_subset_image hvert' F).1.mem_nhds hxF)
  have hd : c.point 1 - c.point 0 ≠ 0 := sub_ne_zero.mpr ((P.arc_simple newDart).1 0 hi).symm
  let L := B.plDartFace vert P hvert newDart
  let R := B.plDartFace vert P hvert (B.map.edgeInv newDart)
  have hLb : P.dartBorders newDart L := (B.plDartFace_eq_iff vert P hvert newDart L).mp rfl
  have hRb : P.dartBorders (B.map.edgeInv newDart) R :=
    (B.plDartFace_eq_iff vert P hvert (B.map.edgeInv newDart) R).mp rfl
  obtain ⟨rL, hrL, hLball⟩ := P.exists_ball_left_subset_of_dartBorders hvert newDart L hLb hi hx
  obtain ⟨rR, hrR, hRball⟩ := P.exists_ball_right_subset_of_dartBorders_flip hvert newDart R hRb hi hx
  obtain ⟨l, hl⟩ := Polyline.leftHalfDisc_nonempty x (c.point 1 - c.point 0)
    (min rL s) hd (lt_min hrL hs)
  obtain ⟨r, hr⟩ := Polyline.rightHalfDisc_nonempty x (c.point 1 - c.point 0)
    (min rR s) hd (lt_min hrR hs)
  have hlL : l ∈ L.val := hLball l (Metric.ball_subset_ball (min_le_left rL s) hl.1) hl.2
  have hlF : l ∈ F.val := hFball (Metric.ball_subset_ball (min_le_right rL s) hl.1)
  have hrR' : r ∈ R.val := hRball r (Metric.ball_subset_ball (min_le_left rR s) hr.1) hr.2
  have hrF : r ∈ F.val := hFball (Metric.ball_subset_ball (min_le_right rR s) hr.1)
  apply Set.Subset.antisymm
  · intro z hz
    have hzc := mem_connectedComponentIn hz
    rcases component_face_diff_eq_plDartFace_or_flip_of_edge_insertion B' B vert' vert P' P
      hvert' hvert newDart ι himage hpos harcs F hinterior z hz with hL | hR
    · exact Or.inl (hL ▸ hzc)
    · exact Or.inr (hR ▸ hzc)
  · exact Set.union_subset (hsub L l hlL hlF) (hsub R r hrR' hrF)

/-- Helper toward Proposition 5.16: actual representatives of the two
possibly coincident relative components can be chosen so that their
component sets are precisely the new dart's left and right faces. -/
theorem exists_components_eq_plDartFaces_of_edge_insertion
    {V : Type*} (B' B : D39FiniteBall) (vert' : B'.D → V) (vert : B.D → V)
    (P' : PLDrawing B'.D V B'.map.edgeInv B'.map.rot vert')
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert' : Function.Surjective vert') (hvert : Function.Surjective vert)
    (newDart : B.D) (ι : B'.D ↪ B.D)
    (himage : ∀ d : B.D, d ∈ Set.range ι ↔ d ≠ newDart ∧ d ≠ B.map.edgeInv newDart)
    (hpos : ∀ v : V, P.pos v = P'.pos v)
    (harcs : ∀ d : B'.D, P.arc (ι d) = P'.arc d)
    (F : P'.Face) (hinterior : (P.arc newDart).interior ⊆ F.val) :
    ∃ u v : ℂ, u ∈ F.val \ (P.arc newDart).image ∧ v ∈ F.val \ (P.arc newDart).image ∧
      connectedComponentIn (F.val \ (P.arc newDart).image) u =
        (B.plDartFace vert P hvert newDart).val ∧
      connectedComponentIn (F.val \ (P.arc newDart).image) v =
        (B.plDartFace vert P hvert (B.map.edgeInv newDart)).val := by
  have him := plImage_eq_union_of_edge_insertion B' B vert' vert P' P newDart ι himage hpos harcs
  have heq := face_diff_eq_union_plDartFaces_of_edge_insertion B' B vert' vert P' P
    hvert' hvert newDart ι himage hpos harcs F hinterior
  let L := B.plDartFace vert P hvert newDart
  let R := B.plDartFace vert P hvert (B.map.edgeInv newDart)
  obtain ⟨u, hu⟩ := (P.face_isPathConnected hvert L).nonempty
  obtain ⟨v, hv⟩ := (P.face_isPathConnected hvert R).nonempty
  have huS : u ∈ F.val \ (P.arc newDart).image := heq ▸ (Or.inl hu)
  have hvS : v ∈ F.val \ (P.arc newDart).image := heq ▸ (Or.inr hv)
  obtain ⟨H, hH⟩ := P'.exists_face_eq_component_face_diff P hvert (P.arc newDart) him F u huS
  obtain ⟨K, hK⟩ := P'.exists_face_eq_component_face_diff P hvert (P.arc newDart) him F v hvS
  have hHL : H = L := P.faces_eq_of_mem (hH.symm ▸ mem_connectedComponentIn huS) hu
  have hKR : K = R := P.faces_eq_of_mem (hK.symm ▸ mem_connectedComponentIn hvS) hv
  exact ⟨u, v, huS, hvS, hH.symm.trans (congrArg Subtype.val hHL),
    hK.symm.trans (congrArg Subtype.val hKR)⟩

end D39FiniteBall

/- OPEN local strengthening. The proved bend sectors contain matching side
germs and suffice for the arbitrary bent-arc bound. This file does not
yet identify the sectors as two DISTINCT components of the small ball
itself. The exact outstanding statement (comments only) is:

  Polyline.exists_exactly_two_components_ball_diff_near_bend
    (c : Polyline) (hc : c.IsSimple) (i : ℕ) (hi : i + 2 < c.points.length) :
    ∃ r : ℝ, 0 < r ∧ ∃ u v : ℂ,
      u ∈ Metric.ball (c.point (i + 1)) r \ c.image ∧
      v ∈ Metric.ball (c.point (i + 1)) r \ c.image ∧
      connectedComponentIn (Metric.ball (c.point (i + 1)) r \ c.image) u ≠
        connectedComponentIn (Metric.ball (c.point (i + 1)) r \ c.image) v ∧
      (∀ z ∈ Metric.ball (c.point (i + 1)) r \ c.image,
        connectedComponentIn (Metric.ball (c.point (i + 1)) r \ c.image) z =
          connectedComponentIn (Metric.ball (c.point (i + 1)) r \ c.image) u ∨
        connectedComponentIn (Metric.ball (c.point (i + 1)) r \ c.image) z =
          connectedComponentIn (Metric.ball (c.point (i + 1)) r \ c.image) v) ∧
      (∃ x ∈ openSegment ℝ (c.point i) (c.point (i + 1)), ∃ s : ℝ, 0 < s ∧
        Polyline.leftHalfDisc x (c.point (i + 1) - c.point i) s ⊆
          connectedComponentIn (Metric.ball (c.point (i + 1)) r \ c.image) u ∧
        Polyline.rightHalfDisc x (c.point (i + 1) - c.point i) s ⊆
          connectedComponentIn (Metric.ball (c.point (i + 1)) r \ c.image) v) ∧
      (∃ y ∈ openSegment ℝ (c.point (i + 1)) (c.point (i + 2)), ∃ t : ℝ, 0 < t ∧
        Polyline.leftHalfDisc y (c.point (i + 2) - c.point (i + 1)) t ⊆
          connectedComponentIn (Metric.ball (c.point (i + 1)) r \ c.image) u ∧
        Polyline.rightHalfDisc y (c.point (i + 2) - c.point (i + 1)) t ⊆
          connectedComponentIn (Metric.ball (c.point (i + 1)) r \ c.image) v)

Three routes examined for this local strengthening:
1. Explicit transverse sectors: implemented all turn signs and matching
   germs. Distinct local components still need a relative separation
   argument; connected disjoint sector subsets alone do not prove it.
2. Reuse cyclic vertex components: the imported local incident-segment
   theorem proves an upper bound; cyclic distinctness uses global winding
   separation, which does not apply to the open arc's whole complement.
3. Close the two-edge chain and use exists_polygonal_separation: an added
   endpoint-only return arc and its exclusion from the small ball must
   still be constructed, including the collinear case. No return arc is
   assumed as an extra premise.

OPEN non-bridge insertion: distinctness of the two named faces and the
rotation-compatible orbit matching remain. All image and geometric
component identifications above are proved without either assertion.
Full original binders retained; hU1old is the intended induction
hypothesis, not a premise of any proved result in this file:

  D39FiniteBall.plDartFace_sameCycle_of_edge_insertion
    {V : Type*} (B' B : D39FiniteBall)
    (vert' : B'.D → V) (vert : B.D → V)
    (P' : PLDrawing B'.D V B'.map.edgeInv B'.map.rot vert')
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert' : Function.Surjective vert') (hvert : Function.Surjective vert)
    (hconn' : ∀ d e : B'.D, Relation.EqvGen
      (fun x y => B'.map.rot x = y ∨ B'.map.edgeInv x = y) d e)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (newDart : B.D) (ι : B'.D ↪ B.D)
    (himage : ∀ d : B.D, d ∈ Set.range ι ↔
      d ≠ newDart ∧ d ≠ B.map.edgeInv newDart)
    (hflip : ∀ d : B'.D, ι (B'.map.edgeInv d) = B.map.edgeInv (ι d))
    (hvertι : ∀ d : B'.D, vert (ι d) = vert' d)
    (hpos : ∀ v : V, P.pos v = P'.pos v)
    (harcs : ∀ d : B'.D, P.arc (ι d) = P'.arc d)
    (F' : P'.Face) (hinterior : (P.arc newDart).interior ⊆ F'.val)
    (hU1old : ∀ d e : B'.D,
      B'.plDartFace vert' P' hvert' d = B'.plDartFace vert' P' hvert' e →
      B'.map.faceSucc.SameCycle d e)
    (d e : B.D)
    (hface : B.plDartFace vert P hvert d = B.plDartFace vert P hvert e) :
    B.map.faceSucc.SameCycle d e

  D39FiniteBall.plDartFace_new_ne_flip_of_nonbridge_edge_insertion
    {V : Type*} (B' B : D39FiniteBall)
    (vert' : B'.D → V) (vert : B.D → V)
    (P' : PLDrawing B'.D V B'.map.edgeInv B'.map.rot vert')
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert' : Function.Surjective vert') (hvert : Function.Surjective vert)
    (hconn' : ∀ d e : B'.D, Relation.EqvGen
      (fun x y => B'.map.rot x = y ∨ B'.map.edgeInv x = y) d e)
    (newDart : B.D) (ι : B'.D ↪ B.D)
    (himage : ∀ d : B.D, d ∈ Set.range ι ↔
      d ≠ newDart ∧ d ≠ B.map.edgeInv newDart)
    (hflip : ∀ d : B'.D, ι (B'.map.edgeInv d) = B.map.edgeInv (ι d))
    (hvertι : ∀ d : B'.D, vert (ι d) = vert' d)
    (hpos : ∀ v : V, P.pos v = P'.pos v)
    (harcs : ∀ d : B'.D, P.arc (ι d) = P'.arc d)
    (F' : P'.Face) (hinterior : (P.arc newDart).interior ⊆ F'.val) :
    B.plDartFace vert P hvert newDart ≠
      B.plDartFace vert P hvert (B.map.edgeInv newDart)

Three routes examined for the remaining orbit matching:
1. Relative components: proved exact face union and component identities.
   These give a geometric assignment, but do not show the named faces
   distinct or that each successor-orbit fiber has just one element.
2. Permutation splices: inspected insertAfter_apply_left/right and
   insertAfterFresh_orbit_count in PermutationSplice.lean, and
   ccwSuccessor_insert_preserve in SlopeAngularOrder.lean. The old/new
   drawing rotation data still need to be converted into the exact
   two-endpoint splice formula and its orbit splitting. Fresh insertion
   preserving orbit count does not itself establish that splitting.
3. Polygonal separation: exists_polygonal_separation requires an actual
   simple return arc in the old drawing with endpoint-only intersection.
   Old map connectivity has not yet been turned into that arc and into
   opposite-side witnesses for the new faces. The winding extraction in
   D39BallOrbitComponents4 needs a nonzero-winding closed walk and does
   not supply those witnesses from distinct orbit labels alone.

No geometric Euler equality, Schoenflies theorem, U1/U2, or local
distinctness conclusion is assumed by the proved declarations.
remain the coordinator's responsibility. No paper-completion claim. -/

end DirectedDistances.PlanarMap

end

