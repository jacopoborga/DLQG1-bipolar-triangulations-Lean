/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PolygonalSeparation6
import Mathlib.Topology.LocallyConstant.Basic

/-! # Approaching a polygon from its complement

Helpers toward Proposition 5.16. The nearest-point arguments here do not
require simplicity or closedness. Global connectedness remains a separate
obligation. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap
namespace Polyline

open Topology

/-- Helper toward Proposition 5.16: distance to a finite polyline attains its
minimum on the image. -/
theorem exists_nearest_image_point (c : Polyline) (z : ℂ) :
    ∃ q ∈ c.image, ∀ y ∈ c.image, dist z q ≤ dist z y := by
  exact c.isCompact_image.exists_isMinOn ⟨c.start, Or.inl rfl⟩
    (continuous_const.dist continuous_id).continuousOn

/-- Helper toward Proposition 5.16: the open ball about a complementary point
with radius its distance to a nearest image point avoids the entire image. -/
theorem ball_nearest_image_subset_compl (c : Polyline) (z q : ℂ)
    (hmin : ∀ y ∈ c.image, dist z q ≤ dist z y) :
    Metric.ball z (dist z q) ⊆ c.imageᶜ := by
  intro y hy hyimage
  exact (not_lt_of_ge (hmin y hyimage)) (by
    simpa only [Metric.mem_ball, dist_comm] using hy)

/-- Helper toward Proposition 5.16: the open segment from a point of the
complement to a nearest image point avoids the image. -/
theorem openSegment_nearest_image_subset_compl (c : Polyline) (z q : ℂ)
    (hz : z ∉ c.image) (hq : q ∈ c.image)
    (hmin : ∀ y ∈ c.image, dist z q ≤ dist z y) :
    openSegment ℝ z q ⊆ c.imageᶜ := by
  have hne : z ≠ q := fun h => hz (h ▸ hq)
  have hd : 0 < dist z q := dist_pos.mpr hne
  intro y hy
  rw [openSegment_eq_image' ℝ z q] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  apply ball_nearest_image_subset_compl c z q hmin
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos ht.1, ← dist_eq_norm, dist_comm q z]
  exact (mul_lt_mul_of_pos_right ht.2 hd).trans_eq (one_mul _)

/-- Helper toward Proposition 5.16: every complementary point can be joined
by a straight segment in the complement to a point arbitrarily close to the
image. The same nearest image point works for every positive radius. -/
theorem exists_segment_to_image_neighborhood (c : Polyline) (z : ℂ)
    (hz : z ∉ c.image) :
    ∃ q ∈ c.image, (∀ y ∈ c.image, dist z q ≤ dist z y) ∧
      ∀ ε : ℝ, 0 < ε → ∃ w : ℂ,
        dist w q < ε ∧ segment ℝ z w ⊆ c.imageᶜ := by
  obtain ⟨q, hq, hmin⟩ := exists_nearest_image_point c z
  have hne : z ≠ q := fun h => hz (h ▸ hq)
  have hd : 0 < dist z q := dist_pos.mpr hne
  refine ⟨q, hq, hmin, ?_⟩
  intro ε hε
  let t : ℝ := min (1 / 2) (ε / (2 * dist z q))
  have htpos : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
  have htone : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have htε : t * dist z q < ε := by
    have htle : t ≤ ε / (2 * dist z q) := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_right htle hd.le
    have heq : ε / (2 * dist z q) * dist z q = ε / 2 := by
      field_simp
    rw [heq] at hmul
    linarith
  let w : ℂ := q + t • (z - q)
  have hwq : dist w q = t * dist z q := by
    change dist (q + t • (z - q)) q = _
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos htpos, ← dist_eq_norm]
  have hwz : dist w z = (1 - t) * dist z q := by
    have heq : w - z = (1 - t) • (q - z) := by
      change q + t • (z - q) - z = (1 - t) • (q - z)
      simp only [sub_smul, one_smul, smul_sub]
      abel
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr htone), ← dist_eq_norm, dist_comm q z]
  refine ⟨w, hwq ▸ htε, ?_⟩
  apply Set.Subset.trans ((convex_ball z (dist z q)).segment_subset ?_ ?_)
    (ball_nearest_image_subset_compl c z q hmin)
  · simpa only [Metric.mem_ball, dist_self] using hd
  · rw [Metric.mem_ball, hwz]
    nlinarith only [htpos, hd]

/-- Helper toward Proposition 5.16: the component of every complementary point
contains points arbitrarily close to one fixed nearest image point. -/
theorem exists_component_points_near_image (c : Polyline) (z : ℂ)
    (hz : z ∉ c.image) :
    ∃ q ∈ c.image, ∀ ε : ℝ, 0 < ε → ∃ w ∈ connectedComponentIn c.imageᶜ z,
      dist w q < ε ∧ segment ℝ z w ⊆ connectedComponentIn c.imageᶜ z := by
  obtain ⟨q, hq, _, hnear⟩ := exists_segment_to_image_neighborhood c z hz
  refine ⟨q, hq, ?_⟩
  intro ε hε
  obtain ⟨w, hw, hseg⟩ := hnear ε hε
  have hsub : segment ℝ z w ⊆ connectedComponentIn c.imageᶜ z :=
    (convex_segment z w).isPreconnected.subset_connectedComponentIn
      (left_mem_segment ℝ z w) hseg
  exact ⟨w, hsub (right_mem_segment ℝ z w), hw, hsub⟩

/-- Helper toward Proposition 5.16: the closure of every complementary
component meets the polygonal image, at a nearest point. -/
theorem exists_image_mem_closure_component (c : Polyline) (z : ℂ)
    (hz : z ∉ c.image) :
    ∃ q ∈ c.image, q ∈ closure (connectedComponentIn c.imageᶜ z) := by
  obtain ⟨q, hq, hnear⟩ := exists_component_points_near_image c z hz
  refine ⟨q, hq, Metric.mem_closure_iff.mpr ?_⟩
  intro ε hε
  obtain ⟨w, hw, hd, _⟩ := hnear ε hε
  exact ⟨w, hw, by simpa only [dist_comm] using hd⟩

/-- Helper toward Proposition 5.16: every connected component of the
complement of a closed polyline lies entirely in one winding side. -/
theorem component_subset_inside_or_outside (c : Polyline)
    (hclosed : c.start = c.finish) (z : ℂ) :
    connectedComponentIn c.imageᶜ z ⊆ c.inside ∨
      connectedComponentIn c.imageᶜ z ⊆ c.outside := by
  apply IsPreconnected.subset_or_subset (isOpen_inside c hclosed)
    (isOpen_outside c hclosed) (disjoint_inside_outside c)
  · rw [inside_union_outside]
    exact connectedComponentIn_subset _ _
  · exact isPreconnected_connectedComponentIn

/-- Helper toward Proposition 5.16: the component of an inside point remains
inside. -/
theorem component_subset_inside (c : Polyline)
    (hclosed : c.start = c.finish) (z : ℂ) (hz : z ∈ c.inside) :
    connectedComponentIn c.imageᶜ z ⊆ c.inside := by
  rcases component_subset_inside_or_outside c hclosed z with h | h
  · exact h
  · have hzout := h (mem_connectedComponentIn hz.1)
    exact False.elim (hz.2 hzout.2)

/-- Helper toward Proposition 5.16: the component of an outside point remains
outside. -/
theorem component_subset_outside (c : Polyline)
    (hclosed : c.start = c.finish) (z : ℂ) (hz : z ∈ c.outside) :
    connectedComponentIn c.imageᶜ z ⊆ c.outside := by
  rcases component_subset_inside_or_outside c hclosed z with h | h
  · have hzin := h (mem_connectedComponentIn hz.1)
    exact False.elim (hzin.2 hz.2)
  · exact h

/-- Helper toward Proposition 5.16: the angle sum, restricted to the
complement, is a locally constant function. -/
theorem isLocallyConstant_angleSum_compl (c : Polyline)
    (hclosed : c.start = c.finish) :
    IsLocallyConstant (fun z : ↥(c.imageᶜ) => c.angleSum z) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro z
  obtain ⟨ε, hε, hconst⟩ := angleSum_locallyConstant c hclosed z z.property
  refine ⟨Subtype.val ⁻¹' Metric.ball (z : ℂ) ε,
    Metric.isOpen_ball.preimage continuous_subtype_val, ?_, ?_⟩
  · simpa only [Set.mem_preimage, Metric.mem_ball, dist_self] using hε
  · intro w hw
    exact hconst w w.property hw

/-- Helper toward Proposition 5.16: the angle sum is constant on every
preconnected subset of the complement of a closed polyline. -/
theorem angleSum_eq_of_isPreconnected (c : Polyline)
    (hclosed : c.start = c.finish) (s : Set ℂ) (hs : IsPreconnected s)
    (hsub : s ⊆ c.imageᶜ) (z w : ℂ) (hz : z ∈ s) (hw : w ∈ s) :
    c.angleSum z = c.angleSum w := by
  have hpre : IsPreconnected ((Subtype.val : ↥(c.imageᶜ) → ℂ) ⁻¹' s) := by
    apply IsInducing.subtypeVal.isPreconnected_image.mp
    rwa [Subtype.image_preimage_coe, Set.inter_eq_right.mpr hsub]
  exact (isLocallyConstant_angleSum_compl c hclosed).apply_eq_of_isPreconnected
    hpre (x := ⟨z, hsub hz⟩) (y := ⟨w, hsub hw⟩) hz hw

/-- Helper toward Proposition 5.16: angle sum is constant on each component
of the complement, with value equal to that at its base point. -/
theorem angleSum_eq_on_component (c : Polyline)
    (hclosed : c.start = c.finish) (z : ℂ) (hz : z ∉ c.image)
    (w : ℂ) (hw : w ∈ connectedComponentIn c.imageᶜ z) :
    c.angleSum w = c.angleSum z := by
  exact angleSum_eq_of_isPreconnected c hclosed _ isPreconnected_connectedComponentIn
    (connectedComponentIn_subset _ _) w z hw (mem_connectedComponentIn hz)

/-- Helper toward Proposition 5.16: at every interior edge point there is one
common radius for two nonempty connected sides, on each of which angle sum is
constant; their constant values differ by one. -/
theorem exists_constant_edge_sides_cyclic (c : Polyline)
    (hc : c.IsCyclicSimple) (i : ℕ) (hi : i + 1 < c.points.length)
    (x : ℂ) (hx : x ∈ c.segmentAt i) (hxi : x ≠ c.point i)
    (hxi1 : x ≠ c.point (i + 1)) :
    ∃ r : ℝ, 0 < r ∧ ∃ a b : ℝ,
      IsConnected (leftHalfDisc x (c.point (i + 1) - c.point i) r) ∧
      IsConnected (rightHalfDisc x (c.point (i + 1) - c.point i) r) ∧
      (∀ z ∈ leftHalfDisc x (c.point (i + 1) - c.point i) r,
        z ∉ c.image ∧ c.angleSum z = a) ∧
      (∀ z ∈ rightHalfDisc x (c.point (i + 1) - c.point i) r,
        z ∉ c.image ∧ c.angleSum z = b) ∧ |a - b| = 1 := by
  have hclosed : c.start = c.finish := by
    rw [← point_zero_eq_start c, ← point_last_eq_finish c]
    exact hc.2.1
  obtain ⟨rl, hrl, hdl⟩ := exists_leftHalfDisc_disjoint_image_cyclic
    c hc i hi x hx hxi hxi1
  obtain ⟨rr, hrr, hdr⟩ := exists_rightHalfDisc_disjoint_image_cyclic
    c hc i hi x hx hxi hxi1
  obtain ⟨ε, hε, hjump⟩ := angleSum_edge_jump_cyclic c hc i hi x hx hxi hxi1
  let r := min ε (min rl rr)
  have hr : 0 < r := lt_min hε (lt_min hrl hrr)
  let d := c.point (i + 1) - c.point i
  have hd : d ≠ 0 := sub_ne_zero.mpr (hc.2.2.1 i hi).symm
  have hleft : leftHalfDisc x d r ⊆ c.imageᶜ := by
    intro z hz
    exact fun hzimage => Set.disjoint_left.mp hdl
      ⟨Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hz.1,
        hz.2⟩ hzimage
  have hright : rightHalfDisc x d r ⊆ c.imageᶜ := by
    intro z hz
    exact fun hzimage => Set.disjoint_left.mp hdr
      ⟨Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hz.1,
        hz.2⟩ hzimage
  obtain ⟨u, hu⟩ := leftHalfDisc_nonempty x d r hd hr
  obtain ⟨v, hv⟩ := rightHalfDisc_nonempty x d r hd hr
  have hcl := isConnected_leftHalfDisc x d r ⟨u, hu⟩
  have hcr := isConnected_rightHalfDisc x d r ⟨v, hv⟩
  refine ⟨r, hr, c.angleSum u, c.angleSum v, hcl, hcr, ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨hleft hz, angleSum_eq_of_isPreconnected c hclosed _ hcl.isPreconnected
      hleft z u hz hu⟩
  · intro z hz
    exact ⟨hright hz, angleSum_eq_of_isPreconnected c hclosed _ hcr.isPreconnected
      hright z v hz hv⟩
  · exact hjump u v (hleft hu) (hright hv)
      (lt_of_lt_of_le hu.1 (min_le_left _ _))
      (lt_of_lt_of_le hv.1 (min_le_left _ _)) (mul_neg_of_pos_of_neg hu.2 hv.2)

/-- Helper toward Proposition 5.16: left half-discs with nearby centers on the
same oriented supporting line overlap, even when their positive radii vary. -/
theorem leftHalfDisc_inter_nonempty_of_center_near (x y d : ℂ) (r s : ℝ)
    (hd : d ≠ 0) (hs : 0 < s) (hxy : y ∈ edgeLine x d)
    (hnear : dist y x < r) :
    (leftHalfDisc x d r ∩ leftHalfDisc y d s).Nonempty := by
  let ρ := min s (r - dist y x)
  have hρ : 0 < ρ := lt_min hs (sub_pos.mpr hnear)
  obtain ⟨w, hw⟩ := leftHalfDisc_nonempty y d ρ hd hρ
  have hcoord : (star d * (w - x)).im = (star d * (w - y)).im := by
    have heq : star d * (w - x) = star d * (w - y) + star d * (y - x) := by
      ring
    rw [heq, Complex.add_im, show (star d * (y - x)).im = 0 from hxy, add_zero]
  refine ⟨w, ⟨?_, ?_⟩, ?_⟩
  · change dist w x < r
    calc
      dist w x ≤ dist w y + dist y x := dist_triangle _ _ _
      _ < ρ + dist y x := by
        have hwd : dist w y < ρ := hw.1
        linarith only [hwd]
      _ ≤ r := by
        have hle : ρ ≤ r - dist y x := min_le_right _ _
        linarith
  · change 0 < (star d * (w - x)).im
    rw [hcoord]
    exact hw.2
  · exact ⟨Metric.ball_subset_ball (min_le_left _ _) hw.1, hw.2⟩

/-- Helper toward Proposition 5.16: positive-radius left half-discs centered
along an open segment form a connected strip when their supporting lines
agree. No continuity of the radii is required. -/
theorem isConnected_iUnion_leftHalfDisc_openSegment (a b d : ℂ)
    (hd : d ≠ 0)
    (hline : ∀ x y : ↥(openSegment ℝ a b), (y : ℂ) ∈ edgeLine x d)
    (r : ↥(openSegment ℝ a b) → ℝ) (hr : ∀ x, 0 < r x) :
    IsConnected (⋃ x : ↥(openSegment ℝ a b), leftHalfDisc x d (r x)) := by
  classical
  let S : Set ℂ := ⋃ x : ↥(openSegment ℝ a b), leftHalfDisc x d (r x)
  have hne (x : ↥(openSegment ℝ a b)) :=
    leftHalfDisc_nonempty x d (r x) hd (hr x)
  choose u hu using hne
  have hsub (x : ↥(openSegment ℝ a b)) : leftHalfDisc x d (r x) ⊆ S := by
    intro w hw
    exact Set.mem_iUnion.mpr ⟨x, hw⟩
  have hcomp (x : ↥(openSegment ℝ a b)) :
      leftHalfDisc x d (r x) ⊆ connectedComponentIn S (u x) :=
    (convex_leftHalfDisc x d (r x)).isPreconnected.subset_connectedComponentIn
      (hu x) (hsub x)
  let κ : ↥(openSegment ℝ a b) → Set ℂ := fun x => connectedComponentIn S (u x)
  have hκ : IsLocallyConstant κ := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro x
    refine ⟨Subtype.val ⁻¹' Metric.ball (x : ℂ) (r x),
      Metric.isOpen_ball.preimage continuous_subtype_val, ?_, ?_⟩
    · simpa only [Set.mem_preimage, Metric.mem_ball, dist_self] using hr x
    · intro y hy
      obtain ⟨w, hwx, hwy⟩ := leftHalfDisc_inter_nonempty_of_center_near
        x y d (r x) (r y) hd (hr y) (hline x y) hy
      exact (connectedComponentIn_eq (hcomp y hwy)).trans
        (connectedComponentIn_eq (hcomp x hwx)).symm
  have hpre : IsPreconnected (openSegment ℝ a b) :=
    (convex_openSegment a b).isPreconnected
  have : PreconnectedSpace ↥(openSegment ℝ a b) :=
    isPreconnected_iff_preconnectedSpace.mp hpre
  let x₀ : ↥(openSegment ℝ a b) := ⟨midpoint ℝ a b, midpoint_mem_openSegment a b⟩
  have heq : S = connectedComponentIn S (u x₀) := by
    apply Set.Subset.antisymm ?_ (connectedComponentIn_subset _ _)
    intro w hw
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hw
    have hk : κ x = κ x₀ := hκ.apply_eq_of_preconnectedSpace x x₀
    change w ∈ κ x₀
    rw [← hk]
    exact hcomp x hx
  change IsConnected S
  rw [heq]
  exact isConnected_connectedComponentIn_iff.mpr (hsub x₀ (hu x₀))

/-- Helper toward Proposition 5.16: reversing the direction turns a right
half-disc into a left half-disc. -/
theorem rightHalfDisc_eq_leftHalfDisc_neg (x d : ℂ) (r : ℝ) :
    rightHalfDisc x d r = leftHalfDisc x (-d) r := by
  ext z
  simp only [rightHalfDisc, leftHalfDisc, Set.mem_inter_iff, Set.mem_ofPred_eq,
    star_neg, neg_mul, Complex.neg_im, neg_pos]

/-- Helper toward Proposition 5.16: each full open edge of a cyclically simple
polygon has connected open left and right strips avoiding the image. Their
half-disc radii are shared between the two sides at every center. -/
theorem exists_connected_open_edge_strips_cyclic (c : Polyline)
    (hc : c.IsCyclicSimple) (i : ℕ) (hi : i + 1 < c.points.length) :
    ∃ r : ↥(openSegment ℝ (c.point i) (c.point (i + 1))) → ℝ,
      (∀ x, 0 < r x) ∧
      (let L := ⋃ x : ↥(openSegment ℝ (c.point i) (c.point (i + 1))),
         leftHalfDisc x (c.point (i + 1) - c.point i) (r x)
       let R := ⋃ x : ↥(openSegment ℝ (c.point i) (c.point (i + 1))),
         rightHalfDisc x (c.point (i + 1) - c.point i) (r x)
       IsOpen L ∧ IsOpen R ∧ IsConnected L ∧ IsConnected R ∧
         Disjoint L c.image ∧ Disjoint R c.image) := by
  classical
  let a := c.point i
  let b := c.point (i + 1)
  have hab : a ≠ b := hc.2.2.1 i hi
  have hd : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hex (x : ↥(openSegment ℝ a b)) :
      ∃ r : ℝ, 0 < r ∧ Disjoint (leftHalfDisc x (b - a) r) c.image ∧
        Disjoint (rightHalfDisc x (b - a) r) c.image := by
    have hxa : (x : ℂ) ≠ a := by
      intro h
      exact hab (left_mem_openSegment_iff.mp (h ▸ x.property))
    have hxb : (x : ℂ) ≠ b := by
      intro h
      exact hab (right_mem_openSegment_iff.mp (h ▸ x.property))
    obtain ⟨r, hr, _, _, _, _, _, _, hl, hrr⟩ :=
      exists_connected_edge_sides_cyclic c hc i hi x
        (openSegment_subset_segment ℝ a b x.property) hxa hxb
    exact ⟨r, hr, hl, hrr⟩
  choose r hr hl hrr using hex
  refine ⟨r, hr, ?_⟩
  have hline (x y : ↥(openSegment ℝ a b)) : (y : ℂ) ∈ edgeLine x (b - a) :=
    segment_subset_edgeLine a b x (openSegment_subset_segment ℝ a b x.property)
      (openSegment_subset_segment ℝ a b y.property)
  refine ⟨isOpen_iUnion (fun x => isOpen_leftHalfDisc x (b - a) (r x)),
    isOpen_iUnion (fun x => isOpen_rightHalfDisc x (b - a) (r x)),
    isConnected_iUnion_leftHalfDisc_openSegment a b (b - a) hd hline r hr, ?_, ?_, ?_⟩
  · simp_rw [rightHalfDisc_eq_leftHalfDisc_neg]
    apply isConnected_iUnion_leftHalfDisc_openSegment a b (-(b - a))
      (neg_ne_zero.mpr hd) ?_ r hr
    intro x y
    change (star (-(b - a)) * ((y : ℂ) - x)).im = 0
    have hxy := hline x y
    change (star (b - a) * ((y : ℂ) - x)).im = 0 at hxy
    simpa only [star_neg, neg_mul, Complex.neg_im, neg_eq_zero] using hxy
  · apply Set.disjoint_left.mpr
    intro z hz hzimage
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hz
    exact Set.disjoint_left.mp (hl x) hx hzimage
  · apply Set.disjoint_left.mpr
    intro z hz hzimage
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hz
    exact Set.disjoint_left.mp (hrr x) hx hzimage

/-- Helper toward Proposition 5.16: the center lies in the closure of every
positive-radius left half-disc with nonzero direction. -/
theorem mem_closure_leftHalfDisc (x d : ℂ) (r : ℝ) (hd : d ≠ 0) (hr : 0 < r) :
    x ∈ closure (leftHalfDisc x d r) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨w, hw⟩ := leftHalfDisc_nonempty x d (min ε r) hd (lt_min hε hr)
  refine ⟨w, ⟨Metric.ball_subset_ball (min_le_right _ _) hw.1, hw.2⟩, ?_⟩
  have hdist : dist w x < ε := lt_of_lt_of_le hw.1 (min_le_left _ _)
  simpa only [dist_comm] using hdist

/-- Helper toward Proposition 5.16: the center lies in the closure of every
positive-radius right half-disc with nonzero direction. -/
theorem mem_closure_rightHalfDisc (x d : ℂ) (r : ℝ) (hd : d ≠ 0) (hr : 0 < r) :
    x ∈ closure (rightHalfDisc x d r) := by
  rw [rightHalfDisc_eq_leftHalfDisc_neg]
  exact mem_closure_leftHalfDisc x (-d) r (neg_ne_zero.mpr hd) hr

/-- Helper toward Proposition 5.16: an entire polygon edge, including its
endpoints, is approached by two disjoint connected open strips in the
complement. Angle sum is constant on each strip and the values differ by one.
This statement does not identify strips belonging to different edges. -/
theorem exists_connected_constant_edge_strips_cyclic (c : Polyline)
    (hc : c.IsCyclicSimple) (i : ℕ) (hi : i + 1 < c.points.length) :
    ∃ L R : Set ℂ, IsOpen L ∧ IsOpen R ∧ IsConnected L ∧ IsConnected R ∧
      L ⊆ c.imageᶜ ∧ R ⊆ c.imageᶜ ∧ Disjoint L R ∧
      c.segmentAt i ⊆ closure L ∩ closure R ∧
      ∃ a b : ℝ, (∀ z ∈ L, c.angleSum z = a) ∧
        (∀ z ∈ R, c.angleSum z = b) ∧ |a - b| = 1 := by
  classical
  have hclosed : c.start = c.finish := by
    rw [← point_zero_eq_start c, ← point_last_eq_finish c]
    exact hc.2.1
  let a := c.point i
  let b := c.point (i + 1)
  let d := b - a
  have hab : a ≠ b := hc.2.2.1 i hi
  have hd : d ≠ 0 := sub_ne_zero.mpr hab.symm
  obtain ⟨r, hr, hoL, hoR, hcL, hcR, hdL, hdR⟩ :=
    exists_connected_open_edge_strips_cyclic c hc i hi
  let L := ⋃ x : ↥(openSegment ℝ a b), leftHalfDisc x d (r x)
  let R := ⋃ x : ↥(openSegment ℝ a b), rightHalfDisc x d (r x)
  have hL : L ⊆ c.imageᶜ := fun _ hz hzim => Set.disjoint_left.mp hdL hz hzim
  have hR : R ⊆ c.imageᶜ := fun _ hz hzim => Set.disjoint_left.mp hdR hz hzim
  have hclL : segment ℝ a b ⊆ closure L := by
    apply Set.Subset.trans (segment_subset_closure_openSegment (𝕜 := ℝ))
    apply closure_minimal ?_ isClosed_closure
    intro x hx
    exact closure_mono (s := leftHalfDisc x d (r ⟨x, hx⟩))
      (fun w hw => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hw⟩)
      (mem_closure_leftHalfDisc x d (r ⟨x, hx⟩) hd (hr ⟨x, hx⟩))
  have hclR : segment ℝ a b ⊆ closure R := by
    apply Set.Subset.trans (segment_subset_closure_openSegment (𝕜 := ℝ))
    apply closure_minimal ?_ isClosed_closure
    intro x hx
    exact closure_mono (s := rightHalfDisc x d (r ⟨x, hx⟩))
      (fun w hw => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hw⟩)
      (mem_closure_rightHalfDisc x d (r ⟨x, hx⟩) hd (hr ⟨x, hx⟩))
  let m : ↥(openSegment ℝ a b) := ⟨midpoint ℝ a b, midpoint_mem_openSegment a b⟩
  have hma : (m : ℂ) ≠ a := by
    intro h
    exact hab (left_mem_openSegment_iff.mp (h ▸ m.property))
  have hmb : (m : ℂ) ≠ b := by
    intro h
    exact hab (right_mem_openSegment_iff.mp (h ▸ m.property))
  obtain ⟨ε, hε, hjump⟩ := angleSum_edge_jump_cyclic c hc i hi m
    (openSegment_subset_segment ℝ a b m.property) hma hmb
  let ρ := min ε (r m)
  have hρ : 0 < ρ := lt_min hε (hr m)
  obtain ⟨u, hu⟩ := leftHalfDisc_nonempty m d ρ hd hρ
  obtain ⟨v, hv⟩ := rightHalfDisc_nonempty m d ρ hd hρ
  have huL : u ∈ L := Set.mem_iUnion.mpr
    ⟨m, ⟨Metric.ball_subset_ball (min_le_right _ _) hu.1, hu.2⟩⟩
  have hvR : v ∈ R := Set.mem_iUnion.mpr
    ⟨m, ⟨Metric.ball_subset_ball (min_le_right _ _) hv.1, hv.2⟩⟩
  have hconstL (z : ℂ) (hz : z ∈ L) : c.angleSum z = c.angleSum u :=
    angleSum_eq_of_isPreconnected c hclosed L hcL.isPreconnected hL z u hz huL
  have hconstR (z : ℂ) (hz : z ∈ R) : c.angleSum z = c.angleSum v :=
    angleSum_eq_of_isPreconnected c hclosed R hcR.isPreconnected hR z v hz hvR
  have hj : |c.angleSum u - c.angleSum v| = 1 :=
    hjump u v (hL huL) (hR hvR)
      (lt_of_lt_of_le hu.1 (min_le_left _ _))
      (lt_of_lt_of_le hv.1 (min_le_left _ _)) (mul_neg_of_pos_of_neg hu.2 hv.2)
  have hdis : Disjoint L R := by
    apply Set.disjoint_left.mpr
    intro z hzL hzR
    have heq : c.angleSum u = c.angleSum v := (hconstL z hzL).symm.trans (hconstR z hzR)
    rw [heq, sub_self, abs_zero] at hj
    norm_num at hj
  refine ⟨L, R, hoL, hoR, hcL, hcR, hL, hR, hdis, ?_,
    c.angleSum u, c.angleSum v, hconstL, hconstR, hj⟩
  intro z hz
  exact ⟨hclL hz, hclR hz⟩

/-- Helper toward Proposition 5.16: a cyclic polygon vertex belongs to no
edge other than its outgoing and incoming edges, with the root incidence
handled cyclically. -/
theorem not_mem_segmentAt_of_ne_vertex_cyclic (c : Polyline)
    (hc : c.IsCyclicSimple) (i j : ℕ)
    (hi : i + 1 < c.points.length) (hj : j + 1 < c.points.length)
    (hji : j ≠ i) (hprev : j + 1 ≠ i)
    (hwrap : ¬ (i = 0 ∧ j + 2 = c.points.length)) :
    c.point i ∉ c.segmentAt j := by
  intro hmem
  have hown : c.point i ∈ c.segmentAt i := left_mem_segment ℝ _ _
  by_cases hij : i < j
  · by_cases hadj : i + 1 = j
    · have hmeet : c.point i ∈ ({c.point (i + 1)} : Set ℂ) := by
        rw [← hc.2.2.2.1 i (by omega)]
        exact ⟨hown, hadj ▸ hmem⟩
      exact hc.2.2.1 i hi (Set.mem_singleton_iff.mp hmeet)
    · exact Set.disjoint_left.mp
        (hc.2.2.2.2.1 i j hi hj (by omega) hwrap) hown hmem
  · have hlt : j + 1 < i := by omega
    by_cases hroot : j = 0 ∧ i + 2 = c.points.length
    · have hiLast : i = c.points.length - 2 := by omega
      have hmeet : c.point i ∈ ({c.point 0} : Set ℂ) := by
        rw [← hc.2.2.2.2.2]
        exact ⟨hroot.1 ▸ hmem, hiLast ▸ hown⟩
      have heq : c.point i = c.point (i + 1) := by
        calc
          c.point i = c.point 0 := Set.mem_singleton_iff.mp hmeet
          _ = c.point (c.points.length - 1) := hc.2.1
          _ = c.point (i + 1) := by congr 1; omega
      exact hc.2.2.1 i hi heq
    · exact Set.disjoint_left.mp
        (hc.2.2.2.2.1 j i hj hi hlt hroot) hmem hown

/-- Helper toward Proposition 5.16: a positive-radius vertex ball avoids
every nonincident edge of a cyclically simple polygon. -/
theorem exists_pos_ball_avoiding_nonincident_vertex_edges_cyclic (c : Polyline)
    (hc : c.IsCyclicSimple) (i : ℕ) (hi : i + 1 < c.points.length) :
    ∃ r : ℝ, 0 < r ∧ ∀ y : ℂ, dist y (c.point i) < r →
      ∀ j : ℕ, j + 1 < c.points.length → j ≠ i → j + 1 ≠ i →
        ¬ (i = 0 ∧ j + 2 = c.points.length) → y ∉ c.segmentAt j := by
  classical
  let J := (Finset.range (c.points.length - 1)).filter
    (fun j => j ≠ i ∧ j + 1 ≠ i ∧ ¬ (i = 0 ∧ j + 2 = c.points.length))
  have hcompact (j : ℕ) : IsCompact (c.segmentAt j) := by
    rw [Polyline.segmentAt, segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)
  have hclosed : IsClosed (⋃ j ∈ J, c.segmentAt j) :=
    isClosed_biUnion_finset (fun j _ => (hcompact j).isClosed)
  have hnot : c.point i ∉ ⋃ j ∈ J, c.segmentAt j := by
    intro hmem
    obtain ⟨j, hjJ, hjmem⟩ := Set.mem_iUnion₂.mp hmem
    obtain ⟨hjrange, hji, hprev, hwrap⟩ := Finset.mem_filter.mp hjJ
    have hj : j + 1 < c.points.length := by
      simp only [Finset.mem_range] at hjrange
      omega
    exact not_mem_segmentAt_of_ne_vertex_cyclic c hc i j hi hj hji hprev hwrap hjmem
  have hev : ∀ᶠ y : ℂ in 𝓝 (c.point i), y ∉ ⋃ j ∈ J, c.segmentAt j :=
    hclosed.isOpen_compl.mem_nhds hnot
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨r, hr, ?_⟩
  intro y hy j hj hji hprev hwrap hjmem
  apply hball hy
  exact Set.mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr
    ⟨by simp only [Finset.mem_range]; omega, hji, hprev, hwrap⟩, hjmem⟩

/-- Helper toward Proposition 5.16: near any vertex the image of a cyclically
simple polygon consists exactly of its two incident segments. The incoming
index is interpreted cyclically at the root. -/
theorem exists_pos_ball_image_eq_incident_segments_cyclic (c : Polyline)
    (hc : c.IsCyclicSimple) (i : ℕ) (hi : i + 1 < c.points.length) :
    ∃ r : ℝ, 0 < r ∧ ∀ y : ℂ, dist y (c.point i) < r →
      (y ∈ c.image ↔ y ∈ c.segmentAt
        (if i = 0 then c.points.length - 2 else i - 1) ∪ c.segmentAt i) := by
  let k := if i = 0 then c.points.length - 2 else i - 1
  have hlen := hc.1
  have hk : k + 1 < c.points.length := by
    dsimp [k]
    split_ifs <;> omega
  obtain ⟨r, hr, havoid⟩ :=
    exists_pos_ball_avoiding_nonincident_vertex_edges_cyclic c hc i hi
  refine ⟨r, hr, ?_⟩
  intro y hy
  constructor
  · intro hyimage
    have hex : ∃ j, j + 1 < c.points.length ∧ y ∈ c.segmentAt j := by
      rcases hyimage with hyroot | ⟨j, hj, hyj⟩
      · have heq : y = c.start := Set.mem_singleton_iff.mp hyroot
        refine ⟨0, by omega, ?_⟩
        rw [heq, ← point_zero_eq_start c]
        exact left_mem_segment ℝ _ _
      · exact ⟨j, hj, hyj⟩
    obtain ⟨j, hj, hyj⟩ := hex
    by_cases hji : j = i
    · exact Or.inr (hji ▸ hyj)
    by_cases hprev : j + 1 = i
    · have heq : j = k := by
        dsimp [k]
        split_ifs <;> omega
      apply Or.inl
      change y ∈ c.segmentAt k
      rw [← heq]
      exact hyj
    by_cases hwrap : i = 0 ∧ j + 2 = c.points.length
    · have heq : j = k := by
        dsimp [k]
        simp only [hwrap.1, ite_true]
        omega
      apply Or.inl
      change y ∈ c.segmentAt k
      rw [← heq]
      exact hyj
    exact (havoid y hy j hj hji hprev hwrap hyj).elim
  · rintro (hyj | hyj)
    · exact c.segmentAt_subset_image hk hyj
    · exact c.segmentAt_subset_image hi hyj

/-- Helper toward Proposition 5.16: each edge is contained in the closures of
two distinct complementary components. Identifying these two components
consistently around all vertices remains a global obligation. -/
theorem exists_distinct_components_adjacent_to_edge_cyclic (c : Polyline)
    (hc : c.IsCyclicSimple) (i : ℕ) (hi : i + 1 < c.points.length) :
    ∃ u v : ℂ, u ∉ c.image ∧ v ∉ c.image ∧
      connectedComponentIn c.imageᶜ u ≠ connectedComponentIn c.imageᶜ v ∧
      c.segmentAt i ⊆ closure (connectedComponentIn c.imageᶜ u) ∩
        closure (connectedComponentIn c.imageᶜ v) := by
  have hclosed : c.start = c.finish := by
    rw [← point_zero_eq_start c, ← point_last_eq_finish c]
    exact hc.2.1
  obtain ⟨L, R, _, _, hcL, hcR, hL, hR, _, hcl, a, b, ha, hb, hj⟩ :=
    exists_connected_constant_edge_strips_cyclic c hc i hi
  obtain ⟨u, hu⟩ := hcL.nonempty
  obtain ⟨v, hv⟩ := hcR.nonempty
  have hLC : L ⊆ connectedComponentIn c.imageᶜ u :=
    hcL.isPreconnected.subset_connectedComponentIn hu hL
  have hRC : R ⊆ connectedComponentIn c.imageᶜ v :=
    hcR.isPreconnected.subset_connectedComponentIn hv hR
  refine ⟨u, v, hL hu, hR hv, ?_, ?_⟩
  · intro heq
    have hvC : v ∈ connectedComponentIn c.imageᶜ u :=
      heq.symm ▸ mem_connectedComponentIn (hR hv)
    have hvu := angleSum_eq_on_component c hclosed u (hL hu) v hvC
    rw [ha u hu, hb v hv] at hvu
    rw [hvu, sub_self, abs_zero] at hj
    norm_num at hj
  · intro z hz
    exact ⟨closure_mono hLC (hcl hz).1, closure_mono hRC (hcl hz).2⟩

/-- Helper toward Proposition 5.16: every complementary point is joined
inside the complement to every positive-radius neighborhood of the image.
The witness in that neighborhood has the same complementary component. -/
theorem exists_joinedIn_image_neighborhood (c : Polyline) (z : ℂ)
    (hz : z ∉ c.image) :
    ∃ q ∈ c.image, ∀ ε : ℝ, 0 < ε → ∃ w : ℂ,
      dist w q < ε ∧ JoinedIn c.imageᶜ z w ∧
        connectedComponentIn c.imageᶜ z = connectedComponentIn c.imageᶜ w := by
  obtain ⟨q, hq, _, hnear⟩ := exists_segment_to_image_neighborhood c z hz
  refine ⟨q, hq, ?_⟩
  intro ε hε
  obtain ⟨w, hw, hseg⟩ := hnear ε hε
  have hcomp : w ∈ connectedComponentIn c.imageᶜ z :=
    (convex_segment z w).isPreconnected.subset_connectedComponentIn
      (left_mem_segment ℝ z w) hseg (right_mem_segment ℝ z w)
  exact ⟨w, hw, JoinedIn.of_segment_subset hseg, connectedComponentIn_eq hcomp⟩

/- Remaining target A (global strips), with full binders:

  ∀ (c : Polyline), c.IsCyclicSimple →
    ∃ (ε : ℝ) (L R : Set ℂ), 0 < ε ∧ IsConnected L ∧ IsConnected R ∧
      Disjoint L R ∧
      L ∪ R = {z | z ∉ c.image ∧ ∃ q ∈ c.image, dist z q < ε}.

The proved full-edge strips do not supply the vertex wedge pieces or prove
that consecutive left strips, and consecutive right strips, join cyclically.
The vertex ball theorem above isolates exactly the two incident segments,
including the root, but does not yet connect the sectors of their complement.

Remaining target B: passage from an arbitrary complementary point to one of
the two global sides L and R. The stronger metric part is proved above for
every ε > 0 by `exists_joinedIn_image_neighborhood`, with one fixed nearest
image point and equality of components. Identifying the neighborhood with
L ∪ R still depends on A.

Remaining target C (at most two complementary components), with full binders:

  ∀ (c : Polyline), c.IsCyclicSimple →
    ∃ u v : ℂ, u ∉ c.image ∧ v ∉ c.image ∧
      ∀ z : ℂ, z ∉ c.image →
        connectedComponentIn c.imageᶜ z = connectedComponentIn c.imageᶜ u ∨
        connectedComponentIn c.imageᶜ z = connectedComponentIn c.imageᶜ v.

The two distinct components adjacent to each individual edge are proved;
their consistent identification across vertices is not proved.

Remaining target D, with full binders:

  ∀ (c : Polyline), c.IsCyclicSimple →
    IsConnected c.inside ∧ IsConnected c.outside.

Three approaches were pursued before leaving these global statements open.
1. Variable-radius polygonal strips: overlap of half-discs, connectedness of
   their union along each full open edge, and closure incidence at both
   endpoints are proved. Extending this to a collar requires checked passages
   through convex, reflex, straight, and root vertices; those passages remain.
2. Nearest-point radial segments: compactness gives one nearest image point;
   the open radial segment avoids the image, and truncations join every
   complementary component to every positive-width neighborhood. This does
   not bound the number of components of that neighborhood without (1).
3. Winding and component propagation: angle sum is proved constant on every
   complementary component; full edge strips have values differing by one;
   components lie entirely inside or outside. Equal angle sums do not imply
   equal components, so this route still needs the vertex-sector gluing.
   An ear-removal alternative was also considered: the searched installed
   topology/geometry/convex sources did not provide a polygon triangulation
   or ear-decomposition theorem discharging the required degeneracies.

No global side connectedness, Jordan theorem, or component count is assumed.
No assertion here establishes completion of Proposition 5.16. -/

end Polyline
end DirectedDistances.PlanarMap

end
