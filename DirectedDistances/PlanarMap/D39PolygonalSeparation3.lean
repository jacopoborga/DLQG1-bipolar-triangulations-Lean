/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PolygonalSeparation2
import DirectedDistances.PlanarMap.D39PolygonEdgeJump
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Module.Convex

/-! # Local half-discs and polygonal separation

Helpers toward Proposition 5.16. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap
namespace Polyline

/-- The real-linear coordinate measuring signed displacement to the left of
the oriented direction `d`. -/
private def leftCoordinate (d : ℂ) : ℂ →ₗ[ℝ] ℂ where
  toFun z := star d * z
  map_add' z w := by exact mul_add _ _ _
  map_smul' r z := by
    simp only [RCLike.real_smul_eq_coe_mul]
    ac_rfl

/-- Helper toward Proposition 5.16: the open half-disc to the left of the
oriented line through `x` with direction `d`. -/
@[expose] def leftHalfDisc (x d : ℂ) (r : ℝ) : Set ℂ :=
  Metric.ball x r ∩ {z | 0 < (star d * (z - x)).im}

/-- Helper toward Proposition 5.16: the open half-disc to the right of the
oriented line through `x` with direction `d`. -/
@[expose] def rightHalfDisc (x d : ℂ) (r : ℝ) : Set ℂ :=
  Metric.ball x r ∩ {z | (star d * (z - x)).im < 0}

/-- Helper toward Proposition 5.16: the supporting line of an oriented edge,
written as the zero set of its signed transverse coordinate. -/
@[expose] def edgeLine (x d : ℂ) : Set ℂ :=
  {z | (star d * (z - x)).im = 0}

/-- Helper toward Proposition 5.16: each open half-disc is convex. -/
theorem convex_leftHalfDisc (x d : ℂ) (r : ℝ) :
    Convex ℝ (leftHalfDisc x d r) := by
  have hbase : Convex ℝ ((leftCoordinate d) ⁻¹' {w : ℂ | 0 < w.im}) :=
    (convex_halfSpace_im_gt 0).linear_preimage (leftCoordinate d)
  have hside : Convex ℝ ((fun z : ℂ => z - x) ⁻¹'
      ((leftCoordinate d) ⁻¹' {w : ℂ | 0 < w.im})) := by
    simpa only [sub_eq_add_neg] using hbase.translate_preimage_left (-x)
  exact (convex_ball x r).inter (by
    change Convex ℝ ((fun z : ℂ => z - x) ⁻¹'
      ((leftCoordinate d) ⁻¹' {w : ℂ | 0 < w.im}))
    exact hside)

/-- Helper toward Proposition 5.16: each open half-disc is convex. -/
theorem convex_rightHalfDisc (x d : ℂ) (r : ℝ) :
    Convex ℝ (rightHalfDisc x d r) := by
  have hbase : Convex ℝ ((leftCoordinate d) ⁻¹' {w : ℂ | w.im < 0}) :=
    (convex_halfSpace_im_lt 0).linear_preimage (leftCoordinate d)
  have hside : Convex ℝ ((fun z : ℂ => z - x) ⁻¹'
      ((leftCoordinate d) ⁻¹' {w : ℂ | w.im < 0})) := by
    simpa only [sub_eq_add_neg] using hbase.translate_preimage_left (-x)
  exact (convex_ball x r).inter (by
    change Convex ℝ ((fun z : ℂ => z - x) ⁻¹'
      ((leftCoordinate d) ⁻¹' {w : ℂ | w.im < 0}))
    exact hside)

/-- Helper toward Proposition 5.16: a nonempty open half-disc is connected. -/
theorem isConnected_leftHalfDisc (x d : ℂ) (r : ℝ)
    (hne : (leftHalfDisc x d r).Nonempty) : IsConnected (leftHalfDisc x d r) :=
  (convex_leftHalfDisc x d r).isConnected hne

/-- Helper toward Proposition 5.16: a nonempty open half-disc is connected. -/
theorem isConnected_rightHalfDisc (x d : ℂ) (r : ℝ)
    (hne : (rightHalfDisc x d r).Nonempty) : IsConnected (rightHalfDisc x d r) :=
  (convex_rightHalfDisc x d r).isConnected hne

/-- Helper toward Proposition 5.16: both sides of a nondegenerate oriented
line meet every ball of positive radius about a point on the line. -/
theorem leftHalfDisc_nonempty (x d : ℂ) (r : ℝ) (hd : d ≠ 0) (hr : 0 < r) :
    (leftHalfDisc x d r).Nonempty := by
  have hnorm : 0 < ‖d‖ := norm_pos_iff.mpr hd
  let s : ℝ := r / (2 * ‖d‖)
  have hs : 0 < s := div_pos hr (mul_pos (by norm_num) hnorm)
  let z : ℂ := x + (s : ℂ) * Complex.I * d
  have hzm : z - x = (s : ℂ) * Complex.I * d := by
    dsimp [z]
    ring
  have hnormstep : ‖(s : ℂ) * Complex.I * d‖ = r / 2 := by
    rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs, Complex.norm_I]
    dsimp [s]
    field_simp [hnorm.ne']
  have hnsq : 0 < Complex.normSq d := by
    rw [← Complex.norm_mul_self_eq_normSq]
    positivity
  have hsquare : star d * d = (Complex.normSq d : ℂ) := by
    simpa [Complex.star_def] using (Complex.normSq_eq_conj_mul_self (z := d)).symm
  have hcross : 0 < (star d * (z - x)).im := by
    rw [hzm]
    have hprod : star d * ((s : ℂ) * Complex.I * d) =
        ((s * Complex.normSq d : ℝ) : ℂ) * Complex.I := by
      calc
        star d * ((s : ℂ) * Complex.I * d) =
            (s : ℂ) * Complex.I * (star d * d) := by ring
        _ = (s : ℂ) * Complex.I * (Complex.normSq d : ℂ) := by rw [hsquare]
        _ = ((s * Complex.normSq d : ℝ) : ℂ) * Complex.I := by
          push_cast
          ac_rfl
    rw [hprod]
    simpa [Complex.mul_im] using mul_pos hs hnsq
  refine ⟨z, ?_⟩
  change z ∈ Metric.ball x r ∧ 0 < (star d * (z - x)).im
  constructor
  · change dist z x < r
    rw [dist_eq_norm, hzm, hnormstep]
    linarith
  · exact hcross

/-- Helper toward Proposition 5.16: both sides of a nondegenerate oriented
line meet every ball of positive radius about a point on the line. -/
theorem rightHalfDisc_nonempty (x d : ℂ) (r : ℝ) (hd : d ≠ 0) (hr : 0 < r) :
    (rightHalfDisc x d r).Nonempty := by
  have hleft := leftHalfDisc_nonempty x d r hd hr
  obtain ⟨z, hz⟩ := hleft
  refine ⟨2 * x - z, ?_⟩
  change 2 * x - z ∈ Metric.ball x r ∧
    (star d * (2 * x - z - x)).im < 0
  constructor
  · change dist (2 * x - z) x < r
    rw [dist_eq_norm]
    have hneg : 2 * x - z - x = -(z - x) := by ring
    rw [hneg, norm_neg]
    have hzball : dist z x < r := hz.1
    simpa [dist_eq_norm] using hzball
  · have hneg : 2 * x - z - x = -(z - x) := by ring
    rw [hneg, mul_neg, Complex.neg_im]
    exact neg_neg_of_pos hz.2

/-- Helper toward Proposition 5.16: the two half-discs are open. -/
theorem isOpen_leftHalfDisc (x d : ℂ) (r : ℝ) :
    IsOpen (leftHalfDisc x d r) := by
  have hcont : Continuous (fun z : ℂ => (star d * (z - x)).im) := by fun_prop
  change IsOpen (Metric.ball x r ∩ {z | 0 < (star d * (z - x)).im})
  exact Metric.isOpen_ball.inter (isOpen_lt continuous_const hcont)

/-- Helper toward Proposition 5.16: the two half-discs are open. -/
theorem isOpen_rightHalfDisc (x d : ℂ) (r : ℝ) :
    IsOpen (rightHalfDisc x d r) := by
  have hcont : Continuous (fun z : ℂ => (star d * (z - x)).im) := by fun_prop
  change IsOpen (Metric.ball x r ∩ {z | (star d * (z - x)).im < 0})
  exact Metric.isOpen_ball.inter (isOpen_lt hcont continuous_const)

/-- Helper toward Proposition 5.16: a segment containing `x` lies in the
supporting line through `x` in the segment direction. -/
theorem segment_subset_edgeLine (a b x : ℂ) (hx : x ∈ segment ℝ a b) :
    segment ℝ a b ⊆ edgeLine x (b - a) := by
  intro z hz
  rw [segment_eq_image'] at hx hz
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, htz⟩ := hz
  have hzd : z - x = ((t - s : ℝ) : ℂ) * (b - a) := by
    calc
      z - x = (a + t • (b - a)) - (a + s • (b - a)) := by rw [← htz, ← hsx]
      _ = ((t - s : ℝ) : ℂ) * (b - a) := by
        rw [RCLike.real_smul_eq_coe_mul, RCLike.real_smul_eq_coe_mul]
        push_cast
        ring_nf
        ac_rfl
  have hsquare : star (b - a) * (b - a) = (Complex.normSq (b - a) : ℂ) := by
    simpa [Complex.star_def] using
      (Complex.normSq_eq_conj_mul_self (z := b - a)).symm
  have hprod : star (b - a) * (z - x) =
      (((t - s) * Complex.normSq (b - a) : ℝ) : ℂ) := by
    rw [hzd]
    calc
      star (b - a) * (((t - s : ℝ) : ℂ) * (b - a)) =
          ((t - s : ℝ) : ℂ) * (star (b - a) * (b - a)) := by ac_rfl
      _ = ((t - s : ℝ) : ℂ) * (Complex.normSq (b - a) : ℂ) := by rw [hsquare]
      _ = (((t - s) * Complex.normSq (b - a) : ℝ) : ℂ) := by
        push_cast
        ring
  change (star (b - a) * (z - x)).im = 0
  rw [hprod]
  simp

/-- Helper toward Proposition 5.16: each half-disc misses its supporting line. -/
theorem disjoint_leftHalfDisc_edgeLine (x d : ℂ) (r : ℝ) :
    Disjoint (leftHalfDisc x d r) (edgeLine x d) := by
  apply Set.disjoint_left.mpr
  intro z hz hzline
  change z ∈ Metric.ball x r ∧ 0 < (star d * (z - x)).im at hz
  change (star d * (z - x)).im = 0 at hzline
  rw [hzline] at hz
  exact (lt_irrefl 0) hz.2

/-- Helper toward Proposition 5.16: each half-disc misses its supporting line. -/
theorem disjoint_rightHalfDisc_edgeLine (x d : ℂ) (r : ℝ) :
    Disjoint (rightHalfDisc x d r) (edgeLine x d) := by
  apply Set.disjoint_left.mpr
  intro z hz hzline
  change z ∈ Metric.ball x r ∧ (star d * (z - x)).im < 0 at hz
  change (star d * (z - x)).im = 0 at hzline
  rw [hzline] at hz
  exact (lt_irrefl 0) hz.2

/-- Helper toward Proposition 5.16: local half-discs at an interior point of
a simple linear polyline avoid its full image. The cyclic endpoint join is not
part of `Polyline.IsSimple` and is handled separately. -/
theorem exists_local_halfDiscs_avoiding_image (p : Polyline)
    (hsimple : p.IsSimple) (hlen : 2 ≤ p.points.length)
    (i : ℕ) (hi : i + 1 < p.points.length) (x : ℂ)
    (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1)) :
    ∃ r : ℝ, 0 < r ∧
      IsOpen (leftHalfDisc x (p.point (i + 1) - p.point i) r) ∧
      IsOpen (rightHalfDisc x (p.point (i + 1) - p.point i) r) ∧
      (leftHalfDisc x (p.point (i + 1) - p.point i) r).Nonempty ∧
      (rightHalfDisc x (p.point (i + 1) - p.point i) r).Nonempty ∧
      IsConnected (leftHalfDisc x (p.point (i + 1) - p.point i) r) ∧
      IsConnected (rightHalfDisc x (p.point (i + 1) - p.point i) r) ∧
      Disjoint (leftHalfDisc x (p.point (i + 1) - p.point i) r) p.image ∧
      Disjoint (rightHalfDisc x (p.point (i + 1) - p.point i) r) p.image := by
  obtain ⟨r, hr, havoid⟩ :=
    exists_pos_ball_avoiding_nonincident_segments p hsimple i hi x hx hxi hxi1
  let d : ℂ := p.point (i + 1) - p.point i
  have hd : d ≠ 0 := by
    dsimp [d]
    exact sub_ne_zero.mpr (Ne.symm (hsimple.1 i hi))
  have hownLeft : Disjoint (leftHalfDisc x d r) (p.segmentAt i) := by
    apply Set.disjoint_left.mpr
    intro z hz hzseg
    have hzline : z ∈ edgeLine x d :=
      segment_subset_edgeLine (p.point i) (p.point (i + 1)) x hx hzseg
    exact (Set.disjoint_left.mp (disjoint_leftHalfDisc_edgeLine x d r)) hz hzline
  have hownRight : Disjoint (rightHalfDisc x d r) (p.segmentAt i) := by
    apply Set.disjoint_left.mpr
    intro z hz hzseg
    have hzline : z ∈ edgeLine x d :=
      segment_subset_edgeLine (p.point i) (p.point (i + 1)) x hx hzseg
    exact (Set.disjoint_left.mp (disjoint_rightHalfDisc_edgeLine x d r)) hz hzline
  have hpoint0 : p.point 0 = p.start := by
    cases hp : p.points with
    | nil => exact (p.nonempty hp).elim
    | cons a l => simp [point, start, hp]
  have hstartseg : p.start ∈ p.segmentAt 0 := by
    rw [← hpoint0]
    exact left_mem_segment ℝ _ _
  have hzero : 0 + 1 < p.points.length := by omega
  have hleftNonempty := leftHalfDisc_nonempty x d r hd hr
  have hrightNonempty := rightHalfDisc_nonempty x d r hd hr
  have hleftConn := isConnected_leftHalfDisc x d r hleftNonempty
  have hrightConn := isConnected_rightHalfDisc x d r hrightNonempty
  have hleftImage : Disjoint (leftHalfDisc x d r) p.image := by
    apply Set.disjoint_left.mpr
    intro z hz hzimage
    change z ∈ Metric.ball x r ∧ 0 < (star d * (z - x)).im at hz
    change z ∈ {p.start} ∪ {w | ∃ j, j + 1 < p.points.length ∧ w ∈ p.segmentAt j} at hzimage
    rcases hzimage with hzstart | ⟨j, hj, hzseg⟩
    · by_cases hi0 : i = 0
      · have hzseg0 : z ∈ p.segmentAt i := by
          have hzEq : z = p.start := by simpa using hzstart
          subst z
          simpa [hi0] using hstartseg
        exact (Set.disjoint_left.mp hownLeft) hz hzseg0
      · have hzdist : dist z x < r := by
          exact Metric.mem_ball.mp hz.1
        have hzEq : z = p.start := by simpa using hzstart
        subst z
        exact havoid p.start hzdist 0 hzero (by omega) hstartseg
    · by_cases hji : j = i
      · subst j
        exact (Set.disjoint_left.mp hownLeft) hz hzseg
      · have hzdist : dist z x < r := by
          exact Metric.mem_ball.mp hz.1
        exact havoid z hzdist j hj hji hzseg
  have hrightImage : Disjoint (rightHalfDisc x d r) p.image := by
    apply Set.disjoint_left.mpr
    intro z hz hzimage
    change z ∈ Metric.ball x r ∧ (star d * (z - x)).im < 0 at hz
    change z ∈ {p.start} ∪ {w | ∃ j, j + 1 < p.points.length ∧ w ∈ p.segmentAt j} at hzimage
    rcases hzimage with hzstart | ⟨j, hj, hzseg⟩
    · by_cases hi0 : i = 0
      · have hzseg0 : z ∈ p.segmentAt i := by
          have hzEq : z = p.start := by simpa using hzstart
          subst z
          simpa [hi0] using hstartseg
        exact (Set.disjoint_left.mp hownRight) hz hzseg0
      · have hzdist : dist z x < r := by
          exact Metric.mem_ball.mp hz.1
        have hzEq : z = p.start := by simpa using hzstart
        subst z
        exact havoid p.start hzdist 0 hzero (by omega) hstartseg
    · by_cases hji : j = i
      · subst j
        exact (Set.disjoint_left.mp hownRight) hz hzseg
      · have hzdist : dist z x < r := by
          exact Metric.mem_ball.mp hz.1
        exact havoid z hzdist j hj hji hzseg
  refine ⟨r, hr, isOpen_leftHalfDisc x d r, isOpen_rightHalfDisc x d r,
    hleftNonempty, hrightNonempty, hleftConn, hrightConn, hleftImage, hrightImage⟩

/-- Helper toward Proposition 5.16: deleting the supporting line from a ball
partitions it into the two open half-discs. -/
theorem ball_diff_edgeLine_eq_halfDiscs (x d : ℂ) (r : ℝ) :
    Metric.ball x r \ edgeLine x d = leftHalfDisc x d r ∪ rightHalfDisc x d r := by
  ext z
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq,
    edgeLine, leftHalfDisc, rightHalfDisc]
  constructor
  · rintro ⟨hzball, hzne⟩
    rcases lt_or_gt_of_ne hzne with hneg | hpos
    · exact Or.inr ⟨hzball, hneg⟩
    · exact Or.inl ⟨hzball, hpos⟩
  · rintro (⟨hzball, hpos⟩ | ⟨hzball, hneg⟩)
    · exact ⟨hzball, ne_of_gt hpos⟩
    · exact ⟨hzball, ne_of_lt hneg⟩





















































































end Polyline
end DirectedDistances.PlanarMap

end
