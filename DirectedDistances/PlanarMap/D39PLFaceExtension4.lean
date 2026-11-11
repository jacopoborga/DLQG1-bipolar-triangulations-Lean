/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLFaceExtension3

/-! Helpers toward Proposition 5.16: orientation normalization and square winding. -/

public section
noncomputable section
namespace DirectedDistances.PlanarMap
namespace Polyline
open Set Topology

/-- Helper toward Proposition 5.16: a closed chain carried by a segment has
zero winding at every point off that segment. -/
theorem angleSum_eq_zero_of_image_subset_segment (p : Polyline)
    (hclosed : p.start = p.finish) (a b : ℂ)
    (himage : p.image ⊆ segment ℝ a b) (z : ℂ) (hz : z ∉ segment ℝ a b) :
    p.angleSum z = 0 := by
  obtain ⟨R, hR⟩ := p.exists_radius_angleSum_eq_zero hclosed
  obtain ⟨w, hw, hwR⟩ := exists_norm_gt_segment_compl a b R
  calc
    p.angleSum z = p.angleSum w :=
      p.angleSum_eq_of_isPreconnected hclosed (segment ℝ a b)ᶜ
        (isPathConnected_segment_compl a b).isConnected.isPreconnected
        (fun _ hx h => hx (himage h)) z w hz hw
    _ = 0 := hR w hwR

/-- Helper toward Proposition 5.16: subdividing a straight segment preserves
its principal angle at every viewpoint off the segment. -/
theorem arg_div_add_of_mem_segment (a b d z : ℂ)
    (hb : b ∈ segment ℝ a d) (hz : z ∉ segment ℝ a d) :
    Complex.arg ((b - z) / (a - z)) + Complex.arg ((d - z) / (b - z)) =
      Complex.arg ((d - z) / (a - z)) := by
  let p := ofHead a [b, d, a]
  have himage : p.image ⊆ segment ℝ a d := by
    rintro w (hw | ⟨i, hi, hw⟩)
    · change w = a at hw
      rw [hw]
      exact left_mem_segment ℝ _ _
    · change i + 1 < 4 at hi
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · exact (convex_segment a d).segment_subset (left_mem_segment ℝ _ _) hb hw
      · exact (convex_segment a d).segment_subset hb (right_mem_segment ℝ _ _) hw
      · exact (convex_segment a d).segment_subset
          (right_mem_segment ℝ _ _) (left_mem_segment ℝ _ _) hw
  have hzero := p.angleSum_eq_zero_of_image_subset_segment (by rfl) a d himage z hz
  have hrev := edgeAngle_reverse (diagonalArc a d) z
    (by rw [(diagonalArc_data a d).2.2.2]; exact hz) 0 (by change 1 < 2; omega)
  change Complex.arg ((a - z) / (d - z)) = -Complex.arg ((d - z) / (a - z)) at hrev
  norm_num only [angleSum, p, ofHead, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, edgeAngle, point, List.getD_cons_zero, List.getD_cons_succ] at hzero
  change (Complex.arg ((b - z) / (a - z)) + Complex.arg ((d - z) / (b - z)) +
    Complex.arg ((a - z) / (d - z))) / (2 * Real.pi) = 0 at hzero
  rw [hrev] at hzero
  have hden : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt (mul_pos (by norm_num) Real.pi_pos)
  have hsum := (div_eq_zero_iff).mp hzero
  rcases hsum with hsum | hsum
  · linarith only [hsum]
  · exact False.elim (hden hsum)

/-- Helper toward Proposition 5.16: subdivision of the two vertical square
edges preserves its counterclockwise winding. -/
theorem angleSum_square_chains_sub (R a b : ℝ) (hR : 0 < R)
    (ha : -R < a ∧ a < R) (hb : -R < b ∧ b < R)
    (z : ℂ) (hz : z ∉ (enclosingSquare R).image) :
    (squareLowerChain R a b).angleSum z - (squareUpperChain R a b).angleSum z =
      (enclosingSquare R).angleSum z := by
  let A : ℂ := ⟨-R, a⟩
  let B : ℂ := ⟨R, b⟩
  let bl : ℂ := ⟨-R, -R⟩
  let br : ℂ := ⟨R, -R⟩
  let tr : ℂ := ⟨R, R⟩
  let tl : ℂ := ⟨-R, R⟩
  have hlt : -R < R := by linarith only [hR]
  have hleftoff : z ∉ segment ℝ tl bl := by
    intro h
    exact hz (Or.inr ⟨3, by change 4 < 5; omega, h⟩)
  have hrightoff : z ∉ segment ℝ br tr := by
    intro h
    exact hz (Or.inr ⟨1, by change 2 < 5; omega, h⟩)
  have hleft := arg_div_add_of_mem_segment tl A bl z
    (by
      rw [segment_symm]
      exact (mem_vertical_segment_iff (-R) R (-R) hlt A).mpr ⟨ha.1.le, ha.2.le, rfl⟩)
    hleftoff
  have hright := arg_div_add_of_mem_segment br B tr z
    ((mem_vertical_segment_iff (-R) R R hlt B).mpr ⟨hb.1.le, hb.2.le, rfl⟩) hrightoff
  have hzu : z ∉ (squareUpperChain R a b).image := by
    intro h
    exact hz ((square_chains_image_union R a b hR ha hb) ▸ Or.inl h)
  have h0 := edgeAngle_reverse (squareUpperChain R a b) z hzu 0 (by change 1 < 4; omega)
  have h1 := edgeAngle_reverse (squareUpperChain R a b) z hzu 1 (by change 2 < 4; omega)
  have h2 := edgeAngle_reverse (squareUpperChain R a b) z hzu 2 (by change 3 < 4; omega)
  change Complex.arg ((tr - z) / (B - z)) = -Complex.arg ((B - z) / (tr - z)) at h0
  change Complex.arg ((tl - z) / (tr - z)) = -Complex.arg ((tr - z) / (tl - z)) at h1
  change Complex.arg ((A - z) / (tl - z)) = -Complex.arg ((tl - z) / (A - z)) at h2
  norm_num only [angleSum, squareLowerChain, squareUpperChain, enclosingSquare,
    ofHead, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  change (Complex.arg ((bl - z) / (A - z)) + Complex.arg ((br - z) / (bl - z)) +
      Complex.arg ((B - z) / (br - z))) / (2 * Real.pi) -
    (Complex.arg ((tl - z) / (A - z)) + Complex.arg ((tr - z) / (tl - z)) +
      Complex.arg ((B - z) / (tr - z))) / (2 * Real.pi) =
    (Complex.arg ((br - z) / (bl - z)) + Complex.arg ((tr - z) / (br - z)) +
      Complex.arg ((tl - z) / (tr - z)) + Complex.arg ((bl - z) / (tl - z))) /
      (2 * Real.pi)
  rw [← sub_div]
  congr 1
  linarith only [hleft, hright, h0, h1, h2]

/-- Helper toward Proposition 5.16: the fixed square has counterclockwise
winding one at its center. -/
theorem enclosingSquare_angleSum_zero (R : ℝ) (hR : 0 < R) :
    (enclosingSquare R).angleSum 0 = 1 := by
  let bl : ℂ := ⟨-R, -R⟩
  let br : ℂ := ⟨R, -R⟩
  let tr : ℂ := ⟨R, R⟩
  let tl : ℂ := ⟨-R, R⟩
  have hbl : bl ≠ 0 := by intro h; have := congrArg Complex.im h; change -R = 0 at this; linarith
  have hbr : br ≠ 0 := by intro h; have := congrArg Complex.re h; exact (ne_of_gt hR) this
  have htr : tr ≠ 0 := by intro h; have := congrArg Complex.re h; exact (ne_of_gt hR) this
  have htl : tl ≠ 0 := by intro h; have := congrArg Complex.im h; exact (ne_of_gt hR) this
  have h0 : br / bl = Complex.I := by
    apply (div_eq_iff hbl).mpr
    apply Complex.ext <;> simp [bl, br, Complex.mul_re, Complex.mul_im]
  have h1 : tr / br = Complex.I := by
    apply (div_eq_iff hbr).mpr
    apply Complex.ext <;> simp [br, tr, Complex.mul_re, Complex.mul_im]
  have h2 : tl / tr = Complex.I := by
    apply (div_eq_iff htr).mpr
    apply Complex.ext <;> simp [tl, tr, Complex.mul_re, Complex.mul_im]
  have h3 : bl / tl = Complex.I := by
    apply (div_eq_iff htl).mpr
    apply Complex.ext <;> simp [bl, tl, Complex.mul_re, Complex.mul_im]
  norm_num only [angleSum, enclosingSquare, ofHead, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  change (Complex.arg ((br - 0) / (bl - 0)) + Complex.arg ((tr - 0) / (br - 0)) +
    Complex.arg ((tl - 0) / (tr - 0)) + Complex.arg ((bl - 0) / (tl - 0))) /
      (2 * Real.pi) = 1
  simp only [sub_zero, h0, h1, h2, h3, Complex.arg_I]
  field_simp
  ring

/-- Helper toward Proposition 5.16: the fixed square has winding one
throughout its inside. -/
theorem enclosingSquare_angleSum_of_mem_inside (R : ℝ) (hR : 0 < R)
    (z : ℂ) (hz : z ∈ (enclosingSquare R).inside) :
    (enclosingSquare R).angleSum z = 1 := by
  have hzero : (0 : ℂ) ∈ (enclosingSquare R).inside := by
    rw [enclosingSquare_inside R hR]
    exact ⟨⟨by simpa using neg_neg_of_pos hR, hR⟩,
      ⟨by simpa using neg_neg_of_pos hR, hR⟩⟩
  calc
    (enclosingSquare R).angleSum z = (enclosingSquare R).angleSum 0 :=
      (enclosingSquare R).angleSum_eq_of_isPreconnected rfl _
        ((enclosingSquare R).isConnected_inside_outside_cyclic
          (enclosingSquare_isCyclicSimple R hR)).1.isPreconnected
        (fun _ h => h.1) z 0 hz hzero
    _ = 1 := enclosingSquare_angleSum_zero R hR

/-- Helper toward Proposition 5.16: reversal preserves cyclic simplicity. -/
theorem isCyclicSimple_reverse (c : Polyline) (hc : c.IsCyclicSimple) :
    c.reverse.IsCyclicSimple := by
  have hlen : c.reverse.points.length = c.points.length := List.length_reverse
  have hcLen := hc.1
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlen, point_reverse_transfer c (by omega), point_reverse_transfer c (by omega)]
    simpa only [Nat.sub_zero, Nat.sub_self] using hc.2.1.symm
  · intro i hi
    rw [hlen] at hi
    rw [point_reverse_transfer c (by omega), point_reverse_transfer c (by omega),
      show c.points.length - 1 - i = c.points.length - 2 - i + 1 by omega,
      show c.points.length - 1 - (i + 1) = c.points.length - 2 - i by omega]
    exact (hc.2.2.1 _ (by omega)).symm
  · intro i hi
    rw [hlen] at hi
    rw [segmentAt_reverse_transfer c (by omega),
      segmentAt_reverse_transfer c (by omega), point_reverse_transfer c (by omega)]
    have hidx : c.points.length - 2 - i = c.points.length - 2 - (i + 1) + 1 := by omega
    rw [hidx, inter_comm, hc.2.2.2.1 _ (by omega)]
    congr 2
    omega
  · intro i j hi hj hij hwrap
    rw [hlen] at hi hj
    rw [segmentAt_reverse_transfer c (by omega), segmentAt_reverse_transfer c (by omega)]
    exact (hc.2.2.2.2.1 (c.points.length - 2 - j) (c.points.length - 2 - i)
      (by omega) (by omega) (by omega) (by rw [hlen] at hwrap; omega)).symm
  · rw [hlen, segmentAt_reverse_transfer c (by omega),
      segmentAt_reverse_transfer c (by omega), point_reverse_transfer c (by omega)]
    rw [Nat.sub_zero, show c.points.length - 2 - (c.points.length - 2) = 0 by omega,
      inter_comm, hc.2.2.2.2.2, hc.2.1, Nat.sub_zero]

/-- Helper toward Proposition 5.16: reversal preserves the winding-defined inside. -/
theorem inside_reverse (c : Polyline) : c.reverse.inside = c.inside := by
  ext z
  change (z ∉ c.reverse.image ∧ c.reverse.angleSum z ≠ 0) ↔
    (z ∉ c.image ∧ c.angleSum z ≠ 0)
  rw [image_reverse_transfer]
  by_cases hz : z ∈ c.image
  · simp only [hz, not_true_eq_false, false_and]
  · rw [angleSum_reverse c z hz, neg_ne_zero]

/-- Helper toward Proposition 5.16: reversal preserves the winding-defined outside. -/
theorem outside_reverse (c : Polyline) : c.reverse.outside = c.outside := by
  ext z
  change (z ∉ c.reverse.image ∧ c.reverse.angleSum z = 0) ↔
    (z ∉ c.image ∧ c.angleSum z = 0)
  rw [image_reverse_transfer]
  by_cases hz : z ∈ c.image
  · simp only [hz, not_true_eq_false, false_and]
  · rw [angleSum_reverse c z hz, neg_eq_zero]

/-- Helper toward Proposition 5.16: a cyclic polygon has one common sign on its inside. -/
theorem exists_inside_angleSum_sign (c : Polyline) (hc : c.IsCyclicSimple) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ z ∈ c.inside, c.angleSum z = ε := by
  obtain ⟨w, hw⟩ := c.inside_nonempty_cyclic hc
  refine ⟨c.angleSum w, eq_or_eq_neg_of_abs_eq (c.abs_angleSum_eq_one_of_mem_inside hc w hw), ?_⟩
  intro z hz
  have hclosed : c.start = c.finish := by
    rw [← point_zero_eq_start, ← point_last_eq_finish]
    exact hc.2.1
  exact c.angleSum_eq_of_isPreconnected hclosed c.inside
    (c.isConnected_inside_outside_cyclic hc).1.isPreconnected (fun _ h => h.1) z w hz hw

/-- Helper toward Proposition 5.16: choose the original polygon or its reversal
to obtain winding one on the same inside, with unchanged boundary and outside. -/
theorem exists_counterclockwise_reorientation (c : Polyline) (hc : c.IsCyclicSimple) :
    ∃ d : Polyline, (d = c ∨ d = c.reverse) ∧ d.IsCyclicSimple ∧
      d.image = c.image ∧ d.inside = c.inside ∧ d.outside = c.outside ∧
      ∀ z ∈ d.inside, d.angleSum z = 1 := by
  obtain ⟨ε, hε, hsign⟩ := c.exists_inside_angleSum_sign hc
  rcases hε with rfl | rfl
  · exact ⟨c, Or.inl rfl, hc, rfl, rfl, rfl, hsign⟩
  · refine ⟨c.reverse, Or.inr rfl, c.isCyclicSimple_reverse hc,
      image_reverse_transfer c, inside_reverse c, outside_reverse c, ?_⟩
    intro z hz
    rw [inside_reverse] at hz
    rw [angleSum_reverse c z hz.1, hsign z hz]
    norm_num

/-- Helper toward Proposition 5.16: after counterclockwise normalization,
every off-boundary winding is zero or one, and one characterizes the inside. -/
theorem angleSum_zero_or_one_of_counterclockwise (c : Polyline)
    (hccw : ∀ w ∈ c.inside, c.angleSum w = 1) (z : ℂ) (hz : z ∉ c.image) :
    (c.angleSum z = 0 ∨ c.angleSum z = 1) ∧
      (c.angleSum z = 1 ↔ z ∈ c.inside) := by
  have hvalues : c.angleSum z = 0 ∨ c.angleSum z = 1 := by
    by_cases hzero : c.angleSum z = 0
    · exact Or.inl hzero
    · exact Or.inr (hccw z ⟨hz, hzero⟩)
  refine ⟨hvalues, ?_⟩
  constructor
  · intro hone
    exact ⟨hz, by rw [hone]; norm_num⟩
  · exact hccw z

/-- Helper toward Proposition 5.16: if a closed chain lies strictly above
a horizontal line, the entire closed lower half-plane is outside. -/
theorem im_le_subset_outside_of_image_im_gt (c : Polyline)
    (hclosed : c.start = c.finish) (a : ℝ)
    (hbound : ∀ w ∈ c.image, a < w.im) :
    {z : ℂ | z.im ≤ a} ⊆ c.outside := by
  intro z hz
  let w : ℂ := ⟨0, a - 1⟩
  have hw : w ∈ c.outside :=
    c.im_lt_subset_outside hclosed a (fun u hu => (hbound u hu).le) (by
      change a - 1 < a
      linarith)
  have hzoff : z ∉ c.image := fun h => (not_lt_of_ge hz) (hbound z h)
  refine ⟨hzoff, ?_⟩
  calc
    c.angleSum z = c.angleSum w :=
      c.angleSum_eq_of_isPreconnected hclosed {u : ℂ | u.im ≤ a}
        (convex_halfSpace_im_le a).isPreconnected
        (fun u hu him => (not_lt_of_ge hu) (hbound u him)) z w hz (by
          change a - 1 ≤ a
          linarith)
    _ = 0 := hw.2

/-- Helper toward Proposition 5.16: if a closed chain lies strictly below
a horizontal line, the entire closed upper half-plane is outside. -/
theorem im_ge_subset_outside_of_image_im_lt (c : Polyline)
    (hclosed : c.start = c.finish) (a : ℝ)
    (hbound : ∀ w ∈ c.image, w.im < a) :
    {z : ℂ | a ≤ z.im} ⊆ c.outside := by
  intro z hz
  let w : ℂ := ⟨0, a + 1⟩
  have hw : w ∈ c.outside :=
    c.im_gt_subset_outside hclosed a (fun u hu => (hbound u hu).le) (by
      change a < a + 1
      linarith)
  have hzoff : z ∉ c.image := fun h => (not_lt_of_ge hz) (hbound z h)
  refine ⟨hzoff, ?_⟩
  calc
    c.angleSum z = c.angleSum w :=
      c.angleSum_eq_of_isPreconnected hclosed {u : ℂ | a ≤ u.im}
        (convex_halfSpace_im_ge a).isPreconnected
        (fun u hu him => (not_lt_of_ge hu) (hbound u him)) z w hz (by
          change a ≤ a + 1
          linarith)
    _ = 0 := hw.2

/-- Helper toward Proposition 5.16: cancellation of both slits and both inner
arcs gives the square winding minus the inner winding. This identity alone
does not identify the closed regions of the displayed loops. -/
theorem angleSum_annulus_chains_eq_square_sub (c : Polyline) (hc : c.IsCyclicSimple)
    (i j : ℕ) (hij : i < j) (hj : j + 1 < c.points.length)
    (R : ℝ) (hR : 0 < R)
    (ha : -R < (c.point i).im ∧ (c.point i).im < R)
    (hb : -R < (c.point j).im ∧ (c.point j).im < R) :
    let a := c.point i
    let b := c.point j
    let s := diagonalArc a (⟨-R, a.im⟩ : ℂ)
    let t := diagonalArc (⟨R, b.im⟩ : ℂ) b
    let U := boundaryConcat (boundaryConcat s (squareUpperChain R a.im b.im)) t
    let V := boundaryConcat (boundaryConcat s (squareLowerChain R a.im b.im)) t
    ∀ z : ℂ, z ∉ (c.image ∪ (enclosingSquare R).image) ∪ (U.image ∪ V.image) →
      (closedConcat V (c.intervalPolyline i (j - i))).angleSum z +
        (closedConcat (c.diagonalComplement i j).reverse U).angleSum z =
          (enclosingSquare R).angleSum z - c.angleSum z := by
  dsimp only
  intro z hz
  have hcancel := c.angleSum_annulus_chains hc i j hij hj R z
    (fun h => hz (h.elim (fun h => Or.inl (Or.inl h)) Or.inr))
  rw [angleSum_square_chains_sub R (c.point i).im (c.point j).im hR ha hb z
    (fun h => hz (Or.inl (Or.inr h)))] at hcancel
  exact hcancel

/-- Helper toward Proposition 5.16: the same cancellation identity is valid
off the images of the actual closed loops, with the slit chains eliminated
from its avoidance condition. -/
theorem angleSum_annulus_loops_eq_square_sub (c : Polyline) (hc : c.IsCyclicSimple)
    (i j : ℕ) (hij : i < j) (hj : j + 1 < c.points.length)
    (R : ℝ) (hR : 0 < R)
    (ha : -R < (c.point i).im ∧ (c.point i).im < R)
    (hb : -R < (c.point j).im ∧ (c.point j).im < R) :
    let a := c.point i
    let b := c.point j
    let s := diagonalArc a (⟨-R, a.im⟩ : ℂ)
    let t := diagonalArc (⟨R, b.im⟩ : ℂ) b
    let U := boundaryConcat (boundaryConcat s (squareUpperChain R a.im b.im)) t
    let V := boundaryConcat (boundaryConcat s (squareLowerChain R a.im b.im)) t
    let p := closedConcat V (c.intervalPolyline i (j - i))
    let q := closedConcat (c.diagonalComplement i j).reverse U
    ∀ z : ℂ, z ∉ (c.image ∪ (enclosingSquare R).image) ∪ (p.image ∪ q.image) →
      p.angleSum z + q.angleSum z = (enclosingSquare R).angleSum z - c.angleSum z := by
  dsimp only
  intro z hz
  let a := c.point i
  let b := c.point j
  let s := diagonalArc a (⟨-R, a.im⟩ : ℂ)
  let t := diagonalArc (⟨R, b.im⟩ : ℂ) b
  let U := boundaryConcat (boundaryConcat s (squareUpperChain R a.im b.im)) t
  let V := boundaryConcat (boundaryConcat s (squareLowerChain R a.im b.im)) t
  have hUf : U.finish = b := by
    rw [finish_boundaryConcat _ _ (by change 2 ≤ 2; omega)]
    rfl
  have hVf : V.finish = b := by
    rw [finish_boundaryConcat _ _ (by change 2 ≤ 2; omega)]
    rfl
  have hxf : (c.intervalPolyline i (j - i)).finish = b := by
    rw [finish_intervalPolyline, show i + (j - i) = j by omega]
  have hyf : (c.diagonalComplement i j).reverse.finish = b := by
    rw [finish_reverse, (c.diagonalComplement_data hc i j hij hj).1]
  apply c.angleSum_annulus_chains_eq_square_sub hc i j hij hj R hR ha hb z
  rintro (hzc | hzUV)
  · exact hz (Or.inl hzc)
  · rcases hzUV with hzU | hzV
    · apply hz
      right
      right
      rw [image_closedConcat _ U (hyf.trans hUf.symm)]
      exact Or.inr hzU
    · apply hz
      right
      left
      rw [image_closedConcat V _ (hVf.trans hxf.symm)]
      exact Or.inl hzV

/-- Helper toward Proposition 5.16: the exterior slits produce two genuinely
cyclically simple loops with the signed square-minus-inner winding identity.
Their closed-region partition is established separately below after normalization. -/
theorem exists_cyclic_annulus_loops_winding (c : Polyline) (hc : c.IsCyclicSimple) :
    ∃ (R : ℝ) (s t p q : Polyline), 0 < R ∧
      closure c.inside ⊆ (enclosingSquare R).inside ∧
      s.IsSimple ∧ t.IsSimple ∧ Disjoint s.image t.image ∧
      s.image ∩ c.image = {s.start} ∧ t.image ∩ c.image = {t.start} ∧
      s.image ∩ (enclosingSquare R).image = {s.finish} ∧
      t.image ∩ (enclosingSquare R).image = {t.finish} ∧
      p.IsCyclicSimple ∧ q.IsCyclicSimple ∧
      (∀ z : ℂ, z ∉ (c.image ∪ (enclosingSquare R).image) ∪ (p.image ∪ q.image) →
        p.angleSum z + q.angleSum z = (enclosingSquare R).angleSum z - c.angleSum z) ∧
      (∀ z ∈ p.inside, p.angleSum z = 1) ∧ (∀ z ∈ q.inside, q.angleSum z = 1) ∧
      p.image ∪ q.image =
        (c.image ∪ (enclosingSquare R).image) ∪ (s.image ∪ t.image) ∧
      p.image ∩ q.image = s.image ∪ t.image ∧
      s.image ∪ t.image ⊆ closure c.outside ∩ closure (enclosingSquare R).inside ∧
      p.inside ⊆ (enclosingSquare R).inside ∧ q.inside ⊆ (enclosingSquare R).inside := by
  obtain ⟨R, i, j, hR, hi, hj, hbox, hdata⟩ :=
    c.exists_disjoint_horizontal_exterior_slits hc
  dsimp only at hdata
  obtain ⟨hab, haim, hbim, hs, ht, hsinter, htinter, hdisj, hcontain⟩ := hdata
  let a := c.point i
  let b := c.point j
  let l : ℂ := ⟨-R, a.im⟩
  let r : ℂ := ⟨R, b.im⟩
  let s := diagonalArc a l
  let t := diagonalArc r b
  let u := squareUpperChain R a.im b.im
  let v := squareLowerChain R a.im b.im
  let U := boundaryConcat (boundaryConcat s u) t
  let V := boundaryConcat (boundaryConcat s v) t
  have hnest : closure c.inside ⊆ (enclosingSquare R).inside := by
    intro z hz
    rw [enclosingSquare_inside R hR]
    exact ⟨abs_lt.mp (hbox z hz).1, abs_lt.mp (hbox z hz).2⟩
  have ha : a ∈ (enclosingSquare R).inside :=
    hnest (c.image_subset_closure_inside_cyclic hc (c.point_mem_image hi))
  have hb : b ∈ (enclosingSquare R).inside :=
    hnest (c.image_subset_closure_inside_cyclic hc (c.point_mem_image hj))
  have hne : a ≠ b := fun h => (ne_of_lt hab) (congrArg Complex.re h)
  have huq : u.image ⊆ (enclosingSquare R).image := by
    rw [← square_chains_image_union R a.im b.im hR (abs_lt.mp haim) (abs_lt.mp hbim)]
    exact subset_union_left
  have hvq : v.image ⊆ (enclosingSquare R).image := by
    rw [← square_chains_image_union R a.im b.im hR (abs_lt.mp haim) (abs_lt.mp hbim)]
    exact subset_union_right
  obtain ⟨hU, hUlen, hUs, hUf, hUim⟩ :=
    square_bypass_data R hR a b ha hb hab u
      (squareUpperChain_isSimple R a.im b.im hR (abs_lt.mp haim).2 (abs_lt.mp hbim).2)
      (by change 2 ≤ 4; omega) rfl rfl huq
  obtain ⟨hV, hVlen, hVs, hVf, hVim⟩ :=
    square_bypass_data R hR a b ha hb hab v
      (squareLowerChain_isSimple R a.im b.im hR (abs_lt.mp haim).1 (abs_lt.mp hbim).1)
      (by change 2 ≤ 4; omega) rfl rfl hvq
  obtain ⟨x, y, hx, hy, hxlen, hylen, hxs, hxf, hys, hyf, hxy, hxyinter, hangle⟩ :=
    c.exists_inner_boundary_chains hc i j hi hj hne
  have hxsub : x.image ⊆ c.image := by rw [← hxy]; exact subset_union_left
  have hysub : y.image ⊆ c.image := by rw [← hxy]; exact subset_union_right
  have hcontact (o : Polyline) (ho : o.image ⊆ (enclosingSquare R).image) :
      ((segment ℝ a l ∪ o.image) ∪ segment ℝ b r) ∩ c.image = {a, b} := by
    have havoid : o.image ∩ c.image = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨hzo, hzc⟩
      exact (hnest (c.image_subset_closure_inside_cyclic hc hzc)).1 (ho hzo)
    rw [union_inter_distrib_right, union_inter_distrib_right,
      ← (diagonalArc_data a l).2.2.2, ← (diagonalArc_data b r).2.2.2,
      hsinter, htinter, havoid, union_empty]
    rfl
  have hUc : U.image ∩ c.image = {a, b} := by rw [hUim]; exact hcontact u huq
  have hVc : V.image ∩ c.image = {a, b} := by rw [hVim]; exact hcontact v hvq
  have hinter (w W : Polyline) (hwlen : 2 ≤ w.points.length)
      (hws : w.start = a) (hwf : w.finish = b) (hwsub : w.image ⊆ c.image)
      (hWlen : 2 ≤ W.points.length) (hWs : W.start = a) (hWf : W.finish = b)
      (hWc : W.image ∩ c.image = {a, b}) : w.image ∩ W.image = {w.start, w.finish} := by
    rw [hws, hwf]
    apply Set.Subset.antisymm
    · rintro z ⟨hzw, hzW⟩
      exact hWc ▸ ⟨hzW, hwsub hzw⟩
    · rintro z (rfl | rfl)
      · exact ⟨by rw [← hws]; exact Or.inl rfl, by rw [← hWs]; exact Or.inl rfl⟩
      · constructor
        · rw [← hwf, ← point_last_eq_finish]; exact w.point_mem_image (by omega)
        · rw [← hWf, ← point_last_eq_finish]; exact W.point_mem_image (by omega)
  have hyrlen : 2 ≤ y.reverse.points.length := by simpa only [reverse, List.length_reverse] using hylen
  have hyrs : y.reverse.start = a := (start_reverse y).trans hyf
  have hyrf : y.reverse.finish = b := (finish_reverse y).trans hys
  have hyrsub : y.reverse.image ⊆ c.image := by rw [image_reverse_transfer]; exact hysub
  have hxV : (closedConcat x V).IsCyclicSimple := closedConcat_isCyclicSimple x V hx hV
    hxlen hVlen (hxs.trans hVs.symm) (hxf.trans hVf.symm)
    (by rw [hxs, hxf]; exact hne)
    (hinter x V hxlen hxs hxf hxsub hVlen hVs hVf hVc)
  have hyU : (closedConcat y.reverse U).IsCyclicSimple := closedConcat_isCyclicSimple
    y.reverse U (isSimple_reverse_transfer y hy) hU hyrlen hUlen
    (hyrs.trans hUs.symm) (hyrf.trans hUf.symm)
    (by rw [hyrs, hyrf]; exact hne)
    (hinter y.reverse U hyrlen hyrs hyrf hyrsub hUlen hUs hUf hUc)
  let p := (closedConcat x V).reverse
  let q := closedConcat y.reverse U
  have hp : p.IsCyclicSimple := isCyclicSimple_reverse _ hxV
  have hq : q.IsCyclicSimple := hyU
  have hsum : ∀ z : ℂ,
      z ∉ (c.image ∪ (enclosingSquare R).image) ∪ (p.image ∪ q.image) →
      p.angleSum z + q.angleSum z = (enclosingSquare R).angleSum z - c.angleSum z := by
    intro z hz
    have hzxV : z ∉ (closedConcat x V).image := by
      intro h
      exact hz (Or.inr (Or.inl ((image_reverse_transfer _).symm ▸ h)))
    have hzU : z ∉ U.image := by
      intro h
      exact hz (Or.inr (Or.inr ((image_closedConcat _ U (hyrf.trans hUf.symm)).symm ▸ Or.inr h)))
    have hzV : z ∉ V.image := by
      intro h
      exact hzxV ((image_closedConcat x V (hxf.trans hVf.symm)).symm ▸ Or.inr h)
    have hzy : z ∉ y.image := fun h => hz (Or.inl (Or.inl (hysub h)))
    change (closedConcat x V).reverse.angleSum z + (closedConcat y.reverse U).angleSum z = _
    rw [angleSum_reverse _ z hzxV, angleSum_closedConcat x V (hxf.trans hVf.symm) z hzV,
      angleSum_closedConcat y.reverse U (hyrf.trans hUf.symm) z hzU, angleSum_reverse y z hzy]
    have hbypass := angleSum_square_bypass_sub R a b z
    change U.angleSum z - V.angleSum z = u.angleSum z - v.angleSum z at hbypass
    have hsquare := angleSum_square_chains_sub R a.im b.im hR
      (abs_lt.mp haim) (abs_lt.mp hbim) z (fun h => hz (Or.inl (Or.inr h)))
    change v.angleSum z - u.angleSum z = _ at hsquare
    have hinner := hangle z
    linarith only [hbypass, hsquare, hinner]
  have hpim : p.image = x.image ∪ ((segment ℝ a l ∪ v.image) ∪ segment ℝ b r) := by
    dsimp only [p]
    rw [image_reverse_transfer, image_closedConcat x V (hxf.trans hVf.symm), hVim]
  have hqim : q.image = y.image ∪ ((segment ℝ a l ∪ u.image) ∪ segment ℝ b r) := by
    dsimp only [q]
    rw [image_closedConcat y.reverse U (hyrf.trans hUf.symm), image_reverse_transfer, hUim]
  have hcim (w : ℂ) (hw : w ∈ c.image) : -R < w.im ∧ w.im < R :=
    abs_lt.mp (hbox w (c.image_subset_closure_inside_cyclic hc hw)).2
  have hqabove : ∀ w ∈ q.image, -R < w.im := by
    intro w hw
    rw [hqim] at hw
    rcases hw with hw | (hw | hw) | hw
    · exact (hcim w (hysub hw)).1
    · exact (convex_halfSpace_im_gt (-R)).segment_subset
        (x := a) (y := l) (abs_lt.mp haim).1 (abs_lt.mp haim).1 hw
    · rcases (mem_squareUpperChain_image_iff R a.im b.im hR
        (abs_lt.mp haim).2 (abs_lt.mp hbim).2 w).mp hw with h | h | h
      · exact (abs_lt.mp haim).1.trans_le h.1
      · rw [h.2.2]; linarith only [hR]
      · exact (abs_lt.mp hbim).1.trans_le h.1
    · exact (convex_halfSpace_im_gt (-R)).segment_subset
        (x := b) (y := r) (abs_lt.mp hbim).1 (abs_lt.mp hbim).1 hw
  have hpbelow : ∀ w ∈ p.image, w.im < R := by
    intro w hw
    rw [hpim] at hw
    rcases hw with hw | (hw | hw) | hw
    · exact (hcim w (hxsub hw)).2
    · exact (convex_halfSpace_im_lt R).segment_subset
        (x := a) (y := l) (abs_lt.mp haim).2 (abs_lt.mp haim).2 hw
    · rcases (mem_squareLowerChain_image_iff R a.im b.im hR
        (abs_lt.mp haim).1 (abs_lt.mp hbim).1 w).mp hw with h | h | h
      · exact h.2.1.trans_lt (abs_lt.mp haim).2
      · rw [h.2.2]; linarith only [hR]
      · exact h.2.1.trans_lt (abs_lt.mp hbim).2
    · exact (convex_halfSpace_im_lt R).segment_subset
        (x := b) (y := r) (abs_lt.mp hbim).2 (abs_lt.mp hbim).2 hw
  have hclosed (d : Polyline) (hd : d.IsCyclicSimple) : d.start = d.finish := by
    rw [← point_zero_eq_start, ← point_last_eq_finish]
    exact hd.2.1
  have havoidp (z : ℂ) (hzc : z ∈ c.outside)
      (hzS : z ∈ (enclosingSquare R).inside) (hzq : z ∈ q.outside) : z ∉ p.image := by
    rw [hpim]
    rintro (hxz | (hsz | hvz) | htz)
    · exact hzc.1 (hxsub hxz)
    · exact hzq.1 (hqim.symm ▸ Or.inr (Or.inl (Or.inl hsz)))
    · exact hzS.1 (hvq hvz)
    · exact hzq.1 (hqim.symm ▸ Or.inr (Or.inr htz))
  have havoidq (z : ℂ) (hzc : z ∈ c.outside)
      (hzS : z ∈ (enclosingSquare R).inside) (hzp : z ∈ p.outside) : z ∉ q.image := by
    rw [hqim]
    rintro (hyz | (hsz | huz) | htz)
    · exact hzc.1 (hysub hyz)
    · exact hzp.1 (hpim.symm ▸ Or.inr (Or.inl (Or.inl hsz)))
    · exact hzS.1 (huq huz)
    · exact hzp.1 (hpim.symm ▸ Or.inr (Or.inr htz))
  have hbase (z : ℂ) (hzS : z ∈ closure (enclosingSquare R).inside)
      (hzc : z ∈ c.outside) (hzq : z ∈ q.outside) : ∃ w ∈ p.inside, p.angleSum w = 1 := by
    obtain ⟨w, ⟨hwc, hwq⟩, hwS⟩ := mem_closure_iff.mp hzS
      (c.outside ∩ q.outside) ((c.isOpen_outside (hclosed c hc)).inter
        (q.isOpen_outside (hclosed q hq))) ⟨hzc, hzq⟩
    have hwp := havoidp w hwc hwS hwq
    have hoff : w ∉ (c.image ∪ (enclosingSquare R).image) ∪ (p.image ∪ q.image) := by
      rintro ((hc | hS) | hp | hq)
      · exact hwc.1 hc
      · exact hwS.1 hS
      · exact hwp hp
      · exact hwq.1 hq
    have h := hsum w hoff
    rw [enclosingSquare_angleSum_of_mem_inside R hR w hwS, hwc.2, hwq.2] at h
    have hone : p.angleSum w = 1 := by linarith only [h]
    exact ⟨w, ⟨hwp, by rw [hone]; norm_num⟩, hone⟩
  let bottom : ℂ := ⟨0, -R⟩
  have hbottom : bottom ∈ closure (enclosingSquare R).inside := by
    rw [enclosingSquare_closure_inside R hR]
    exact ⟨by simp only [bottom, abs_zero]; exact hR.le,
      by simp only [bottom, abs_neg, abs_of_pos hR]; exact le_rfl⟩
  obtain ⟨w, hwp, hwone⟩ := hbase bottom hbottom
    (c.im_le_subset_outside_of_image_im_gt (hclosed c hc) (-R)
      (fun w hw => (hcim w hw).1) (by change -R ≤ -R; exact le_rfl))
    (q.im_le_subset_outside_of_image_im_gt (hclosed q hq) (-R) hqabove (by
      change -R ≤ -R
      exact le_rfl))
  have hpone : ∀ z ∈ p.inside, p.angleSum z = 1 := by
    intro z hz
    rw [← hwone]
    exact p.angleSum_eq_of_isPreconnected (hclosed p hp) p.inside
      (p.isConnected_inside_outside_cyclic hp).1.isPreconnected (fun _ h => h.1) z w hz hwp
  let top : ℂ := ⟨0, R⟩
  have htop : top ∈ closure (enclosingSquare R).inside := by
    rw [enclosingSquare_closure_inside R hR]
    exact ⟨by simp only [top, abs_zero]; exact hR.le,
      by simp only [top, abs_of_pos hR]; exact le_rfl⟩
  have htc : top ∈ c.outside := c.im_ge_subset_outside_of_image_im_lt (hclosed c hc) R
    (fun w hw => (hcim w hw).2) (by change R ≤ R; exact le_rfl)
  have htp : top ∈ p.outside := p.im_ge_subset_outside_of_image_im_lt (hclosed p hp) R hpbelow
    (by change R ≤ R; exact le_rfl)
  obtain ⟨w', ⟨hwc, hwp'⟩, hwS⟩ := mem_closure_iff.mp htop
    (c.outside ∩ p.outside) ((c.isOpen_outside (hclosed c hc)).inter
      (p.isOpen_outside (hclosed p hp))) ⟨htc, htp⟩
  have hwq := havoidq w' hwc hwS hwp'
  have hoff : w' ∉ (c.image ∪ (enclosingSquare R).image) ∪ (p.image ∪ q.image) := by
    rintro ((hc | hS) | hp | hq)
    · exact hwc.1 hc
    · exact hwS.1 hS
    · exact hwp'.1 hp
    · exact hwq hq
  have h := hsum w' hoff
  rw [enclosingSquare_angleSum_of_mem_inside R hR w' hwS, hwc.2, hwp'.2] at h
  have hqone : q.angleSum w' = 1 := by linarith only [h]
  have hwqinside : w' ∈ q.inside := ⟨hwq, by rw [hqone]; norm_num⟩
  have hqoneall : ∀ z ∈ q.inside, q.angleSum z = 1 := by
    intro z hz
    rw [← hqone]
    exact q.angleSum_eq_of_isPreconnected (hclosed q hq) q.inside
      (q.isConnected_inside_outside_cyclic hq).1.isPreconnected (fun _ h => h.1) z w' hz hwqinside
  refine ⟨R, s, diagonalArc b r, p, q, hR, hnest, hs, ht, hdisj, hsinter, htinter,
    ?_, ?_, hp, hq, hsum, hpone, hqoneall, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(diagonalArc_data a l).2.2.2]
    exact (left_slit_inter_enclosingSquare R hR a ha).1
  · rw [(diagonalArc_data b r).2.2.2]
    exact (right_slit_inter_enclosingSquare R hR b hb).1
  · rw [hpim, hqim, (diagonalArc_data a l).2.2.2, (diagonalArc_data b r).2.2.2]
    have huv : u.image ∪ v.image = (enclosingSquare R).image :=
      square_chains_image_union R a.im b.im hR (abs_lt.mp haim) (abs_lt.mp hbim)
    rw [← hxy, ← huv]
    ext z
    simp only [mem_union]
    tauto
  · rw [hpim, hqim, (diagonalArc_data a l).2.2.2, (diagonalArc_data b r).2.2.2]
    apply Set.Subset.antisymm
    · rintro z ⟨hzp, hzq⟩
      by_cases hzs : z ∈ segment ℝ a l
      · exact Or.inl hzs
      by_cases hzt : z ∈ segment ℝ b r
      · exact Or.inr hzt
      have hxp : z ∈ x.image ∨ z ∈ v.image := by
        rcases hzp with hz | (hz | hz) | hz
        · exact Or.inl hz
        · exact False.elim (hzs hz)
        · exact Or.inr hz
        · exact False.elim (hzt hz)
      have hyq : z ∈ y.image ∨ z ∈ u.image := by
        rcases hzq with hz | (hz | hz) | hz
        · exact Or.inl hz
        · exact False.elim (hzs hz)
        · exact Or.inr hz
        · exact False.elim (hzt hz)
      rcases hxp with hzx | hzv <;> rcases hyq with hzy | hzu
      · have hz : z ∈ ({a, b} : Set ℂ) := hxyinter ▸ ⟨hzx, hzy⟩
        rcases hz with rfl | rfl
        · exact Or.inl (left_mem_segment ℝ _ _)
        · exact Or.inr (left_mem_segment ℝ _ _)
      · exact False.elim ((hnest (c.image_subset_closure_inside_cyclic hc (hxsub hzx))).1 (huq hzu))
      · exact False.elim ((hnest (c.image_subset_closure_inside_cyclic hc (hysub hzy))).1 (hvq hzv))
      · have hz : z ∈ ({l, r} : Set ℂ) :=
          square_chains_image_inter R a.im b.im hR (abs_lt.mp haim) (abs_lt.mp hbim) ▸
            ⟨hzu, hzv⟩
        rcases hz with rfl | rfl
        · exact Or.inl (right_mem_segment ℝ _ _)
        · exact Or.inr (right_mem_segment ℝ _ _)
    · rintro z (hzs | hzt)
      · exact ⟨Or.inr (Or.inl (Or.inl hzs)), Or.inr (Or.inl (Or.inl hzs))⟩
      · exact ⟨Or.inr (Or.inr hzt), Or.inr (Or.inr hzt)⟩
  · intro z hz
    rw [enclosingSquare_closure_inside R hR]
    exact hcontain hz
  all_goals
    apply inside_subset_inside_of_image_subset_closure (enclosingSquare R)
      (enclosingSquare_isCyclicSimple R hR)
  · exact hclosed p hp
  · rw [hpim]
    rintro z (hzx | (hzs | hzv) | hzt)
    · exact subset_closure (hnest (c.image_subset_closure_inside_cyclic hc (hxsub hzx)))
    · rw [enclosingSquare_closure_inside R hR]
      exact (hcontain (Or.inl ((diagonalArc_data a l).2.2.2.symm ▸ hzs))).2
    · exact (enclosingSquare R).image_subset_closure_inside_cyclic
        (enclosingSquare_isCyclicSimple R hR) (hvq hzv)
    · rw [enclosingSquare_closure_inside R hR]
      exact (hcontain (Or.inr ((diagonalArc_data b r).2.2.2.symm ▸ hzt))).2
  · exact hclosed q hq
  · rw [hqim]
    rintro z (hzy | (hzs | hzu) | hzt)
    · exact subset_closure (hnest (c.image_subset_closure_inside_cyclic hc (hysub hzy)))
    · rw [enclosingSquare_closure_inside R hR]
      exact (hcontain (Or.inl ((diagonalArc_data a l).2.2.2.symm ▸ hzs))).2
    · exact (enclosingSquare R).image_subset_closure_inside_cyclic
        (enclosingSquare_isCyclicSimple R hR) (huq hzu)
    · rw [enclosingSquare_closure_inside R hR]
      exact (hcontain (Or.inr ((diagonalArc_data b r).2.2.2.symm ▸ hzt))).2

/-- Helper toward Proposition 5.16: counterclockwise inner boundaries admit
the exact closed annulus partition, with signed winding subtraction. -/
theorem exists_closed_annulus_partition_counterclockwise (c : Polyline)
    (hc : c.IsCyclicSimple) (hccw : ∀ z ∈ c.inside, c.angleSum z = 1) :
    ∃ (R : ℝ) (s t p q : Polyline), 0 < R ∧
      (enclosingSquare R).IsCyclicSimple ∧ closure c.inside ⊆ (enclosingSquare R).inside ∧
      s.IsSimple ∧ t.IsSimple ∧ Disjoint s.image t.image ∧
      s.image ∩ c.image = {s.start} ∧ t.image ∩ c.image = {t.start} ∧
      s.image ∩ (enclosingSquare R).image = {s.finish} ∧
      t.image ∩ (enclosingSquare R).image = {t.finish} ∧
      p.IsCyclicSimple ∧ q.IsCyclicSimple ∧
      closure p.inside ∪ closure q.inside = closure c.outside ∩ closure (enclosingSquare R).inside ∧
      closure p.inside ∩ closure q.inside = s.image ∪ t.image ∧
      p.image ∪ q.image = (c.image ∪ (enclosingSquare R).image) ∪ (s.image ∪ t.image) ∧
      ∀ z : ℂ, z ∉ (c.image ∪ (enclosingSquare R).image) ∪ (p.image ∪ q.image) →
        p.angleSum z + q.angleSum z = (enclosingSquare R).angleSum z - c.angleSum z := by
  obtain ⟨R, s, t, p, q, hR, hnest, hs, ht, hst, hsc, htc, hsS, htS, hp, hq,
    hsum, hpone, hqone, himunion, himinter, hslits, hpS, hqS⟩ :=
    c.exists_cyclic_annulus_loops_winding hc
  have hcclosed : c.start = c.finish := by
    rw [← point_zero_eq_start, ← point_last_eq_finish]; exact hc.2.1
  have hpclosed : p.start = p.finish := by
    rw [← point_zero_eq_start, ← point_last_eq_finish]; exact hp.2.1
  have hqclosed : q.start = q.finish := by
    rw [← point_zero_eq_start, ← point_last_eq_finish]; exact hq.2.1
  have hS := enclosingSquare_isCyclicSimple R hR
  have hKp : s.image ∪ t.image ⊆ p.image := fun _ h => (himinter.symm ▸ h).1
  have hKq : s.image ∪ t.image ⊆ q.image := fun _ h => (himinter.symm ▸ h).2
  have hci : c.inside ⊆ p.outside ∩ q.outside := by
    intro z hz
    have hzS := hnest (subset_closure hz)
    have hzK : z ∉ s.image ∪ t.image := fun h =>
      (c.closure_sides_avoid hcclosed).2 (hslits h).1 hz
    have hoff : z ∉ p.image ∪ q.image := by
      rw [himunion]
      exact fun h => h.elim (fun h => h.elim hz.1 hzS.1) hzK
    have hs' := hsum z (fun h => h.elim (fun h => h.elim hz.1 hzS.1) hoff)
    rw [enclosingSquare_angleSum_of_mem_inside R hR z hzS, hccw z hz] at hs'
    have hpv := (p.angleSum_zero_or_one_of_counterclockwise hpone z (fun h => hoff (Or.inl h))).1
    have hqv := (q.angleSum_zero_or_one_of_counterclockwise hqone z (fun h => hoff (Or.inr h))).1
    have hpzero : p.angleSum z = 0 := by rcases hpv with h | h <;> rcases hqv with h' | h' <;> linarith only [hs', h, h']
    have hqzero : q.angleSum z = 0 := by linarith only [hs', hpzero]
    exact ⟨⟨fun h => hoff (Or.inl h), hpzero⟩, ⟨fun h => hoff (Or.inr h), hqzero⟩⟩
  have hpc : p.inside ⊆ c.outside := by
    have havoid : closure c.inside ⊆ p.insideᶜ :=
      (closure_mono (fun _ h => (hci h).1)).trans (p.closure_sides_avoid hpclosed).2
    intro z hz
    have hzoff : z ∉ c.image := fun h => havoid (c.image_subset_closure_inside_cyclic hc h) hz
    exact ⟨hzoff, by
      by_contra h
      exact havoid (subset_closure (show z ∈ c.inside from ⟨hzoff, h⟩)) hz⟩
  have hqc : q.inside ⊆ c.outside := by
    have havoid : closure c.inside ⊆ q.insideᶜ :=
      (closure_mono (fun _ h => (hci h).2)).trans (q.closure_sides_avoid hqclosed).2
    intro z hz
    have hzoff : z ∉ c.image := fun h => havoid (c.image_subset_closure_inside_cyclic hc h) hz
    exact ⟨hzoff, by
      by_contra h
      exact havoid (subset_closure (show z ∈ c.inside from ⟨hzoff, h⟩)) hz⟩
  have hpavoidq {z : ℂ} (hz : z ∈ p.inside) : z ∉ q.image := by
    intro h
    have him : z ∈ p.image ∪ q.image := Or.inr h
    rw [himunion] at him
    rcases him with (hc | hS) | hK
    · exact (hpc hz).1 hc
    · exact (hpS hz).1 hS
    · exact hz.1 (hKp hK)
  have hqavoidp {z : ℂ} (hz : z ∈ q.inside) : z ∉ p.image := by
    intro h
    have him : z ∈ p.image ∪ q.image := Or.inl h
    rw [himunion] at him
    rcases him with (hc | hS) | hK
    · exact (hqc hz).1 hc
    · exact (hqS hz).1 hS
    · exact hz.1 (hKq hK)
  have hdisj : Disjoint p.inside q.inside := by
    apply Set.disjoint_left.mpr
    intro z hzp hzq
    have hoff : z ∉ (c.image ∪ (enclosingSquare R).image) ∪ (p.image ∪ q.image) :=
      fun h => h.elim (fun h => h.elim (hpc hzp).1 (hpS hzp).1)
        (fun h => h.elim hzp.1 hzq.1)
    have h := hsum z hoff
    rw [hpone z hzp, hqone z hzq, enclosingSquare_angleSum_of_mem_inside R hR z (hpS hzp),
      (hpc hzp).2] at h
    norm_num at h
  have hcover : closure p.inside ∪ closure q.inside =
      closure c.outside ∩ closure (enclosingSquare R).inside := by
    apply Set.Subset.antisymm
    · rintro z (hz | hz)
      · exact ⟨closure_mono hpc hz, closure_mono hpS hz⟩
      · exact ⟨closure_mono hqc hz, closure_mono hqS hz⟩
    · intro z hz
      by_cases him : z ∈ p.image ∪ q.image
      · exact him.elim (fun h => Or.inl (p.image_subset_closure_inside_cyclic hp h))
          (fun h => Or.inr (q.image_subset_closure_inside_cyclic hq h))
      have hzoffc : z ∉ c.image := fun h => him (himunion.symm ▸ Or.inl (Or.inl h))
      have hzoffS : z ∉ (enclosingSquare R).image := fun h => him (himunion.symm ▸ Or.inl (Or.inr h))
      have hzc : z ∈ c.outside := by
        have hnot := (c.closure_sides_avoid hcclosed).2 hz.1
        exact ⟨hzoffc, by by_contra h; exact hnot ⟨hzoffc, h⟩⟩
      have hzS : z ∈ (enclosingSquare R).inside := by
        rw [closure_inside_eq_union_image _ hS] at hz
        exact hz.2.resolve_right hzoffS
      have h := hsum z (fun h => h.elim (fun h => h.elim hzoffc hzoffS) him)
      rw [enclosingSquare_angleSum_of_mem_inside R hR z hzS, hzc.2] at h
      by_cases hpzero : p.angleSum z = 0
      · right
        apply subset_closure
        exact ⟨fun h => him (Or.inr h), by intro hqzero; rw [hpzero, hqzero] at h; norm_num at h⟩
      · exact Or.inl (subset_closure ⟨fun h => him (Or.inl h), hpzero⟩)
  have hinter : closure p.inside ∩ closure q.inside = s.image ∪ t.image := by
    rw [closure_inside_eq_union_image _ hp, closure_inside_eq_union_image _ hq]
    apply Set.Subset.antisymm
    · rintro z ⟨hz | hz, hw | hw⟩
      · exact False.elim (Set.disjoint_left.mp hdisj hz hw)
      · exact False.elim (hpavoidq hz hw)
      · exact False.elim (hqavoidp hw hz)
      · exact himinter ▸ ⟨hz, hw⟩
    · exact fun z hz => ⟨Or.inr (hKp hz), Or.inr (hKq hz)⟩
  exact ⟨R, s, t, p, q, hR, hS, hnest, hs, ht, hst, hsc, htc, hsS, htS,
    hp, hq, hcover, hinter, himunion, hsum⟩

/-- Helper toward Proposition 5.16: the closed annulus partition is independent
of the orientation of its inner cyclic polygon. -/
theorem exists_closed_annulus_partition (c : Polyline) (hc : c.IsCyclicSimple) :
    ∃ (R : ℝ) (s t p q : Polyline), 0 < R ∧
      (enclosingSquare R).IsCyclicSimple ∧ closure c.inside ⊆ (enclosingSquare R).inside ∧
      s.IsSimple ∧ t.IsSimple ∧ Disjoint s.image t.image ∧
      s.image ∩ c.image = {s.start} ∧ t.image ∩ c.image = {t.start} ∧
      s.image ∩ (enclosingSquare R).image = {s.finish} ∧
      t.image ∩ (enclosingSquare R).image = {t.finish} ∧
      p.IsCyclicSimple ∧ q.IsCyclicSimple ∧
      closure p.inside ∪ closure q.inside = closure c.outside ∩ closure (enclosingSquare R).inside ∧
      closure p.inside ∩ closure q.inside = s.image ∪ t.image ∧
      p.image ∪ q.image = (c.image ∪ (enclosingSquare R).image) ∪ (s.image ∪ t.image) := by
  obtain ⟨d, _, hd, hdimage, hdinside, hdoutside, hdccw⟩ :=
    c.exists_counterclockwise_reorientation hc
  obtain ⟨R, s, t, p, q, hR, hS, hnest, hs, ht, hst, hsc, htc, hsS, htS,
    hp, hq, hcover, hinter, himunion, _⟩ :=
    d.exists_closed_annulus_partition_counterclockwise hd hdccw
  rw [hdinside] at hnest
  rw [hdimage] at hsc htc himunion
  rw [hdoutside] at hcover
  exact ⟨R, s, t, p, q, hR, hS, hnest, hs, ht, hst, hsc, htc, hsS, htS,
    hp, hq, hcover, hinter, himunion⟩

end Polyline
end DirectedDistances.PlanarMap
