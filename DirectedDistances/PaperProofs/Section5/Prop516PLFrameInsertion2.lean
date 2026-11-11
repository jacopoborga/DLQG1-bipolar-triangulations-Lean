/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516PLFrameInsertion

/-! Helpers toward Proposition 5.16: a reflex quadrilateral at a square contact. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set Topology
namespace Polyline

/-- Helper toward Proposition 5.16: a four-segment reflex frame whose root
is the point `(R,t)` on the right side of the coordinate square. -/
@[expose] def rightCornerFrame (R t : ℝ) : Polyline :=
  ofHead (⟨R, t⟩ : ℂ)
    [⟨5 * R, t + 4 * R⟩, ⟨-11 * R, t⟩, ⟨5 * R, t - 4 * R⟩, ⟨R, t⟩]

/-- Helper toward Proposition 5.16: affine equations and horizontal bounds
on each of the four sides of the reflex frame. -/
theorem rightCornerFrame_segment_constraints (R t : ℝ) (hR : 0 < R) (z : ℂ) :
    (z ∈ (rightCornerFrame R t).segmentAt 0 →
      R ≤ z.re ∧ z.re ≤ 5 * R ∧ z.im - t = z.re - R) ∧
    (z ∈ (rightCornerFrame R t).segmentAt 1 →
      -11 * R ≤ z.re ∧ z.re ≤ 5 * R ∧ 4 * (z.im - t) = z.re + 11 * R) ∧
    (z ∈ (rightCornerFrame R t).segmentAt 2 →
      -11 * R ≤ z.re ∧ z.re ≤ 5 * R ∧ 4 * (z.im - t) = -(z.re + 11 * R)) ∧
    (z ∈ (rightCornerFrame R t).segmentAt 3 →
      R ≤ z.re ∧ z.re ≤ 5 * R ∧ z.im - t = -(z.re - R)) := by
  have hseg (a b : ℂ) (l u k m : ℝ)
      (ha : l ≤ a.re ∧ a.re ≤ u ∧ k * a.im = a.re + m)
      (hb : l ≤ b.re ∧ b.re ≤ u ∧ k * b.im = b.re + m)
      (hz : z ∈ segment ℝ a b) :
      l ≤ z.re ∧ z.re ≤ u ∧ k * z.im = z.re + m := by
    obtain ⟨s, v, hs, hv, hsv, rfl⟩ := hz
    simp only [Complex.add_re, Complex.add_im, Complex.smul_re,
      Complex.smul_im, smul_eq_mul]
    refine ⟨?_, ?_, ?_⟩
    · calc
        l = s * l + v * l := by rw [← add_mul, hsv, one_mul]
        _ ≤ s * a.re + v * b.re := add_le_add
          (mul_le_mul_of_nonneg_left ha.1 hs) (mul_le_mul_of_nonneg_left hb.1 hv)
    · calc
        s * a.re + v * b.re ≤ s * u + v * u := add_le_add
          (mul_le_mul_of_nonneg_left ha.2.1 hs) (mul_le_mul_of_nonneg_left hb.2.1 hv)
        _ = u := by rw [← add_mul, hsv, one_mul]
    · calc
        k * (s * a.im + v * b.im) = s * (k * a.im) + v * (k * b.im) := by ring
        _ = s * (a.re + m) + v * (b.re + m) := by rw [ha.2.2, hb.2.2]
        _ = s * a.re + v * b.re + m := by
          calc
            _ = s * a.re + v * b.re + (s + v) * m := by ring
            _ = _ := by rw [hsv, one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hz
    have h := hseg ⟨R, t⟩ ⟨5 * R, t + 4 * R⟩ R (5 * R) 1 (t - R)
      (by dsimp; constructor; rfl; constructor <;> linarith)
      (by dsimp; constructor; linarith; constructor; rfl; ring) hz
    exact ⟨h.1, h.2.1, by linarith only [h.2.2]⟩
  · intro hz
    have h := hseg ⟨5 * R, t + 4 * R⟩ ⟨-11 * R, t⟩ (-11 * R) (5 * R) 4
      (4 * t + 11 * R)
      (by dsimp; constructor; linarith; constructor; rfl; ring)
      (by dsimp; constructor; rfl; constructor; linarith; ring) hz
    exact ⟨h.1, h.2.1, by linarith only [h.2.2]⟩
  · intro hz
    have h := hseg ⟨-11 * R, t⟩ ⟨5 * R, t - 4 * R⟩ (-11 * R) (5 * R) (-4)
      (-4 * t + 11 * R)
      (by dsimp; constructor; rfl; constructor; linarith; ring)
      (by dsimp; constructor; linarith; constructor; rfl; ring) hz
    exact ⟨h.1, h.2.1, by linarith only [h.2.2]⟩
  · intro hz
    have h := hseg ⟨5 * R, t - 4 * R⟩ ⟨R, t⟩ R (5 * R) (-1) (-t - R)
      (by dsimp; constructor; linarith; constructor; rfl; ring)
      (by dsimp; constructor; rfl; constructor <;> linarith) hz
    exact ⟨h.1, h.2.1, by linarith only [h.2.2]⟩

/-- Helper toward Proposition 5.16: the reflex frame is cyclically simple,
including its root, its two opposite side pairs, and all four junctions. -/
theorem rightCornerFrame_isCyclicSimple (R t : ℝ) (hR : 0 < R) :
    (rightCornerFrame R t).IsCyclicSimple := by
  have hc := rightCornerFrame_segment_constraints R t hR
  refine ⟨by change 4 ≤ 5; omega, rfl, ?_, ?_, ?_, ?_⟩
  · intro i hi
    change i + 1 < 5 at hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
    all_goals
      intro heq
      have hre := congrArg Complex.re heq
      norm_num [rightCornerFrame, ofHead, point, start] at hre
      linarith only [hR, hre]
  · intro i hi
    change i + 2 < 5 at hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · apply Set.Subset.antisymm
      · intro z hz
        have h0 := (hc z).1 hz.1
        have h1 := (hc z).2.1 hz.2
        change z = (⟨5 * R, t + 4 * R⟩ : ℂ)
        apply Complex.ext <;> dsimp <;> linarith only [h0.2.2, h1.2.2]
      · rintro z rfl
        exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
    · apply Set.Subset.antisymm
      · intro z hz
        have h1 := (hc z).2.1 hz.1
        have h2 := (hc z).2.2.1 hz.2
        change z = (⟨-11 * R, t⟩ : ℂ)
        apply Complex.ext <;> dsimp <;> linarith only [h1.2.2, h2.2.2]
      · rintro z rfl
        exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
    · apply Set.Subset.antisymm
      · intro z hz
        have h2 := (hc z).2.2.1 hz.1
        have h3 := (hc z).2.2.2 hz.2
        change z = (⟨5 * R, t - 4 * R⟩ : ℂ)
        apply Complex.ext <;> dsimp <;> linarith only [h2.2.2, h3.2.2]
      · rintro z rfl
        exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
  · intro i j hi hj hij hwrap
    change i + 1 < 5 at hi
    change j + 1 < 5 at hj
    have hpairs : (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 3) := by
      change ¬ (i = 0 ∧ j + 2 = 5) at hwrap
      omega
    rcases hpairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · apply Set.disjoint_left.mpr
      intro z hz hw
      have h0 := (hc z).1 hz
      have h2 := (hc z).2.2.1 hw
      linarith only [h0.1, h0.2.2, h2.2.2, hR]
    · apply Set.disjoint_left.mpr
      intro z hz hw
      have h1 := (hc z).2.1 hz
      have h3 := (hc z).2.2.2 hw
      linarith only [h3.1, h1.2.2, h3.2.2, hR]
  · apply Set.Subset.antisymm
    · intro z hz
      have h0 := (hc z).1 hz.1
      have h3 := (hc z).2.2.2 hz.2
      change z = (⟨R, t⟩ : ℂ)
      apply Complex.ext <;> dsimp <;> linarith only [h0.2.2, h3.2.2]
    · rintro z rfl
      exact ⟨left_mem_segment ℝ _ _, right_mem_segment ℝ _ _⟩

/-- Helper toward Proposition 5.16: for right-side contact, the entire
four-edge frame meets the closed square only at the prescribed root. -/
theorem rightCornerFrame_inter_closedSquare (R t : ℝ) (hR : 0 < R)
    (ht : -R ≤ t ∧ t ≤ R) :
    (rightCornerFrame R t).image ∩ {z : ℂ | |z.re| ≤ R ∧ |z.im| ≤ R} =
      {(⟨R, t⟩ : ℂ)} := by
  apply Set.Subset.antisymm
  · intro z hz
    have hre := abs_le.mp hz.2.1
    have him := abs_le.mp hz.2.2
    rcases hz.1 with hz | ⟨i, hi, hz⟩
    · exact hz
    · change i + 1 < 5 at hi
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
      · have h := (rightCornerFrame_segment_constraints R t hR z).1 hz
        change z = (⟨R, t⟩ : ℂ)
        apply Complex.ext <;> dsimp <;> linarith only [h.1, h.2.2, hre.2]
      · have h := (rightCornerFrame_segment_constraints R t hR z).2.1 hz
        exfalso
        linarith only [h.2.2, hre.1, him.2, ht.1, hR]
      · have h := (rightCornerFrame_segment_constraints R t hR z).2.2.1 hz
        exfalso
        linarith only [h.2.2, hre.1, him.1, ht.2, hR]
      · have h := (rightCornerFrame_segment_constraints R t hR z).2.2.2 hz
        change z = (⟨R, t⟩ : ℂ)
        apply Complex.ext <;> dsimp <;> linarith only [h.1, h.2.2, hre.2]
  · rintro z rfl
    refine ⟨Or.inl rfl, ?_⟩
    change |R| ≤ R ∧ |t| ≤ R
    exact ⟨(abs_of_pos hR).le, abs_le.mpr ht⟩

/-- Helper toward Proposition 5.16: the open coordinate square belongs to
the bounded winding side of the right-contact reflex frame. -/
theorem openSquare_subset_rightCornerFrame_inside (R t : ℝ) (hR : 0 < R)
    (ht : -R ≤ t ∧ t ≤ R) :
    (enclosingSquare R).inside ⊆ (rightCornerFrame R t).inside := by
  let p := rightCornerFrame R t
  let w : ℂ := ⟨-R / 2, 0⟩
  have hw : w ∈ (enclosingSquare R).inside := by
    rw [enclosingSquare_inside R hR]
    change (-R < -R / 2 ∧ -R / 2 < R) ∧ (-R < 0 ∧ 0 < R)
    constructor <;> constructor <;> linarith only [hR]
  have havoid : (enclosingSquare R).inside ⊆ p.imageᶜ := by
    intro z hz hzp
    have hzS : |z.re| ≤ R ∧ |z.im| ≤ R := by
      rw [enclosingSquare_inside R hR] at hz
      exact ⟨abs_le.mpr ⟨hz.1.1.le, hz.1.2.le⟩,
        abs_le.mpr ⟨hz.2.1.le, hz.2.2.le⟩⟩
    have heq : z = (⟨R, t⟩ : ℂ) :=
      (rightCornerFrame_inter_closedSquare R t hR ht).subset ⟨hzp, hzS⟩
    rw [enclosingSquare_inside R hR, heq] at hz
    exact (lt_irrefl R) hz.1.2
  have hlow : 0 ≤ R * (t + R) := mul_nonneg hR.le (by linarith only [ht.1])
  have hhigh : 0 ≤ R * (R - t) := mul_nonneg hR.le (by linarith only [ht.2])
  have hangle (i : ℕ) (hi : i < 4) : 0 < p.edgeAngle w i := by
    apply (d39_arg_div_mem_Ioo_of_leftOf (p.point i) (p.point (i + 1)) w ?_).1
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
    all_goals
      norm_num [p, w, rightCornerFrame, ofHead, point, start,
        Complex.mul_im, Complex.conj_re, Complex.conj_im]
      nlinarith only [sq_pos_of_pos hR, hlow, hhigh]
  have hpos : 0 < p.angleSum w := by
    have h0 := hangle 0 (by omega)
    have h1 := hangle 1 (by omega)
    have h2 := hangle 2 (by omega)
    have h3 := hangle 3 (by omega)
    unfold angleSum
    change 0 < (∑ i ∈ Finset.range 4, p.edgeAngle w i) / (2 * Real.pi)
    apply div_pos _ (mul_pos (by norm_num) Real.pi_pos)
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] using
      add_pos (add_pos (add_pos h0 h1) h2) h3
  have hconv : Convex ℝ (enclosingSquare R).inside := by
    rw [enclosingSquare_inside R hR]
    exact ((convex_halfSpace_re_gt (-R)).inter (convex_halfSpace_re_lt R)).inter
      ((convex_halfSpace_im_gt (-R)).inter (convex_halfSpace_im_lt R))
  intro z hz
  refine ⟨havoid hz, ?_⟩
  rw [p.angleSum_eq_of_isPreconnected (by rfl) _ hconv.isPreconnected havoid z w hz hw]
  exact ne_of_gt hpos

/-- Helper toward Proposition 5.16: the right-contact reflex quadrilateral
encloses the entire closed square, with boundary contact only at its root. -/
theorem closedSquare_subset_rightCornerFrame_closure_inside
    (R t : ℝ) (hR : 0 < R) (ht : -R ≤ t ∧ t ≤ R) :
    {z : ℂ | |z.re| ≤ R ∧ |z.im| ≤ R} ⊆ closure (rightCornerFrame R t).inside := by
  rw [← enclosingSquare_closure_inside R hR]
  exact closure_mono (openSquare_subset_rightCornerFrame_inside R t hR ht)

/-- Helper toward Proposition 5.16: an injective affine change of plane
coordinates preserves the exact cyclic segment-intersection predicate. -/
theorem isCyclicSimple_mapPoints_of_affine (p : Polyline) (F : ℂ → ℂ)
    (hF : AffineOnSegments F p) (hinj : Function.Injective F)
    (hp : p.IsCyclicSimple) : (mapPoints F p).IsCyclicSimple := by
  have hinter (i j : ℕ) (hi : i + 1 < p.points.length)
      (hj : j + 1 < p.points.length) :
      (mapPoints F p).segmentAt i ∩ (mapPoints F p).segmentAt j =
        F '' (p.segmentAt i ∩ p.segmentAt j) := by
    rw [segmentAt_mapPoints F p hF hi, segmentAt_mapPoints F p hF hj,
      Set.image_inter hinj]
  refine ⟨by simpa only [length_mapPoints] using hp.1, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [length_mapPoints, point_mapPoints] using congrArg F hp.2.1
  · intro i hi heq
    rw [length_mapPoints] at hi
    simp only [point_mapPoints] at heq
    exact hp.2.2.1 i hi (hinj heq)
  · intro i hi
    rw [length_mapPoints] at hi
    rw [hinter i (i + 1) (by omega) (by omega), hp.2.2.2.1 i hi,
      Set.image_singleton, point_mapPoints]
  · intro i j hi hj hij hwrap
    rw [length_mapPoints] at hi hj hwrap
    apply Set.disjoint_iff_inter_eq_empty.mpr
    rw [hinter i j hi hj, Set.disjoint_iff_inter_eq_empty.mp
      (hp.2.2.2.2.1 i j hi hj hij hwrap), Set.image_empty]
  · rw [length_mapPoints, hinter 0 (p.points.length - 2) (by have := hp.1; omega)
      (by have := hp.1; omega), hp.2.2.2.2.2, Set.image_singleton, point_mapPoints]

/-- Helper toward Proposition 5.16: complex multiplication is affine on
every segment of every polyline. -/
theorem affineOnSegments_mul (p : Polyline) (u : ℂ) :
    AffineOnSegments (fun z => u * z) p := by
  intro i hi
  exact ⟨(LinearMap.mulLeft ℝ u).toAffineMap, fun _ _ => rfl⟩

/-- Helper toward Proposition 5.16: a nonzero complex scaling preserves
the normalized angle sum, at the correspondingly scaled viewpoint. -/
theorem angleSum_mapPoints_mul (p : Polyline) (u : ℂ) (hu : u ≠ 0) (z : ℂ) :
    (mapPoints (fun w => u * w) p).angleSum (u * z) = p.angleSum z := by
  unfold angleSum
  rw [length_mapPoints]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [edgeAngle, point_mapPoints, ← mul_sub, mul_div_mul_left _ _ hu]

/-- Helper toward Proposition 5.16: nonzero complex scaling transports
the winding-defined inside pointwise. -/
theorem mem_inside_mapPoints_mul_iff (p : Polyline) (u : ℂ) (hu : u ≠ 0) (z : ℂ) :
    u * z ∈ (mapPoints (fun w => u * w) p).inside ↔ z ∈ p.inside := by
  change (_ ∉ _ ∧ _ ≠ 0) ↔ (_ ∉ _ ∧ _ ≠ 0)
  rw [image_mapPoints _ _ (affineOnSegments_mul p u), angleSum_mapPoints_mul p u hu z]
  have hmem : u * z ∈ (fun w => u * w) '' p.image ↔ z ∈ p.image := by
    constructor
    · rintro ⟨w, hw, heq⟩
      exact (mul_right_injective₀ hu heq) ▸ hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  rw [hmem]

/-- Helper toward Proposition 5.16: rotating the right-side construction
by a symmetry of the coordinate square gives the full corner-frame data. -/
theorem cornerFrame_of_square_symmetry (R t : ℝ) (hR : 0 < R)
    (ht : -R ≤ t ∧ t ≤ R) (u : ℂ) (hu : u ≠ 0)
    (hsym : ∀ z : ℂ, max |(u * z).re| |(u * z).im| = max |z.re| |z.im|) :
    let p := mapPoints (fun z => u * z) (rightCornerFrame R t)
    p.IsCyclicSimple ∧
      closure (enclosingSquare R).inside ⊆ closure p.inside ∧
      p.image ∩ closure (enclosingSquare R).inside = {u * (⟨R, t⟩ : ℂ)} := by
  dsimp only
  let p := rightCornerFrame R t
  let q := mapPoints (fun z => u * z) p
  have hinj : Function.Injective (fun z : ℂ => u * z) := mul_right_injective₀ hu
  have hclosed (z : ℂ) :
      u * z ∈ closure (enclosingSquare R).inside ↔ z ∈ closure (enclosingSquare R).inside := by
    rw [enclosingSquare_closure_inside R hR]
    change (|(u * z).re| ≤ R ∧ |(u * z).im| ≤ R) ↔ (|z.re| ≤ R ∧ |z.im| ≤ R)
    rw [← max_le_iff, ← max_le_iff, hsym]
  have hopen (z : ℂ) :
      u * z ∈ (enclosingSquare R).inside ↔ z ∈ (enclosingSquare R).inside := by
    rw [enclosingSquare_inside R hR]
    change ((-R < (u * z).re ∧ (u * z).re < R) ∧
      (-R < (u * z).im ∧ (u * z).im < R)) ↔
      ((-R < z.re ∧ z.re < R) ∧ (-R < z.im ∧ z.im < R))
    rw [← abs_lt, ← abs_lt, ← abs_lt, ← abs_lt, ← max_lt_iff, ← max_lt_iff, hsym]
  refine ⟨isCyclicSimple_mapPoints_of_affine p _ (affineOnSegments_mul p u) hinj
    (rightCornerFrame_isCyclicSimple R t hR), ?_, ?_⟩
  · apply closure_mono
    intro z hz
    have heq : u * (u⁻¹ * z) = z := by rw [← mul_assoc, mul_inv_cancel₀ hu, one_mul]
    rw [← heq, mem_inside_mapPoints_mul_iff p u hu]
    exact openSquare_subset_rightCornerFrame_inside R t hR ht ((hopen _).mp (heq.symm ▸ hz))
  · apply Set.Subset.antisymm
    · rintro z ⟨hz, hzS⟩
      rw [image_mapPoints _ _ (affineOnSegments_mul p u)] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      have hwS := (hclosed w).mp hzS
      rw [enclosingSquare_closure_inside R hR] at hwS
      have heq : w = (⟨R, t⟩ : ℂ) :=
        (rightCornerFrame_inter_closedSquare R t hR ht).subset ⟨hw, hwS⟩
      exact congrArg (fun z => u * z) heq
    · rintro z rfl
      refine ⟨?_, (hclosed _).mpr ?_⟩
      · rw [image_mapPoints _ _ (affineOnSegments_mul p u)]
        exact ⟨_, Or.inl rfl, rfl⟩
      · rw [enclosingSquare_closure_inside R hR]
        exact ⟨(abs_of_pos hR).le, abs_le.mpr ht⟩

/-- Helper toward Proposition 5.16: every square-boundary point is the
image of a right-side point under a complex rotation preserving the square. -/
theorem exists_square_symmetry_of_mem_boundary (R : ℝ) (hR : 0 < R)
    (c : ℂ) (hc : c ∈ (enclosingSquare R).image) :
    ∃ (u : ℂ) (t : ℝ), u ≠ 0 ∧ (-R ≤ t ∧ t ≤ R) ∧
      (∀ z : ℂ, max |(u * z).re| |(u * z).im| = max |z.re| |z.im|) ∧
      c = u * (⟨R, t⟩ : ℂ) := by
  obtain ⟨hr, hi, hside⟩ := (mem_enclosingSquare_image_iff R hR c).mp hc
  rcases hside with h | h | h | h
  · refine ⟨-1, -c.im, by norm_num, ⟨by linarith only [hi.2], by linarith only [hi.1]⟩,
      ?_, ?_⟩
    · intro z
      simp only [neg_one_mul, Complex.neg_re, Complex.neg_im, abs_neg]
    · apply Complex.ext <;> simp [h]
  · refine ⟨1, c.im, one_ne_zero, hi, ?_, ?_⟩
    · intro z
      rw [one_mul]
    · apply Complex.ext <;> simp [h]
  · refine ⟨-Complex.I, c.re, by simp, hr, ?_, ?_⟩
    · intro z
      simp [Complex.mul_re, Complex.mul_im, abs_neg, max_comm]
    · apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, h]
  · refine ⟨Complex.I, -c.re, Complex.I_ne_zero,
      ⟨by linarith only [hr.2], by linarith only [hr.1]⟩, ?_, ?_⟩
    · intro z
      simp [Complex.mul_re, Complex.mul_im, abs_neg, max_comm]
    · apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, h]

/-- Helper toward Proposition 5.16: every point of the enclosing-square
boundary is a corner of a simple four-segment polygon enclosing the closed
square and touching it only at that corner. The three new vertices are
actual complex points; no simple-exterior premise is used. -/
theorem exists_corner_quadrilateral (R : ℝ) (hR : 0 < R) (c : ℂ)
    (hc : c ∈ (enclosingSquare R).image) :
    ∃ A B C : ℂ,
      let p := ofHead c [A, B, C, c]
      p.IsCyclicSimple ∧
        closure (enclosingSquare R).inside ⊆ closure p.inside ∧
        p.image ∩ closure (enclosingSquare R).inside = {c} := by
  obtain ⟨u, t, hu, ht, hsym, rfl⟩ := exists_square_symmetry_of_mem_boundary R hR c hc
  refine ⟨u * (⟨5 * R, t + 4 * R⟩ : ℂ), u * (⟨-11 * R, t⟩ : ℂ),
    u * (⟨5 * R, t - 4 * R⟩ : ℂ), ?_⟩
  exact cornerFrame_of_square_symmetry R t hR ht u hu hsym

/-- Helper toward Proposition 5.16: square-boundary membership is the
level condition for the maximum of the absolute coordinate values. -/
theorem mem_enclosingSquare_image_iff_max (R : ℝ) (hR : 0 < R) (z : ℂ) :
    z ∈ (enclosingSquare R).image ↔ max |z.re| |z.im| = R := by
  rw [mem_enclosingSquare_image_iff R hR]
  constructor
  · rintro ⟨hr, hi, hside⟩
    have hra := abs_le.mpr hr
    have hia := abs_le.mpr hi
    rcases hside with h | h | h | h
    · simp only [h, abs_neg, abs_of_pos hR, max_eq_left hia]
    · simp only [h, abs_of_pos hR, max_eq_left hia]
    · simp only [h, abs_neg, abs_of_pos hR, max_eq_right hra]
    · simp only [h, abs_of_pos hR, max_eq_right hra]
  · intro hz
    have hr : |z.re| ≤ R := (le_max_left _ _).trans_eq hz
    have hi : |z.im| ≤ R := (le_max_right _ _).trans_eq hz
    refine ⟨abs_le.mp hr, abs_le.mp hi, ?_⟩
    rcases max_eq_iff.mp hz with h | h
    · rcases (abs_eq hR.le).mp h.1 with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
    · rcases (abs_eq hR.le).mp h.1 with h | h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))

/-- Helper toward Proposition 5.16: a simple access arc starting inside
the square and meeting its boundary only at its finish stays in the closed
square. In particular, first contact cannot leave and reenter the square. -/
theorem image_subset_closedSquare_of_unique_boundary_contact (p : Polyline)
    (hlen : 2 ≤ p.points.length) (hp : p.IsSimple) (R : ℝ) (hR : 0 < R)
    (hs : max |p.start.re| |p.start.im| < R)
    (hcontact : p.image ∩ (enclosingSquare R).image = {p.finish}) :
    p.image ⊆ closure (enclosingSquare R).inside := by
  let f : ℂ → ℝ := fun z => max |z.re| |z.im|
  have hcont : Continuous (fun s : unitInterval => f (p.toPath s)) :=
    ((continuous_abs.comp Complex.continuous_re).max
      (continuous_abs.comp Complex.continuous_im)).comp p.toPath.continuous
  have hfinish : f p.finish = R :=
    (mem_enclosingSquare_image_iff_max R hR _).mp (hcontact.symm.subset (mem_singleton _)).2
  intro z hz
  rw [enclosingSquare_closure_inside R hR]
  suffices max |z.re| |z.im| ≤ R by exact max_le_iff.mp this
  by_contra hn
  have hlt : R < f z := lt_of_not_ge hn
  rw [← range_toPath] at hz
  obtain ⟨s, rfl⟩ := hz
  obtain ⟨r, hrs, hr⟩ := intermediate_value_Icc
    (show (0 : unitInterval) ≤ s from s.property.1) hcont.continuousOn
    (show f (p.toPath 0) ≤ R ∧ R ≤ f (p.toPath s) by
      exact ⟨by simpa only [Path.source] using hs.le, hlt.le⟩)
  have hreq : p.toPath r = p.finish := hcontact.subset
    ⟨by rw [← range_toPath]; exact mem_range_self r,
      (mem_enclosingSquare_image_iff_max R hR _).mpr hr⟩
  have hr1 : r = 1 := p.toPath_injective hlen hp
    (by simpa only [Path.target] using hreq)
  have hs1 : s = 1 := le_antisymm s.property.2 (hr1 ▸ hrs.2)
  rw [hs1, Path.target, hfinish] at hlt
  exact (lt_irrefl R) hlt

/-- Helper toward Proposition 5.16: two nondegenerate simple arcs with
the same start and no other common point have different initial ray
arguments. This supplies the angular separation needed at a leaf. -/
theorem initialDirection_arg_ne_of_inter_eq_start (p q : Polyline)
    (hp : p.IsSimple) (hq : q.IsSimple)
    (hlp : 2 ≤ p.points.length) (hlq : 2 ≤ q.points.length)
    (hs : q.start = p.start) (hi : p.image ∩ q.image = {p.start}) :
    p.initialDirection.arg ≠ q.initialDirection.arg := by
  have hpn : p.initialDirection ≠ 0 := by
    intro h
    exact hp.1 0 (by omega) (p.point_zero_eq_start.trans (sub_eq_zero.mp h).symm)
  have hqn : q.initialDirection ≠ 0 := by
    intro h
    exact hq.1 0 (by omega) (q.point_zero_eq_start.trans (sub_eq_zero.mp h).symm)
  intro heq
  let r := ‖q.initialDirection‖ / ‖p.initialDirection‖
  have hr : 0 < r := div_pos (norm_pos_iff.mpr hqn) (norm_pos_iff.mpr hpn)
  have hdir : q.initialDirection = r • p.initialDirection := by
    rw [Complex.real_smul]
    simpa only [r, Complex.ofReal_div] using ((Complex.arg_eq_arg_iff hpn hqn).mp heq).symm
  let s := min (1 / 2 : ℝ) (r / 2)
  have hspos : 0 < s := lt_min (by norm_num) (half_pos hr)
  have hsone : s ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hsr : s ≤ r := (min_le_right _ _).trans (by linarith only [hr])
  let z := p.start + s • p.initialDirection
  have hzp : z ∈ p.image := by
    refine Or.inr ⟨0, by omega, ?_⟩
    rw [segmentAt, point_zero_eq_start, segment_eq_image']
    exact ⟨s, ⟨hspos.le, hsone⟩, rfl⟩
  have hzq : z ∈ q.image := by
    refine Or.inr ⟨0, by omega, ?_⟩
    rw [segmentAt, point_zero_eq_start, segment_eq_image']
    refine ⟨s / r, ⟨div_nonneg hspos.le hr.le, (div_le_one hr).mpr hsr⟩, ?_⟩
    change q.start + (s / r) • q.initialDirection = z
    rw [hs, hdir, smul_smul, div_mul_cancel₀ _ hr.ne']
  have hzroot : z = p.start := hi.subset ⟨hzp, hzq⟩
  have hzero : s • p.initialDirection = 0 := add_eq_left.mp hzroot
  rcases smul_eq_zero.mp hzero with h | h
  · exact hspos.ne' h
  · exact hpn h

end Polyline

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: a geometrically disjoint access arc
can be inserted at a leaf, with the full-turn angular slot proved from
geometry. Every old dart arc and vertex position is preserved. -/
theorem exists_pendantDrawing_at_leaf {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (a : B.D) (hleaf : B.map.rot a = a) (g : Polyline)
    (hg : g.IsSimple) (hlen : 2 ≤ g.points.length)
    (hs : g.start = P.pos (vert a))
    (hcontact : g.image ∩ P.image = {g.start}) :
    ∃ Q : PLDrawing (B.insertPendant a).D (Option V)
      (B.insertPendant a).map.edgeInv (B.insertPendant a).map.rot (B.pendantVert vert a),
      (∀ v, Q.pos (some v) = P.pos v) ∧
      (∀ d : B.D, Q.arc (.inl d) = P.arc d) ∧
      Q.pos none = g.finish ∧ Q.arc (.inr true) = g ∧
      Q.image = P.image ∪ g.image := by
  have hne : g.start ≠ g.finish := by
    exact Polyline.start_ne_finish_of_isSimple g hlen hg
  have hnot : g.finish ∉ P.image := by
    intro h
    have heq : g.finish = g.start := hcontact.subset ⟨g.finish_mem_image_cornerAccess, h⟩
    exact hne heq.symm
  have hdis : Disjoint g.interior P.image := by
    apply Set.disjoint_left.mpr
    intro z hz hzP
    have heq : z = g.start := hcontact.subset ⟨hz.1, hzP⟩
    exact hz.2 (Or.inl heq)
  have hargs : (P.arc a).initialDirection.arg ≠ g.initialDirection.arg := by
    apply Polyline.initialDirection_arg_ne_of_inter_eq_start (P.arc a) g
      (P.arc_simple a) hg (P.arc_length a) hlen (hs.trans (P.arc_start a).symm)
    apply Set.Subset.antisymm
    · intro z hz
      have heq : z = g.start := hcontact.subset ⟨hz.2, Or.inr ⟨a, hz.1⟩⟩
      exact heq.trans (hs.trans (P.arc_start a).symm)
    · rintro z rfl
      exact ⟨Or.inl rfl, Or.inl ((P.arc_start a).trans hs.symm)⟩
  have hslot : ccwTurn (P.arc a).initialDirection g.initialDirection <
      ccwTurn (P.arc a).initialDirection (P.arc (B.map.rot a)).initialDirection := by
    rw [hleaf, (ccwTurn_eq_two_pi_iff _ _).mpr rfl]
    exact d39_ccwTurn_lt_two_pi hargs
  exact ⟨B.insertPendantDrawing vert P a g.finish hnot g hg hs rfl hdis hslot,
    fun _ => rfl, fun _ => rfl, rfl, rfl,
    B.insertPendantDrawing_image vert P a g.finish hnot g hg hs rfl hdis hslot⟩

/-- Helper toward Proposition 5.16: the first straight frame side can be
inserted at the first-contact leaf. All old and access-pendant darts retain
their entire polylines, and the new side has exactly two listed points. -/
theorem exists_first_quadrilateral_side_drawing {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (a : B.D)
    (Q : PLDrawing (B.insertPendant a).D (Option V)
      (B.insertPendant a).map.edgeInv (B.insertPendant a).map.rot (B.pendantVert vert a))
    (A B₁ C : ℂ)
    (hF : (Polyline.ofHead (Q.pos none) [A, B₁, C, Q.pos none]).IsCyclicSimple)
    (hcontact : (Polyline.ofHead (Q.pos none) [A, B₁, C, Q.pos none]).image ∩ Q.image =
      {Q.pos none}) :
    let D := B.insertPendant a
    let v := B.pendantVert vert a
    ∃ T : PLDrawing (D.insertPendant (.inr false)).D (Option (Option V))
      (D.insertPendant (.inr false)).map.edgeInv (D.insertPendant (.inr false)).map.rot
        (D.pendantVert v (.inr false)),
      (∀ x, T.pos (some x) = Q.pos x) ∧
      (∀ d : D.D, T.arc (.inl d) = Q.arc d) ∧
      T.pos none = A ∧
      T.arc (.inr true) = Polyline.cornerSegment (Q.pos none) A ∧
      (T.arc (.inr true)).points.length = 2 := by
  dsimp only
  let g := Polyline.cornerSegment (Q.pos none) A
  have hne : Q.pos none ≠ A := hF.2.2.1 0 (by change 1 < 5; omega)
  have hg : g.IsSimple := Polyline.isSimple_cornerSegment hne
  have hgsub : g.image ⊆ (Polyline.ofHead (Q.pos none) [A, B₁, C, Q.pos none]).image := by
    rw [Polyline.image_cornerSegment]
    exact (Polyline.ofHead (Q.pos none) [A, B₁, C, Q.pos none]).segmentAt_subset_image
      (i := 0) (by change 1 < 5; omega)
  have hct : g.image ∩ Q.image = {g.start} := by
    apply Set.Subset.antisymm
    · intro z hz
      exact hcontact.subset ⟨hgsub hz.1, hz.2⟩
    · rintro z rfl
      exact ⟨Or.inl rfl, Or.inl ⟨none, rfl⟩⟩
  obtain ⟨T, hp, ha, hf, he, _⟩ := (B.insertPendant a).exists_pendantDrawing_at_leaf
    (B.pendantVert vert a) Q (.inr false) (by rfl) g hg
    (by change 2 ≤ 2; omega) rfl hct
  exact ⟨T, hp, ha, hf, he, by rw [he]; rfl⟩

/-- Helper toward Proposition 5.16: the pendant drawing produced at first
contact stays entirely in the closed square, including its reverse dart.
This uses simplicity of the actual pendant arc, not simplicity of a face. -/
theorem pendantDrawing_image_subset_closedSquare {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (a : B.D)
    (Q : PLDrawing (B.insertPendant a).D (Option V)
      (B.insertPendant a).map.edgeInv (B.insertPendant a).map.rot (B.pendantVert vert a))
    (R : ℝ) (hR : 0 < R)
    (hbound : ∀ z ∈ P.image, max |z.re| |z.im| < R)
    (hpos : ∀ v, Q.pos (some v) = P.pos v)
    (harc : ∀ d : B.D, Q.arc (.inl d) = P.arc d)
    (hcontact : (Q.arc (.inr true)).image ∩ (Polyline.enclosingSquare R).image =
      {Q.pos none}) :
    Q.image ⊆ closure (Polyline.enclosingSquare R).inside := by
  have hfinish : (Q.arc (.inr true)).finish = Q.pos none := Q.arc_finish _
  have hstart : max |(Q.arc (.inr true)).start.re| |(Q.arc (.inr true)).start.im| < R := by
    have hs : (Q.arc (.inr true)).start = Q.pos (some (vert a)) := Q.arc_start _
    rw [hs]
    rw [hpos]
    exact hbound _ (Or.inl ⟨vert a, rfl⟩)
  have hq := Polyline.image_subset_closedSquare_of_unique_boundary_contact
    (Q.arc (.inr true)) (Q.arc_length _) (Q.arc_simple _) R hR hstart
    (by rwa [hfinish])
  have hP : P.image ⊆ closure (Polyline.enclosingSquare R).inside := by
    intro z hz
    rw [Polyline.enclosingSquare_closure_inside R hR]
    exact max_le_iff.mp (hbound z hz).le
  have hnone : Q.pos none ∈ closure (Polyline.enclosingSquare R).inside := by
    rw [← hfinish]
    exact hq (Q.arc (.inr true)).finish_mem_image_cornerAccess
  rintro z (⟨v, rfl⟩ | ⟨d, hd⟩)
  · cases v with
    | none => exact hnone
    | some v => rw [hpos]; exact hP (Or.inl ⟨v, rfl⟩)
  · cases d with
    | inl d => rw [harc] at hd; exact hP (Or.inr ⟨d, hd⟩)
    | inr b =>
      cases b with
      | true => exact hq hd
      | false =>
        have hflip : (Q.arc (.inr false)).image = (Q.arc (.inr true)).image :=
          Q.arc_image_flip (.inr true)
        rw [hflip] at hd
        exact hq hd

/-- Helper toward Proposition 5.16: both first-contact pendant drawings
admit enclosing simple quadrilateral frames avoiding the entire respective
drawing except at the new vertex. Original and pendant arcs are retained;
this theorem does not yet insert frame darts or identify an exterior orbit. -/
theorem exists_pendant_drawings_with_disjoint_quadrilateral_frames
    {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) (a : B.D)
    (hext : (¬ Bornology.IsBounded (B.plDartFace vert P hvert a).val) ∧
      (¬ Bornology.IsBounded (B.plDartFace vert P' hvert a).val)) :
    ∃ (R : ℝ)
      (Q Q' : PLDrawing (B.insertPendant a).D (Option V)
        (B.insertPendant a).map.edgeInv (B.insertPendant a).map.rot (B.pendantVert vert a))
      (A B₁ C A' B₁' C' : ℂ),
      let F := Polyline.ofHead (Q.pos none) [A, B₁, C, Q.pos none]
      let F' := Polyline.ofHead (Q'.pos none) [A', B₁', C', Q'.pos none]
      0 < R ∧
        (∀ v, Q.pos (some v) = P.pos v) ∧
        (∀ v, Q'.pos (some v) = P'.pos v) ∧
        (∀ d : B.D, Q.arc (.inl d) = P.arc d) ∧
        (∀ d : B.D, Q'.arc (.inl d) = P'.arc d) ∧
        Q.image ⊆ closure (Polyline.enclosingSquare R).inside ∧
        Q'.image ⊆ closure (Polyline.enclosingSquare R).inside ∧
        F.IsCyclicSimple ∧ F'.IsCyclicSimple ∧
        closure (Polyline.enclosingSquare R).inside ⊆ closure F.inside ∧
        closure (Polyline.enclosingSquare R).inside ⊆ closure F'.inside ∧
        F.image ∩ Q.image = {Q.pos none} ∧
        F'.image ∩ Q'.image = {Q'.pos none} := by
  obtain ⟨R, Q, Q', hR, hb, hp, hp', ha, ha', hc, hc', hct, hct', _, _⟩ :=
    B.exists_pendant_drawings_to_common_enclosingSquare vert P P' hvert a hext
  have hQ := B.pendantDrawing_image_subset_closedSquare vert P a Q R hR
    (fun z hz => hb z (Or.inl hz)) hp ha hct
  have hQ' := B.pendantDrawing_image_subset_closedSquare vert P' a Q' R hR
    (fun z hz => hb z (Or.inr hz)) hp' ha' hct'
  obtain ⟨A, B₁, C, hF, hFin, hFct⟩ :=
    Polyline.exists_corner_quadrilateral R hR (Q.pos none) hc
  obtain ⟨A', B₁', C', hF', hFin', hFct'⟩ :=
    Polyline.exists_corner_quadrilateral R hR (Q'.pos none) hc'
  refine ⟨R, Q, Q', A, B₁, C, A', B₁', C', hR, hp, hp', ha, ha', hQ, hQ',
    hF, hF', hFin, hFin', ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro z hz
      exact hFct.subset ⟨hz.1, hQ hz.2⟩
    · rintro z rfl
      exact ⟨Or.inl rfl, Or.inl ⟨none, rfl⟩⟩
  · apply Set.Subset.antisymm
    · intro z hz
      exact hFct'.subset ⟨hz.1, hQ' hz.2⟩
    · rintro z rfl
      exact ⟨Or.inl rfl, Or.inl ⟨none, rfl⟩⟩

end D39FiniteBall
end DirectedDistances.PlanarMap

end



















































































































