/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39TriangleWinding

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open scoped ComplexConjugate

/-- Helper toward Proposition 5.16: a point strictly to the left of `a → b`
has a quotient with positive imaginary part. -/
theorem d39_im_div_pos_of_leftOf (a b z : ℂ)
    (hleft : 0 < (conj (b - a) * (z - a)).im) :
    0 < ((b - z) / (a - z)).im := by
  have hza : a - z ≠ 0 := by
    intro h
    have haz : a = z := sub_eq_zero.mp h
    subst z
    simp at hleft
  have hnum :
      (b - z).im * (a - z).re - (b - z).re * (a - z).im =
        (conj (b - a) * (z - a)).im := by
    simp only [Complex.sub_im, Complex.sub_re, Complex.conj_re,
      Complex.conj_im, Complex.mul_im]
    ring
  rw [Complex.div_im, ← sub_div, hnum]
  exact div_pos hleft (Complex.normSq_pos.mpr hza)

/-- Helper toward Proposition 5.16: the principal edge angle is in `(0, pi)`
whenever the point is strictly left of the oriented edge. -/
theorem d39_arg_div_mem_Ioo_of_leftOf (a b z : ℂ)
    (hleft : 0 < (conj (b - a) * (z - a)).im) :
    Complex.arg ((b - z) / (a - z)) ∈ Set.Ioo 0 Real.pi := by
  have hIm := d39_im_div_pos_of_leftOf a b z hleft
  have harg_nonneg : 0 ≤ Complex.arg ((b - z) / (a - z)) :=
    (Complex.arg_nonneg_iff).2 hIm.le
  have harg_ne : Complex.arg ((b - z) / (a - z)) ≠ 0 := by
    intro hz
    have hzero := (Complex.arg_eq_zero_iff).1 hz
    exact hIm.ne' hzero.2
  have harg_pos : 0 < Complex.arg ((b - z) / (a - z)) :=
    lt_of_le_of_ne harg_nonneg (Ne.symm harg_ne)
  have harg_lt : Complex.arg ((b - z) / (a - z)) < Real.pi := by
    apply Complex.arg_lt_pi_iff.mpr
    exact Or.inr hIm.ne'
  exact ⟨harg_pos, harg_lt⟩

/-- Helper toward Proposition 5.16: every polyline edge angle is positive and
less than `pi` when the point is strictly to the left of that edge. -/
theorem d39_edgeAngle_mem_Ioo_of_leftOf (p : Polyline) (z : ℂ) (i : ℕ)
    (hleft : 0 < (conj (p.point (i + 1) - p.point i) *
      (z - p.point i)).im) :
    p.edgeAngle z i ∈ Set.Ioo 0 Real.pi := by
  exact d39_arg_div_mem_Ioo_of_leftOf _ _ _ hleft

/-- Helper toward Proposition 5.16: the oriented-side determinant vanishes
on the closed segment joining the two endpoints. -/
theorem d39_leftSide_eq_zero_of_mem_segment {a b z : ℂ}
    (hz : z ∈ segment ℝ a b) :
    (conj (b - a) * (z - a)).im = 0 := by
  rw [segment_eq_image'] at hz
  rcases hz with ⟨θ, hθ, hz⟩
  rw [← hz]
  simp only [add_sub_cancel_left]
  rw [RCLike.real_smul_eq_coe_mul]
  simp [Complex.mul_im]
  ring

/-- Helper toward Proposition 5.16: the first triangle-side determinant at a
barycentric point is the second barycentric weight times the triangle area. -/
theorem d39_leftSide_origin_barycentric (a b : ℂ) (s t : ℝ) :
    (conj a * ((s : ℂ) * a + (t : ℂ) * b)).im =
      t * (conj a * b).im := by
  simp [Complex.mul_im]
  <;> ring

/-- Helper toward Proposition 5.16: the chord-side determinant at a
barycentric point is the remaining barycentric weight times the triangle area. -/
theorem d39_leftSide_chord_barycentric (a b : ℂ) (s t : ℝ) :
    (conj (b - a) * ((s : ℂ) * a + (t : ℂ) * b - a)).im =
      (1 - s - t) * (conj a * b).im := by
  simp [Complex.mul_im]
  <;> ring

/-- Helper toward Proposition 5.16: the last triangle-side determinant at a
barycentric point is the first barycentric weight times the triangle area. -/
theorem d39_leftSide_last_barycentric (a b : ℂ) (s t : ℝ) :
    (conj (0 - b) * ((s : ℂ) * a + (t : ℂ) * b - b)).im =
      s * (conj a * b).im := by
  simp [Complex.mul_im]
  <;> ring

/-- Helper toward Proposition 5.16: the area determinant of `r * u`, `r * v`
is positive when the argument of `v / u` lies in `(0, pi)`. -/
theorem d39_triangle_area_pos (r : ℝ) (u v : ℂ)
    (hu : u ≠ 0) (hr : 0 < r)
    (harg : 0 < Complex.arg (v / u))
    (hargPi : Complex.arg (v / u) < Real.pi) :
    (conj ((r : ℂ) * u) * ((r : ℂ) * v)).im > 0 := by
  have hqim_nonneg : 0 ≤ (v / u).im :=
    (Complex.arg_nonneg_iff).1 harg.le
  have hqim_ne : (v / u).im ≠ 0 := by
    intro hzero
    have hre : 0 ≤ (v / u).re := by
      rcases (Complex.arg_lt_pi_iff).1 hargPi with hre | him
      · exact hre
      · exact (him hzero).elim
    have hargZero := (Complex.arg_eq_zero_iff).2 ⟨hre, hzero⟩
    exact harg.ne' hargZero
  have hqim : 0 < (v / u).im := lt_of_le_of_ne hqim_nonneg (Ne.symm hqim_ne)
  have hdet : 0 < (conj u * v).im := by
    have hfactor : (conj u * v).im = Complex.normSq u * (v / u).im := by
      calc
        (conj u * v).im = (conj u * ((v / u) * u)).im := by
          have hqu : (v / u) * u = v := div_mul_cancel₀ v hu
          exact congrArg Complex.im (congrArg (fun x : ℂ => conj u * x) hqu.symm)
        _ = ((Complex.normSq u : ℂ) * (v / u)).im := by
          congr 1
          calc
            conj u * ((v / u) * u) = (conj u * u) * (v / u) := by ring
            _ = (Complex.normSq u : ℂ) * (v / u) := by
              rw [← Complex.normSq_eq_conj_mul_self]
        _ = Complex.normSq u * (v / u).im := by simp
    rw [hfactor]
    exact mul_pos (Complex.normSq_pos.mpr hu) hqim
  have hscale :
      conj ((r : ℂ) * u) * ((r : ℂ) * v) =
        ((r * r : ℝ) : ℂ) * (conj u * v) := by
    rw [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  have himscale : (((r * r : ℝ) : ℂ) * (conj u * v)).im =
      (r * r) * (conj u * v).im := by simp
  rw [hscale]
  rw [himscale]
  exact mul_pos (mul_pos hr hr) hdet

/-- Helper toward Proposition 5.16: strict left-side inequalities on the
three directed triangle edges imply that the point avoids the polyline image. -/
theorem d39_triangle_not_mem_image_of_leftSides (r : ℝ) (u v z : ℂ)
    (h0 : 0 < (conj ((r : ℂ) * u) * z).im)
    (h1 : 0 < (conj ((r : ℂ) * v - (r : ℂ) * u) *
      (z - (r : ℂ) * u)).im)
    (h2 : 0 < (conj (0 - (r : ℂ) * v) *
      (z - (r : ℂ) * v)).im) :
    z ∉ (d39TrianglePolyline r u v).image := by
  let p := d39TrianglePolyline r u v
  intro hz
  change z = p.start ∨ ∃ i, i + 1 < p.points.length ∧ z ∈ p.segmentAt i at hz
  rcases hz with hstart | ⟨i, hi, hseg⟩
  · have hpstart : p.start = 0 := by simp [p, d39TrianglePolyline, Polyline.start]
    rw [hpstart] at hstart
    subst z
    simp at h0
  · have hlen : p.points.length = 4 := by simp [p, d39TrianglePolyline]
    rw [hlen] at hi
    have hi' : i < 3 := by omega
    interval_cases i
    · have hseg' : z ∈ segment ℝ 0 ((r : ℂ) * u) := by
        simpa [p, d39TrianglePolyline, Polyline.segmentAt, Polyline.point,
          Polyline.start] using hseg
      have hzero := d39_leftSide_eq_zero_of_mem_segment hseg'
      have hzero' : (conj ((r : ℂ) * u) * z).im = 0 := by
        simpa [sub_zero] using hzero
      linarith
    · have hseg' : z ∈ segment ℝ ((r : ℂ) * u) ((r : ℂ) * v) := by
        simpa [p, d39TrianglePolyline, Polyline.segmentAt, Polyline.point,
          Polyline.start] using hseg
      have hzero := d39_leftSide_eq_zero_of_mem_segment hseg'
      linarith
    · have hseg' : z ∈ segment ℝ ((r : ℂ) * v) 0 := by
        simpa [p, d39TrianglePolyline, Polyline.segmentAt, Polyline.point,
          Polyline.start] using hseg
      have hzero := d39_leftSide_eq_zero_of_mem_segment hseg'
      linarith

/-- Helper toward Proposition 5.16: a point in the open barycentric triangle
has positive angle on each edge and winding one around the triangle loop. -/
theorem d39_triangle_openTriangle_angleSum_eq_one_and_hasWinding
    (r : ℝ) (u v z : ℂ)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (harg : 0 < Complex.arg (v / u))
    (hargPi : Complex.arg (v / u) < Real.pi)
    (hr : 0 < r)
    (hz : z ∈ d39OpenTriangle r u v) :
    (d39TrianglePolyline r u v).angleSum z = 1 ∧
      HasWinding
        ((d39TrianglePolyline r u v).toPath.cast rfl
          (d39TrianglePolyline_closed r u v)) z 1 := by
  rcases hz with ⟨s, t, hs, ht, hst, hz⟩
  let a := (r : ℂ) * u
  let b := (r : ℂ) * v
  have harea : 0 < (conj a * b).im := by
    simpa [a, b] using d39_triangle_area_pos r u v hu hr harg hargPi
  have hzform : z = (s : ℂ) * a + (t : ℂ) * b := by
    rw [hz]
    dsimp [a, b]
    push_cast
    ring
  have hremain : 0 < 1 - s - t := by linarith
  have hleft0 : 0 < (conj a * z).im := by
    rw [hzform, d39_leftSide_origin_barycentric]
    exact mul_pos ht harea
  have hleft1 : 0 < (conj (b - a) * (z - a)).im := by
    rw [hzform, d39_leftSide_chord_barycentric]
    exact mul_pos hremain harea
  have hleft2 : 0 < (conj (0 - b) * (z - b)).im := by
    rw [hzform, d39_leftSide_last_barycentric]
    exact mul_pos hs harea
  have hleft0' : 0 < (conj ((r : ℂ) * u) * z).im := by
    change 0 < (conj a * z).im
    exact hleft0
  have hleft1' : 0 <
      (conj ((r : ℂ) * v - (r : ℂ) * u) * (z - (r : ℂ) * u)).im := by
    change 0 < (conj (b - a) * (z - a)).im
    exact hleft1
  have hleft2' : 0 <
      (conj (0 - (r : ℂ) * v) * (z - (r : ℂ) * v)).im := by
    change 0 < (conj (0 - b) * (z - b)).im
    exact hleft2
  have hzavoid := d39_triangle_not_mem_image_of_leftSides r u v z
    hleft0' hleft1' hleft2'
  have hangle0 :
      0 < (d39TrianglePolyline r u v).edgeAngle z 0 := by
    have hleft : 0 <
        (conj ((d39TrianglePolyline r u v).point 1 -
          (d39TrianglePolyline r u v).point 0) *
          (z - (d39TrianglePolyline r u v).point 0)).im := by
      change 0 < (conj (a - 0) * (z - 0)).im
      simpa using hleft0
    exact (d39_edgeAngle_mem_Ioo_of_leftOf _ _ _ hleft).1
  have hangle1 :
      0 < (d39TrianglePolyline r u v).edgeAngle z 1 := by
    have hleft : 0 <
        (conj ((d39TrianglePolyline r u v).point 2 -
          (d39TrianglePolyline r u v).point 1) *
          (z - (d39TrianglePolyline r u v).point 1)).im := by
      change 0 < (conj (b - a) * (z - a)).im
      exact hleft1
    exact (d39_edgeAngle_mem_Ioo_of_leftOf _ _ _ hleft).1
  have hangle2 :
      0 < (d39TrianglePolyline r u v).edgeAngle z 2 := by
    have hleft : 0 <
        (conj ((d39TrianglePolyline r u v).point 3 -
          (d39TrianglePolyline r u v).point 2) *
          (z - (d39TrianglePolyline r u v).point 2)).im := by
      change 0 < (conj (0 - b) * (z - b)).im
      exact hleft2
    exact (d39_edgeAngle_mem_Ioo_of_leftOf _ _ _ hleft).1
  exact ⟨
    d39_triangle_angleSum_eq_one_of_positive_edgeAngles r u v z hzavoid
      hangle0 hangle1 hangle2,
    d39_triangle_hasWinding_one_of_positive_edgeAngles r u v z hzavoid
      hangle0 hangle1 hangle2⟩

/-- Helper toward Proposition 5.16: along the ray opposite the first triangle
side, the triangle angle sum vanishes for every positive radius. -/
theorem d39_triangle_angleSum_eq_zero_on_negative_ray
    (r ρ : ℝ) (u v : ℂ)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hr : 0 < r) (hρ : 0 < ρ)
    (harg : 0 < Complex.arg (v / u))
    (hargPi : Complex.arg (v / u) < Real.pi) :
    (d39TrianglePolyline r u v).angleSum (-(ρ : ℂ) * u) = 0 := by
  let q : ℂ := (r : ℂ) * (v / u) + (ρ : ℂ)
  have hquotIm : 0 < (v / u).im := by
    have hnonneg : 0 ≤ (v / u).im :=
      (Complex.arg_nonneg_iff).1 harg.le
    have hne : (v / u).im ≠ 0 := by
      intro hz
      have hre : 0 ≤ (v / u).re := by
        rcases (Complex.arg_lt_pi_iff).1 hargPi with hre | him
        · exact hre
        · exact (him hz).elim
      have hargZero := (Complex.arg_eq_zero_iff).2 ⟨hre, hz⟩
      exact harg.ne' hargZero
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hqIm : 0 < q.im := by
    dsimp [q]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add]
    linarith [mul_pos hr hquotIm]
  have hq : q ≠ 0 := by
    intro h
    rw [h] at hqIm
    simp at hqIm
  have hq_u : q * u = (r : ℂ) * v + (ρ : ℂ) * u := by
    dsimp [q]
    field_simp [hu]
  have hquot0 :
      ((d39TrianglePolyline r u v).point 1 + (ρ : ℂ) * u) /
          ((d39TrianglePolyline r u v).point 0 + (ρ : ℂ) * u) =
        ((r + ρ : ℝ) : ℂ) / (ρ : ℂ) := by
    change (((r : ℂ) * u + (ρ : ℂ) * u) /
      (0 + (ρ : ℂ) * u)) = _
    have hsum : 0 < r + ρ := add_pos hr hρ
    simp only [zero_add]
    field_simp [hu, hρ.ne', hsum.ne']
    <;> push_cast
    <;> ring
  have hquot1 :
      ((d39TrianglePolyline r u v).point 2 + (ρ : ℂ) * u) /
          ((d39TrianglePolyline r u v).point 1 + (ρ : ℂ) * u) =
        q / (r + ρ : ℝ) := by
    change (((r : ℂ) * v + (ρ : ℂ) * u) /
      ((r : ℂ) * u + (ρ : ℂ) * u)) = _
    rw [← hq_u]
    have hsum : 0 < r + ρ := add_pos hr hρ
    field_simp [hu, hsum.ne']
    <;> push_cast
    <;> ring
  have hquot2 :
      ((d39TrianglePolyline r u v).point 3 + (ρ : ℂ) * u) /
        ((d39TrianglePolyline r u v).point 2 + (ρ : ℂ) * u) =
        (ρ : ℂ) / q := by
    change ((0 + (ρ : ℂ) * u) /
      ((r : ℂ) * v + (ρ : ℂ) * u)) = _
    simp only [zero_add]
    rw [← hq_u]
    field_simp [hu, hq]
  have harg0 :
      (d39TrianglePolyline r u v).edgeAngle (-(ρ : ℂ) * u) 0 = 0 := by
    rw [Polyline.edgeAngle]
    simp only [neg_mul, sub_neg_eq_add, Nat.zero_add]
    change Complex.arg
      (((d39TrianglePolyline r u v).point 1 + (ρ : ℂ) * u) /
        ((d39TrianglePolyline r u v).point 0 + (ρ : ℂ) * u)) = 0
    rw [hquot0]
    rw [← Complex.ofReal_div]
    exact Complex.arg_ofReal_of_nonneg (div_pos (add_pos hr hρ) hρ).le
  have harg1 :
      (d39TrianglePolyline r u v).edgeAngle (-(ρ : ℂ) * u) 1 = q.arg := by
    rw [Polyline.edgeAngle]
    simp only [neg_mul, sub_neg_eq_add, Nat.one_add]
    change Complex.arg
      (((d39TrianglePolyline r u v).point 2 + (ρ : ℂ) * u) /
        ((d39TrianglePolyline r u v).point 1 + (ρ : ℂ) * u)) = q.arg
    rw [hquot1]
    have hsum : 0 < r + ρ := add_pos hr hρ
    have hcoe : q / (r + ρ : ℝ) = q * ((1 / (r + ρ) : ℝ) : ℂ) := by
      simp [div_eq_mul_inv, Complex.ofReal_inv, one_div]
    rw [hcoe, Complex.arg_mul_real (div_pos one_pos hsum) q]
  have harg2 :
      (d39TrianglePolyline r u v).edgeAngle (-(ρ : ℂ) * u) 2 = -q.arg := by
    rw [Polyline.edgeAngle]
    simp only [neg_mul, sub_neg_eq_add, Nat.add_one]
    change Complex.arg
      (((d39TrianglePolyline r u v).point 3 + (ρ : ℂ) * u) /
        ((d39TrianglePolyline r u v).point 2 + (ρ : ℂ) * u)) = -q.arg
    rw [hquot2]
    have hcoe : (ρ : ℂ) / q = ((ρ : ℝ) : ℂ) * q⁻¹ := by
      simp [div_eq_mul_inv]
    rw [hcoe, Complex.arg_real_mul (q⁻¹) hρ]
    rw [Complex.arg_inv]
    simp [ne_of_lt (Complex.arg_lt_pi_iff.mpr (Or.inr hqIm.ne'))]
  have hsum :
      (d39TrianglePolyline r u v).edgeAngle (-(ρ : ℂ) * u) 0 +
        (d39TrianglePolyline r u v).edgeAngle (-(ρ : ℂ) * u) 1 +
        (d39TrianglePolyline r u v).edgeAngle (-(ρ : ℂ) * u) 2 = 0 := by
    rw [harg0, harg1, harg2]
    ring
  have hangleSum :
      (d39TrianglePolyline r u v).angleSum (-(ρ : ℂ) * u) =
        ((d39TrianglePolyline r u v).edgeAngle (-(ρ : ℂ) * u) 0 +
          (d39TrianglePolyline r u v).edgeAngle (-(ρ : ℂ) * u) 1 +
          (d39TrianglePolyline r u v).edgeAngle (-(ρ : ℂ) * u) 2) /
          (2 * Real.pi) := by
    simp only [Polyline.angleSum]
    have hlen : (d39TrianglePolyline r u v).points.length = 4 := by
      simp [d39TrianglePolyline]
    rw [show (d39TrianglePolyline r u v).points.length - 1 = 3 by omega]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hangleSum, hsum]
  simp

/-- Helper toward Proposition 5.16: the ray opposite `u` lies outside the
closed wedge generated by `u` and `v` when their counterclockwise turn is in
`(0, pi)`. -/
theorem d39_negative_ray_not_mem_closedWedge (ρ : ℝ) (u v : ℂ)
    (hu : u ≠ 0) (hρ : 0 < ρ)
    (harg : 0 < Complex.arg (v / u))
    (hargPi : Complex.arg (v / u) < Real.pi) :
    -(ρ : ℂ) * u ∉ d39ClosedWedge u v := by
  intro hz
  rcases hz with ⟨s, t, hs, ht, heq⟩
  have hdet : 0 < (conj u * v).im := by
    simpa using d39_triangle_area_pos 1 u v hu one_pos harg hargPi
  have hcross := congrArg (fun x : ℂ => (conj u * x).im) heq
  have hzero : (conj u * (-(ρ : ℂ) * u)).im = 0 := by
    simp [Complex.mul_im]
    ring
  rw [hzero, d39_leftSide_origin_barycentric] at hcross
  have ht0 : t = 0 := by nlinarith
  subst t
  have heq' : -(ρ : ℂ) * u = (s : ℂ) * u := by simpa using heq
  have hscalar : -(ρ : ℝ) = s := by
    have hdiv := congrArg (fun x : ℂ => x / u) heq'
    field_simp [hu] at hdiv
    exact_mod_cast hdiv
  linarith










































end DirectedDistances.PlanarMap

end
