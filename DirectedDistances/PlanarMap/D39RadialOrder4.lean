/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39RadialOrder3







public section

noncomputable section

namespace DirectedDistances.PlanarMap

open scoped ComplexConjugate

/-- Helper toward Proposition 5.16: for three distinct arguments, the
counterclockwise cyclic turn sum is `2 * pi` exactly when the second ray lies
before the third ray in the turn from the first ray. -/
theorem d39_cyclic_turn_sum_eq_two_pi_iff_ordered
    {u v w : ℂ} (_huv : u.arg ≠ v.arg) (huw : u.arg ≠ w.arg)
    (hvw : v.arg ≠ w.arg) :
    ccwTurn u v + ccwTurn v w + ccwTurn w u = 2 * Real.pi ↔
      ccwTurn u v < ccwTurn u w := by
  have hturn_ne : ccwTurn u v ≠ ccwTurn u w := by
    intro h
    exact hvw (ccwTurn_left_injective h)
  have hwu := ccwTurn_add_reverse w u (Ne.symm huw)
  have hvw' := ccwTurn_add_reverse v w hvw
  constructor
  · intro hsum
    by_contra horder
    have hlt : ccwTurn u w < ccwTurn u v :=
      lt_of_le_of_ne (le_of_not_gt horder) (Ne.symm hturn_ne)
    have hcomp := ccwTurn_comp_add (a := u) (b := w) (c := v) hlt
    have hwv := ccwTurn_add_reverse w v (Ne.symm hvw)
    have hsum4 : ccwTurn u v + ccwTurn v w + ccwTurn w u = 4 * Real.pi := by
      linarith
    linarith [Real.pi_pos]
  · intro horder
    have hcomp := ccwTurn_comp_add (a := u) (b := v) (c := w) horder
    linarith

/-- Helper toward Proposition 5.16: for three distinct arguments, the
counterclockwise cyclic turn sum is either `2 * pi` or `4 * pi`. -/
theorem d39_cyclic_turn_sum_eq_two_or_four_pi
    {u v w : ℂ} (_huv : u.arg ≠ v.arg) (huw : u.arg ≠ w.arg)
    (hvw : v.arg ≠ w.arg) :
    ccwTurn u v + ccwTurn v w + ccwTurn w u = 2 * Real.pi ∨
      ccwTurn u v + ccwTurn v w + ccwTurn w u = 4 * Real.pi := by
  have hturn_ne : ccwTurn u v ≠ ccwTurn u w := by
    intro h
    exact hvw (ccwTurn_left_injective h)
  rcases lt_or_gt_of_ne hturn_ne with horder | hreverse
  · exact Or.inl ((d39_cyclic_turn_sum_eq_two_pi_iff_ordered _huv huw hvw).2 horder)
  · have hwu := ccwTurn_add_reverse w u (Ne.symm huw)
    have hvw' := ccwTurn_add_reverse v w hvw
    have hcomp := ccwTurn_comp_add (a := u) (b := w) (c := v) hreverse
    have hwv := ccwTurn_add_reverse w v (Ne.symm hvw)
    right
    -- The reverse ordering contributes two full turns after telescoping.
    have : ccwTurn u v + ccwTurn v w + ccwTurn w u = 4 * Real.pi := by
      linarith
    exact this

/-- Helper toward Proposition 5.16: the closed triangular polyline through
`a`, `b`, and `c`, in that order. -/
@[expose] def d39CyclicTrianglePolyline (a b c : ℂ) : Polyline :=
  ⟨[a, b, c, a], by simp⟩

/-- Helper toward Proposition 5.16: the cyclic triangle polyline is closed. -/
theorem d39CyclicTrianglePolyline_closed (a b c : ℂ) :
    (d39CyclicTrianglePolyline a b c).start =
      (d39CyclicTrianglePolyline a b c).finish := by
  simp [d39CyclicTrianglePolyline, Polyline.start, Polyline.finish]

/-- Helper toward Proposition 5.16: a point strictly to the left of all
three directed sides avoids the closed triangular polyline. -/
theorem d39_cyclicTriangle_not_mem_image_of_leftSides
    (a b c z : ℂ)
    (h0 : 0 < (conj (b - a) * (z - a)).im)
    (h1 : 0 < (conj (c - b) * (z - b)).im)
    (h2 : 0 < (conj (a - c) * (z - c)).im) :
    z ∉ (d39CyclicTrianglePolyline a b c).image := by
  intro hz
  change z = (d39CyclicTrianglePolyline a b c).start ∨
    ∃ i, i + 1 < (d39CyclicTrianglePolyline a b c).points.length ∧
      z ∈ (d39CyclicTrianglePolyline a b c).segmentAt i at hz
  rcases hz with hstart | ⟨i, hi, hseg⟩
  · subst z
    simp [d39CyclicTrianglePolyline, Polyline.start] at h0
  · have hlen : (d39CyclicTrianglePolyline a b c).points.length = 4 := by
      simp [d39CyclicTrianglePolyline]
    have hi' : i < 3 := by omega
    interval_cases i
    · have hseg' : z ∈ segment ℝ a b := by
        simpa [d39CyclicTrianglePolyline, Polyline.segmentAt, Polyline.point,
          Polyline.start] using hseg
      have hzero := d39_leftSide_eq_zero_of_mem_segment hseg'
      exact (ne_of_gt h0) hzero
    · have hseg' : z ∈ segment ℝ b c := by
        simpa [d39CyclicTrianglePolyline, Polyline.segmentAt, Polyline.point,
          Polyline.start] using hseg
      have hzero := d39_leftSide_eq_zero_of_mem_segment hseg'
      exact (ne_of_gt h1) hzero
    · have hseg' : z ∈ segment ℝ c a := by
        simpa [d39CyclicTrianglePolyline, Polyline.segmentAt, Polyline.point,
          Polyline.start] using hseg
      have hzero := d39_leftSide_eq_zero_of_mem_segment hseg'
      exact (ne_of_gt h2) hzero

/-- Helper toward Proposition 5.16: three positive edge angles at an avoided
point force the cyclic triangle's normalized angle sum to be one. -/
theorem d39_cyclicTriangle_angleSum_eq_one_of_positive_edgeAngles
    (a b c z : ℂ)
    (hz : z ∉ (d39CyclicTrianglePolyline a b c).image)
    (h0 : 0 < (d39CyclicTrianglePolyline a b c).edgeAngle z 0)
    (h1 : 0 < (d39CyclicTrianglePolyline a b c).edgeAngle z 1)
    (h2 : 0 < (d39CyclicTrianglePolyline a b c).edgeAngle z 2) :
    (d39CyclicTrianglePolyline a b c).angleSum z = 1 := by
  let p := d39CyclicTrianglePolyline a b c
  have hclosed : p.start = p.finish := d39CyclicTrianglePolyline_closed a b c
  have hlen : p.points.length = 4 := by simp [p, d39CyclicTrianglePolyline]
  have hi0 : 0 + 1 < p.points.length := by omega
  have hi1 : 1 + 1 < p.points.length := by omega
  have hi2 : 2 + 1 < p.points.length := by omega
  have h0u := (Polyline.edgeAngle_mem_Ioo p z 0 hi0 hz).2
  have h1u := (Polyline.edgeAngle_mem_Ioo p z 1 hi1 hz).2
  have h2u := (Polyline.edgeAngle_mem_Ioo p z 2 hi2 hz).2
  have hsumPos : 0 < p.edgeAngle z 0 + p.edgeAngle z 1 + p.edgeAngle z 2 := by
    linarith
  have hsumLt : p.edgeAngle z 0 + p.edgeAngle z 1 + p.edgeAngle z 2 <
      3 * Real.pi := by
    linarith
  have hformula : p.angleSum z =
      (p.edgeAngle z 0 + p.edgeAngle z 1 + p.edgeAngle z 2) /
        (2 * Real.pi) := by
    simp only [Polyline.angleSum]
    change (∑ i ∈ Finset.range 3, p.edgeAngle z i) / (2 * Real.pi) = _
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ]
    simp only [Finset.sum_range_zero]
    ring
  have hanglePos : 0 < p.angleSum z := by
    rw [hformula]
    exact div_pos hsumPos (by positivity)
  have hangleLt : p.angleSum z < (3 / 2 : ℝ) := by
    rw [hformula]
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith [Real.pi_pos]
  obtain ⟨n, hn⟩ := Polyline.angleSum_isInt p hclosed z hz
  have hnPosR : (0 : ℝ) < (n : ℝ) := by rw [← hn]; exact hanglePos
  have hnPos : 0 < n := by exact_mod_cast hnPosR
  have hnLtR : (n : ℝ) < 2 := by linarith [hn, hangleLt]
  have hnLt : n < 2 := by exact_mod_cast hnLtR
  have hnOne : n = 1 := by omega
  rw [hn, hnOne]
  norm_num

/-- Helper toward Proposition 5.16: if a point is strictly to the left of
all three directed sides, the cyclic triangle loop winds once around it. -/
theorem d39_cyclicTriangle_hasWinding_one_of_leftSides
    (a b c z : ℂ)
    (h0 : 0 < (conj (b - a) * (z - a)).im)
    (h1 : 0 < (conj (c - b) * (z - b)).im)
    (h2 : 0 < (conj (a - c) * (z - c)).im) :
    HasWinding
      ((d39CyclicTrianglePolyline a b c).toPath.cast rfl
        (d39CyclicTrianglePolyline_closed a b c)) z 1 := by
  have hz := d39_cyclicTriangle_not_mem_image_of_leftSides a b c z h0 h1 h2
  have hleft0 : 0 <
      (conj ((d39CyclicTrianglePolyline a b c).point 1 -
        (d39CyclicTrianglePolyline a b c).point 0) *
        (z - (d39CyclicTrianglePolyline a b c).point 0)).im := by
    simpa [d39CyclicTrianglePolyline, Polyline.point, Polyline.start] using h0
  have hleft1 : 0 <
      (conj ((d39CyclicTrianglePolyline a b c).point 2 -
        (d39CyclicTrianglePolyline a b c).point 1) *
        (z - (d39CyclicTrianglePolyline a b c).point 1)).im := by
    simpa [d39CyclicTrianglePolyline, Polyline.point, Polyline.start] using h1
  have hleft2 : 0 <
      (conj ((d39CyclicTrianglePolyline a b c).point 3 -
        (d39CyclicTrianglePolyline a b c).point 2) *
        (z - (d39CyclicTrianglePolyline a b c).point 2)).im := by
    simpa [d39CyclicTrianglePolyline, Polyline.point, Polyline.start] using h2
  have hangle0 := (d39_edgeAngle_mem_Ioo_of_leftOf _ _ _ hleft0).1
  have hangle1 := (d39_edgeAngle_mem_Ioo_of_leftOf _ _ _ hleft1).1
  have hangle2 := (d39_edgeAngle_mem_Ioo_of_leftOf _ _ _ hleft2).1
  apply (hasWinding_iff_angleSum_eq_int (d39CyclicTrianglePolyline a b c)
    (d39CyclicTrianglePolyline_closed a b c) z 1 hz).2
  simpa using d39_cyclicTriangle_angleSum_eq_one_of_positive_edgeAngles
    a b c z hz hangle0 hangle1 hangle2



































































end DirectedDistances.PlanarMap

end
