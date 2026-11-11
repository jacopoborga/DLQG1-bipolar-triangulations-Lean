/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PolygonWindingBridge2
public import DirectedDistances.PlanarMap.D39CyclicOrderWinding2






public section

noncomputable section

namespace DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16. The closed triangular polyline with
vertices `0`, `r * u`, `r * v`, and `0`, in counterclockwise order when the
argument of `v / u` lies in `(0, pi)`. -/
@[expose] def d39TrianglePolyline (r : ℝ) (u v : ℂ) : Polyline :=
  ⟨[0, (r : ℂ) * u, (r : ℂ) * v, 0], by simp⟩

/-- Helper toward Proposition 5.16. Barycentric description of the open
triangle bounded by the two radial segments and their chord. -/
@[expose] def d39OpenTriangle (r : ℝ) (u v : ℂ) : Set ℂ :=
  {z | ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ s + t < 1 ∧
    z = ((s * r : ℝ) : ℂ) * u + ((t * r : ℝ) : ℂ) * v}

/-- Helper toward Proposition 5.16. The closed cone between the rays through
`u` and `v`, expressed using nonnegative real coefficients. -/
@[expose] def d39ClosedWedge (u v : ℂ) : Set ℂ :=
  {z | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ z = (s : ℂ) * u + (t : ℂ) * v}

/-- Helper toward Proposition 5.16. A polygonal wedge loop: one triangle when
the counterclockwise turn is less than `pi`, and two adjacent triangles, with
their shared radial edge cancelled, when the turn is larger. -/
@[expose] def d39WedgePolyline (r : ℝ) (u v : ℂ) : Polyline :=
  if ccwTurn u v < Real.pi then d39TrianglePolyline r u v
  else
    let m := Complex.exp
      (((Complex.arg u + ccwTurn u v / 2 : ℝ) : ℂ) * Complex.I)
    ⟨[0, (r : ℂ) * u, (r : ℂ) * m, (r : ℂ) * v, 0], by simp⟩

/-- Helper toward Proposition 5.16. The path associated with the polygonal
wedge loop, based at its origin. -/
@[expose] def d39WedgeLoop (r : ℝ) (u v : ℂ) :
    Path (d39WedgePolyline r u v).start (d39WedgePolyline r u v).start :=
  (d39WedgePolyline r u v).toPath.cast rfl (by
    by_cases h : ccwTurn u v < Real.pi
    · simp [d39WedgePolyline, h, d39TrianglePolyline, Polyline.start, Polyline.finish]
    · simp [d39WedgePolyline, h, Polyline.start, Polyline.finish])

/-- Helper toward Proposition 5.16. The open part of the angular wedge within
radius `ε`, using a lifted angular interval of length `δ`. -/
@[expose] def d39OpenWedgeNearZero (ε a δ : ℝ) : Set ℂ :=
  {z | ∃ ρ θ : ℝ, 0 < ρ ∧ ρ < ε ∧ a < θ ∧ θ < a + δ ∧
    z = (ρ : ℂ) * Complex.exp (θ * Complex.I)}

/-- Helper toward Proposition 5.16. The closed unbounded angular wedge with
lifted initial angle `a` and width `δ`. -/
@[expose] def d39ClosedAngularWedge (a δ : ℝ) : Set ℂ :=
  {z | z = 0 ∨ ∃ ρ θ : ℝ, 0 < ρ ∧ a ≤ θ ∧ θ ≤ a + δ ∧
    z = (ρ : ℂ) * Complex.exp (θ * Complex.I)}

/-- Helper toward Proposition 5.16. The triangle polyline is closed. -/
theorem d39TrianglePolyline_closed (r : ℝ) (u v : ℂ) :
    (d39TrianglePolyline r u v).start = (d39TrianglePolyline r u v).finish := by
  simp [d39TrianglePolyline, Polyline.start, Polyline.finish]

/-- Helper toward Proposition 5.16. The polygonal wedge loop is closed. -/
theorem d39WedgePolyline_closed (r : ℝ) (u v : ℂ) :
    (d39WedgePolyline r u v).start = (d39WedgePolyline r u v).finish := by
  by_cases h : ccwTurn u v < Real.pi
  · simp [d39WedgePolyline, h, d39TrianglePolyline, Polyline.start, Polyline.finish]
  · simp [d39WedgePolyline, h, Polyline.start, Polyline.finish]

/-- Helper toward Proposition 5.16. For a point avoiding the triangular
polyline, three strictly positive edge angles force the normalized angle sum
to be one. Integrality supplies the winding-number quantization. -/
theorem d39_triangle_angleSum_eq_one_of_positive_edgeAngles
    (r : ℝ) (u v z : ℂ)
    (hz : z ∉ (d39TrianglePolyline r u v).image)
    (h0 : 0 < (d39TrianglePolyline r u v).edgeAngle z 0)
    (h1 : 0 < (d39TrianglePolyline r u v).edgeAngle z 1)
    (h2 : 0 < (d39TrianglePolyline r u v).edgeAngle z 2) :
    (d39TrianglePolyline r u v).angleSum z = 1 := by
  let p := d39TrianglePolyline r u v
  have hclosed : p.start = p.finish := d39TrianglePolyline_closed r u v
  have hlen : p.points.length = 4 := by simp [p, d39TrianglePolyline]
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
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
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

/-- Helper toward Proposition 5.16. The same angle hypotheses identify the
winding of the triangle loop as one. -/
theorem d39_triangle_hasWinding_one_of_positive_edgeAngles
    (r : ℝ) (u v z : ℂ)
    (hz : z ∉ (d39TrianglePolyline r u v).image)
    (h0 : 0 < (d39TrianglePolyline r u v).edgeAngle z 0)
    (h1 : 0 < (d39TrianglePolyline r u v).edgeAngle z 1)
    (h2 : 0 < (d39TrianglePolyline r u v).edgeAngle z 2) :
    HasWinding
      ((d39TrianglePolyline r u v).toPath.cast rfl
        (d39TrianglePolyline_closed r u v)) z 1 := by
  apply (hasWinding_iff_angleSum_eq_int (d39TrianglePolyline r u v)
    (d39TrianglePolyline_closed r u v) z 1 hz).2
  simpa using d39_triangle_angleSum_eq_one_of_positive_edgeAngles r u v z hz h0 h1 h2

/-- Helper toward Proposition 5.16. A zero triangle angle sum identifies its
winding as zero through the logarithmic lift bridge. -/
theorem d39_triangle_hasWinding_zero_of_angleSum_eq_zero
    (r : ℝ) (u v z : ℂ)
    (hz : z ∉ (d39TrianglePolyline r u v).image)
    (hsum : (d39TrianglePolyline r u v).angleSum z = 0) :
    HasWinding
      ((d39TrianglePolyline r u v).toPath.cast rfl
        (d39TrianglePolyline_closed r u v)) z 0 := by
  exact (hasWinding_iff_angleSum_eq_int (d39TrianglePolyline r u v)
    (d39TrianglePolyline_closed r u v) z 0 hz).2 (by simpa using hsum)

















































































end DirectedDistances.PlanarMap

end
