/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39RadialOrder11

/-! # Base angle helpers toward Proposition 5.16 -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16: among three distinct real angles in one
turn, there is a base angle strictly inside a gap between consecutive
directions. -/
theorem d39_three_distinct_angles_have_base_gap
    (a b c : ℝ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : -Real.pi < a ∧ a ≤ Real.pi)
    (hb : -Real.pi < b ∧ b ≤ Real.pi)
    (hc : -Real.pi < c ∧ c ≤ Real.pi) :
    ∃ α : ℝ, a ≠ α ∧ b ≠ α ∧ c ≠ α ∧ -Real.pi < α ∧ α < Real.pi := by
  rcases lt_or_gt_of_ne hab with hablt | hblt
  · by_cases hca : c < a
    · refine ⟨(c + a) / 2, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
    · have haclt : a < c := by
        rcases lt_or_eq_of_le (le_of_not_gt hca) with h | h
        · exact h
        · exact False.elim (hac h)
      by_cases hcb : c < b
      · refine ⟨(a + c) / 2, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
      · have hbclt : b < c := by
          rcases lt_or_eq_of_le (le_of_not_gt hcb) with h | h
          · exact h
          · exact False.elim (hbc h)
        refine ⟨(a + b) / 2, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  · by_cases hcb : c < b
    · refine ⟨(c + b) / 2, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
    · have hbclt : b < c := by
        rcases lt_or_eq_of_le (le_of_not_gt hcb) with h | h
        · exact h
        · exact False.elim (hbc h)
      by_cases hca : c < a
      · refine ⟨(b + c) / 2, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
      · have haclt : a < c := by
          rcases lt_or_eq_of_le (le_of_not_gt hca) with h | h
          · exact h
          · exact False.elim (hac h)
        refine ⟨(b + a) / 2, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Helper toward Proposition 5.16: one can choose the rotated-circle base
angle away from three distinct nonzero rays, so all three ray hit times are
strictly between zero and one. -/
theorem d39_exists_base_angle_with_three_interior_ray_hits
    (u v w : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : u.arg ≠ v.arg) (huw : u.arg ≠ w.arg)
    (hvw : v.arg ≠ w.arg) :
    ∃ α : ℝ,
      (∀ k : ℤ, u.arg ≠ α + 2 * Real.pi * (k : ℝ)) ∧
      (∀ k : ℤ, v.arg ≠ α + 2 * Real.pi * (k : ℝ)) ∧
      (∀ k : ℤ, w.arg ≠ α + 2 * Real.pi * (k : ℝ)) ∧
      d39RotatedCircleRayHitTime α u ∈ Set.Ioo 0 1 ∧
      d39RotatedCircleRayHitTime α v ∈ Set.Ioo 0 1 ∧
      d39RotatedCircleRayHitTime α w ∈ Set.Ioo 0 1 := by
  have huarg := Complex.arg_mem_Ioc u
  have hvarg := Complex.arg_mem_Ioc v
  have hwarg := Complex.arg_mem_Ioc w
  change -Real.pi < u.arg ∧ u.arg ≤ Real.pi at huarg
  change -Real.pi < v.arg ∧ v.arg ≤ Real.pi at hvarg
  change -Real.pi < w.arg ∧ w.arg ≤ Real.pi at hwarg
  obtain ⟨α, huα, hvα, hwα, hαlo, hαhi⟩ :=
    d39_three_distinct_angles_have_base_gap u.arg v.arg w.arg
      huv huw hvw huarg hvarg hwarg
  have hperiod : 0 < 2 * Real.pi := by positivity
  have hmiss (a : ℂ) (ha : -Real.pi < a.arg ∧ a.arg ≤ Real.pi)
      (haα : a.arg ≠ α) : ∀ k : ℤ, a.arg ≠ α + 2 * Real.pi * (k : ℝ) := by
    intro k h
    have hdifflo : -(2 * Real.pi) < a.arg - α := by linarith [ha.1, hαhi]
    have hdiffhi : a.arg - α < 2 * Real.pi := by linarith [ha.2, hαlo]
    have hklo : (-1 : ℝ) < (k : ℝ) := by nlinarith [h, hdifflo, hperiod]
    have hkhi : (k : ℝ) < 1 := by nlinarith [h, hdiffhi, hperiod]
    have hklo' : (-1 : ℤ) < k := by exact_mod_cast hklo
    have hkhi' : k < (1 : ℤ) := by exact_mod_cast hkhi
    have hk : k = 0 := by omega
    apply haα
    rw [h, hk]
    ring
  have hmissU := hmiss u huarg huα
  have hmissV := hmiss v hvarg hvα
  have hmissW := hmiss w hwarg hwα
  refine ⟨α, hmissU, hmissV, hmissW, ?_, ?_, ?_⟩
  · exact d39_rotatedCircleRayHitTime_mem_Ioo α u hu hmissU
  · exact d39_rotatedCircleRayHitTime_mem_Ioo α v hv hmissV
  · exact d39_rotatedCircleRayHitTime_mem_Ioo α w hw hmissW

/-- Helper toward Proposition 5.16: if the circle's base angle is not a
translate of a ray argument, its base point avoids that positive ray. -/
theorem d39_rotatedCirclePath_basepoint_avoids_positive_ray
    (ρ α : ℝ) (a : ℂ) (hρ : 0 < ρ) (ha : a ≠ 0)
    (hmiss : ∀ k : ℤ, a.arg ≠ α + 2 * Real.pi * (k : ℝ)) :
    d39RotatedCirclePath ρ α (0 : unitInterval) ∉
      {z : ℂ | ∃ r : ℝ, 0 ≤ r ∧ z = (r : ℂ) * a} := by
  intro hray
  rcases hray with ⟨r, hr, hpoint⟩
  have hpoint' : (ρ : ℂ) * Complex.exp ((α : ℂ) * Complex.I) =
      (r : ℂ) * a := by
    simpa [d39RotatedCirclePath] using hpoint
  have hrad : ρ = r * ‖a‖ := by
    calc
      ρ = ‖d39RotatedCirclePath ρ α (0 : unitInterval)‖ :=
        (d39_rotatedCirclePath_norm hρ _).symm
      _ = ‖(r : ℂ) * a‖ := congrArg norm hpoint
      _ = r * ‖a‖ := by
        rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hr]
  have hrpos : 0 < r := by
    by_contra hnot
    have hrzero : r = 0 := le_antisymm (le_of_not_gt hnot) hr
    rw [hrzero] at hrad
    have hρzero : ρ = 0 := by simpa using hrad
    exact (ne_of_gt hρ) hρzero
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hρ)
  have hrs : r = ρ * (r / ρ) := by
    field_simp [ne_of_gt hρ]
  have hscalar : (r : ℂ) = (ρ : ℂ) * ((r / ρ : ℝ) : ℂ) := by
    exact_mod_cast hrs
  have hscaled : (ρ : ℂ) * Complex.exp ((α : ℂ) * Complex.I) =
      (ρ : ℂ) * (((r / ρ : ℝ) : ℂ) * a) := by
    calc
      (ρ : ℂ) * Complex.exp ((α : ℂ) * Complex.I) = (r : ℂ) * a := hpoint'
      _ = ((ρ : ℂ) * ((r / ρ : ℝ) : ℂ)) * a := by rw [hscalar]
      _ = (ρ : ℂ) * (((r / ρ : ℝ) : ℂ) * a) := by ring
  have hphase : Complex.exp ((α : ℂ) * Complex.I) =
      ((r / ρ : ℝ) : ℂ) * a := mul_left_cancel₀ hρC hscaled
  obtain ⟨k, harg⟩ := d39_exp_positive_ray_argument_lift
    ((α : ℂ) * Complex.I) a (r / ρ) ha (div_pos hrpos hρ) hphase
  have hangle : α = a.arg + 2 * Real.pi * (k : ℝ) := by
    simpa using harg
  have hbad : a.arg = α + 2 * Real.pi * ((-k : ℤ) : ℝ) := by
    rw [hangle]
    push_cast
    ring
  exact hmiss (-k) hbad

/-- Helper toward Proposition 5.16: the rotated circle's two endpoint
parameters avoid a positive ray whenever its base angle avoids that ray. -/
theorem d39_rotatedCirclePath_endpoints_avoid_positive_ray
    (ρ α : ℝ) (a : ℂ) (hρ : 0 < ρ) (ha : a ≠ 0)
    (hmiss : ∀ k : ℤ, a.arg ≠ α + 2 * Real.pi * (k : ℝ)) :
    d39RotatedCirclePath ρ α (0 : unitInterval) ∉
        {z : ℂ | ∃ r : ℝ, 0 ≤ r ∧ z = (r : ℂ) * a} ∧
      d39RotatedCirclePath ρ α (1 : unitInterval) ∉
        {z : ℂ | ∃ r : ℝ, 0 ≤ r ∧ z = (r : ℂ) * a} := by
  have hbase := d39_rotatedCirclePath_basepoint_avoids_positive_ray
    ρ α a hρ ha hmiss
  have hend : d39RotatedCirclePath ρ α (1 : unitInterval) =
      d39RotatedCirclePath ρ α (0 : unitInterval) := by
    exact (d39RotatedCirclePath ρ α).target'.trans
      (d39RotatedCirclePath ρ α).source'.symm
  exact ⟨hbase, by rw [hend]; exact hbase⟩

/-- Helper toward Proposition 5.16: at both endpoint parameters, the image
circle avoids an image germ when the chosen base angle avoids its source ray. -/
theorem d39_imageRotatedCirclePath_endpoints_avoid_image_germ
    (K : ℂ ≃ₜ ℂ) (u u' : ℂ) (r s ρ α : ℝ)
    (hu : u ≠ 0) (hρ : 0 < ρ)
    (himage : K '' {z : ℂ | ∃ q : ℝ, 0 ≤ q ∧ q ≤ r ∧
        z = (q : ℂ) * u} =
      {z : ℂ | ∃ q : ℝ, 0 ≤ q ∧ q ≤ s ∧ z = (q : ℂ) * u'})
    (hmiss : ∀ k : ℤ, u.arg ≠ α + 2 * Real.pi * (k : ℝ)) :
    ∀ t : unitInterval, (t = 0 ∨ t = 1) →
      ((d39RotatedCirclePath ρ α).map K.continuous) t ∉
        {z : ℂ | ∃ q : ℝ, 0 ≤ q ∧ q ≤ s ∧ z = (q : ℂ) * u'} := by
  have hsource := d39_rotatedCirclePath_endpoints_avoid_positive_ray
    ρ α u hρ hu hmiss
  intro t ht
  rcases ht with ht | ht
  · subst t
    intro himagePoint
    rw [← himage] at himagePoint
    rcases himagePoint with ⟨z, hz, hzpoint⟩
    change K z = K (d39RotatedCirclePath ρ α (0 : unitInterval)) at hzpoint
    have hzpath : z = d39RotatedCirclePath ρ α (0 : unitInterval) :=
      K.injective hzpoint
    rcases hz with ⟨q, hq0, hqr, hqpoint⟩
    apply hsource.1
    refine ⟨q, hq0, ?_⟩
    calc
      d39RotatedCirclePath ρ α (0 : unitInterval) = z := hzpath.symm
      _ = (q : ℂ) * u := hqpoint
  · subst t
    intro himagePoint
    rw [← himage] at himagePoint
    rcases himagePoint with ⟨z, hz, hzpoint⟩
    change K z = K (d39RotatedCirclePath ρ α (1 : unitInterval)) at hzpoint
    have hzpath : z = d39RotatedCirclePath ρ α (1 : unitInterval) :=
      K.injective hzpoint
    rcases hz with ⟨q, hq0, hqr, hqpoint⟩
    apply hsource.2
    refine ⟨q, hq0, ?_⟩
    calc
      d39RotatedCirclePath ρ α (1 : unitInterval) = z := hzpath.symm
      _ = (q : ℂ) * u := hqpoint

/-- Helper toward Proposition 5.16: a winding-one lift gives a total
increment of `2π` for the three cyclic intervals cut at any three parameters. -/
theorem d39_winding_one_cyclic_increment_sum
    {z w : ℂ} {L : Path z z} (hwind : HasWinding L w 1)
    (t₁ t₂ t₃ : unitInterval) :
    ∃ φ : C(unitInterval, ℂ),
      (∀ t, Complex.exp (φ t) = L t - w) ∧
        ((φ t₂).im - (φ t₁).im) +
          ((φ t₃).im - (φ t₂).im) +
          ((φ t₁).im + 2 * Real.pi - (φ t₃).im) = 2 * Real.pi := by
  obtain ⟨φ, hφ, hinc⟩ := d39_hasWinding_one_lift_imaginary_increment hwind
  refine ⟨φ, hφ, ?_⟩
  linarith [hinc]

/-- Helper toward Proposition 5.16: if one lifted endpoint gains `2π`,
open strips on the two pieces adjacent to the base point have indices shifted
by one. -/
theorem d39_endpoint_argument_strips_shift_by_one
    (g x₀ x₁ : ℝ) (k₀ k₁ : ℤ)
    (hperiod : 0 < 2 * Real.pi) (hwind : x₁ = x₀ + 2 * Real.pi)
    (hstrip₀ : g + 2 * Real.pi * (k₀ : ℝ) < x₀ ∧
      x₀ < g + 2 * Real.pi * ((k₀ + 1 : ℤ) : ℝ))
    (hstrip₁ : g + 2 * Real.pi * (k₁ : ℝ) < x₁ ∧
      x₁ < g + 2 * Real.pi * ((k₁ + 1 : ℤ) : ℝ)) :
    k₁ = k₀ + 1 := by
  have hstrip₁' := hstrip₁
  rw [hwind] at hstrip₁'
  push_cast at hstrip₁'
  ring_nf at hstrip₁'
  have hprodlo : 2 * Real.pi * (k₀ : ℝ) < 2 * Real.pi * (k₁ : ℝ) := by
    linarith [hstrip₀.1, hstrip₁'.2]
  have hklo : k₀ < k₁ := by
    by_contra hnot
    have hcast : (k₁ : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast (le_of_not_gt hnot)
    have hmul := mul_le_mul_of_nonneg_left hcast hperiod.le
    linarith [hprodlo]
  have hprodhi : 2 * Real.pi * ((k₁ - 1 : ℤ) : ℝ) <
      2 * Real.pi * ((k₀ + 1 : ℤ) : ℝ) := by
    have hleft : g + 2 * Real.pi * ((k₁ - 1 : ℤ) : ℝ) < x₀ := by
      calc
        g + 2 * Real.pi * ((k₁ - 1 : ℤ) : ℝ) =
            g + 2 * Real.pi * (k₁ : ℝ) - 2 * Real.pi := by
              push_cast
              ring
        _ < x₀ + 2 * Real.pi - 2 * Real.pi := by linarith [hstrip₁'.1]
        _ = x₀ := by ring
    have hright : x₀ < g + 2 * Real.pi * ((k₀ + 1 : ℤ) : ℝ) := hstrip₀.2
    linarith
  have hkhi : k₁ < k₀ + 2 := by
    by_contra hnot
    have hcast : (k₀ : ℝ) + 2 ≤ (k₁ : ℝ) := by exact_mod_cast (le_of_not_gt hnot)
    have hmul := mul_le_mul_of_nonneg_left hcast hperiod.le
    have hmul' : 2 * Real.pi * ((k₀ + 1 : ℤ) : ℝ) ≤
        2 * Real.pi * ((k₁ - 1 : ℤ) : ℝ) := by
      push_cast at hmul ⊢
      ring_nf at hmul ⊢
      linarith
    linarith [hprodhi]
  omega

/-- Helper toward Proposition 5.16: strips on the two sides of the base
point combine to give the branch fact for the wrap-around increment. -/
theorem d39_wraparound_branch_iff_third_ray_between_of_split_strips
    (u v w : ℂ) (base₀ base₁ first third g : ℝ) (k₀ k₁ : ℤ)
    (huv : u.arg ≠ v.arg) (huw : u.arg ≠ w.arg)
    (hvw : v.arg ≠ w.arg)
    (hwind : base₁ = base₀ + 2 * Real.pi)
    (hbase₀ : g + 2 * Real.pi * (k₀ : ℝ) < base₀ ∧
      base₀ < g + 2 * Real.pi * ((k₀ + 1 : ℤ) : ℝ))
    (hbase₁ : g + 2 * Real.pi * (k₁ : ℝ) < base₁ ∧
      base₁ < g + 2 * Real.pi * ((k₁ + 1 : ℤ) : ℝ))
    (hfirst : g + 2 * Real.pi * (k₀ : ℝ) < first ∧
      first < g + 2 * Real.pi * ((k₀ + 1 : ℤ) : ℝ))
    (hthird : g + 2 * Real.pi * (k₁ : ℝ) < third ∧
      third < g + 2 * Real.pi * ((k₁ + 1 : ℤ) : ℝ))
    (hfirstLift : ∃ n : ℤ, first = u.arg + 2 * Real.pi * (n : ℝ))
    (hthirdLift : ∃ n : ℤ, third = w.arg + 2 * Real.pi * (n : ℝ))
    (hgLift : ∃ n : ℤ, g = v.arg + 2 * Real.pi * (n : ℝ)) :
    first + 2 * Real.pi - third = ccwTurn w u - 2 * Real.pi ↔
      ccwTurn w v < ccwTurn w u := by
  have hperiod : 0 < 2 * Real.pi := by positivity
  have hk : k₁ = k₀ + 1 :=
    d39_endpoint_argument_strips_shift_by_one g base₀ base₁ k₀ k₁
      hperiod hwind hbase₀ hbase₁
  have hfirstNorm := hfirst
  push_cast at hfirstNorm
  ring_nf at hfirstNorm
  have hfirstShift : g + 2 * Real.pi * (k₁ : ℝ) < first + 2 * Real.pi ∧
      first + 2 * Real.pi < g + 2 * Real.pi * (k₁ : ℝ) + 2 * Real.pi := by
    rw [hk]
    constructor
    · push_cast
      ring_nf
      linarith [hfirstNorm.1]
    · push_cast
      ring_nf
      linarith [hfirstNorm.2, hperiod]
  have hthird' : g + 2 * Real.pi * (k₁ : ℝ) < third ∧
      third < g + 2 * Real.pi * (k₁ : ℝ) + 2 * Real.pi := by
    constructor
    · exact hthird.1
    · have := hthird.2
      push_cast at this
      ring_nf at this ⊢
      exact this
  have hgLift' : ∃ m : ℤ,
      g + 2 * Real.pi * (k₁ : ℝ) = v.arg + 2 * Real.pi * (m : ℝ) := by
    rcases hgLift with ⟨n, hn⟩
    refine ⟨n + k₁, ?_⟩
    rw [hn]
    push_cast
    ring
  have hfirstLift' : ∃ m : ℤ,
      first + 2 * Real.pi = u.arg + 2 * Real.pi * (m : ℝ) := by
    rcases hfirstLift with ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    rw [hn]
    push_cast
    ring
  exact d39_same_strip_clockwise_branch_iff_third_ray_between
    w u v third (first + 2 * Real.pi) (g + 2 * Real.pi * (k₁ : ℝ))
    (Ne.symm huw) (Ne.symm hvw) huv hthird' hfirstShift hthirdLift
    hfirstLift' hgLift'





























end DirectedDistances.PlanarMap

end
