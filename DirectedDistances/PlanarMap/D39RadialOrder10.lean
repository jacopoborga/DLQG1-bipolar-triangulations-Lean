/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39RadialOrder9

/-! # Rotated circle order helpers toward Proposition 5.16 -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16: the angle of each open-turn ray hit is a
representative of the ray argument modulo `2π`. -/
theorem d39_rotatedCircleRayHitTime_angle_lift
    (α : ℝ) (a : ℂ)
    (hmiss : ∀ j : ℤ, a.arg ≠ α + 2 * Real.pi * (j : ℝ)) :
    ∃ k : ℤ,
      α + 2 * Real.pi * d39RotatedCircleRayHitTime α a =
        a.arg + 2 * Real.pi * (k : ℝ) := by
  have hperiod : 0 < 2 * Real.pi := by positivity
  let x := (α - a.arg) / (2 * Real.pi)
  let k : ℤ := ⌊x⌋ + 1
  have hlow : α < a.arg + 2 * Real.pi * (k : ℝ) := by
    have hfloor := Int.lt_floor_add_one x
    have hmul := (div_lt_iff₀ hperiod).mp hfloor
    dsimp [k, x]
    push_cast at hmul ⊢
    nlinarith
  have hupperle : a.arg + 2 * Real.pi * (k : ℝ) ≤ α + 2 * Real.pi := by
    have hfloor := Int.floor_le x
    have hmul := (le_div_iff₀ hperiod).mp hfloor
    dsimp [k, x]
    push_cast at hmul ⊢
    nlinarith
  have hupper : a.arg + 2 * Real.pi * (k : ℝ) < α + 2 * Real.pi := by
    by_contra hnot
    have heq : a.arg + 2 * Real.pi * (k : ℝ) = α + 2 * Real.pi :=
      le_antisymm hupperle (le_of_not_gt hnot)
    have hbad : a.arg = α + 2 * Real.pi * ((-⌊x⌋ : ℤ) : ℝ) := by
      dsimp [k] at heq
      push_cast at heq ⊢
      nlinarith
    exact hmiss (-⌊x⌋) hbad
  have hhit := d39_rotatedCircleRayHitTime_eq_of_lift α a k hlow hupper
  refine ⟨k, ?_⟩
  calc
    α + 2 * Real.pi * d39RotatedCircleRayHitTime α a =
        α + 2 * Real.pi *
          ((a.arg + 2 * Real.pi * (k : ℝ) - α) / (2 * Real.pi)) :=
        congrArg (fun t : ℝ => α + 2 * Real.pi * t) hhit
    _ = a.arg + 2 * Real.pi * (k : ℝ) := by
      field_simp [ne_of_gt hperiod]
      ring

/-- Helper toward Proposition 5.16: when one ray is hit before another in a
single turn, the positive angular increment between their hit lifts is the
counterclockwise turn between the rays. -/
theorem d39_rotatedCircleHitTime_increment_eq_ccwTurn_of_lt
    (α : ℝ) (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : u.arg ≠ v.arg)
    (hmissU : ∀ k : ℤ, u.arg ≠ α + 2 * Real.pi * (k : ℝ))
    (hmissV : ∀ k : ℤ, v.arg ≠ α + 2 * Real.pi * (k : ℝ))
    (ht : d39RotatedCircleRayHitTime α u <
      d39RotatedCircleRayHitTime α v) :
    2 * Real.pi *
      (d39RotatedCircleRayHitTime α v - d39RotatedCircleRayHitTime α u) =
        ccwTurn u v := by
  obtain ⟨ku, hku⟩ := d39_rotatedCircleRayHitTime_angle_lift α u hmissU
  obtain ⟨kv, hkv⟩ := d39_rotatedCircleRayHitTime_angle_lift α v hmissV
  let x := α + 2 * Real.pi * d39RotatedCircleRayHitTime α u
  let y := α + 2 * Real.pi * d39RotatedCircleRayHitTime α v
  have hcongr : ∃ k : ℤ,
      y - x = v.arg - u.arg + 2 * Real.pi * (k : ℝ) := by
    refine ⟨kv - ku, ?_⟩
    dsimp [x, y]
    rw [hku, hkv]
    push_cast
    ring
  have huIoo := d39_rotatedCircleRayHitTime_mem_Ioo α u hu hmissU
  have hvIoo := d39_rotatedCircleRayHitTime_mem_Ioo α v hv hmissV
  have hperiod : 0 < 2 * Real.pi := by positivity
  have hdiff : -1 <
      d39RotatedCircleRayHitTime α v - d39RotatedCircleRayHitTime α u ∧
      d39RotatedCircleRayHitTime α v - d39RotatedCircleRayHitTime α u < 1 := by
    constructor
    · linarith [huIoo.2, hvIoo.1]
    · linarith [huIoo.1, hvIoo.2]
  have hstep : y - x = 2 * Real.pi *
      (d39RotatedCircleRayHitTime α v - d39RotatedCircleRayHitTime α u) := by
    dsimp [x, y]
    ring
  have hscaledLow := mul_lt_mul_of_pos_left hdiff.1 hperiod
  have hscaledHigh := mul_lt_mul_of_pos_left hdiff.2 hperiod
  have hbound : -(2 * Real.pi) < y - x ∧ y - x < 2 * Real.pi := by
    rw [hstep]
    constructor <;> nlinarith [hscaledLow, hscaledHigh]
  have hbranches := d39_lifted_angle_increment_has_two_turn_branches
    u v x y huv hcongr hbound
  have hpos : 0 < y - x := by
    rw [hstep]
    exact mul_pos hperiod (sub_pos.mpr ht)
  rcases hbranches with hbranch | hbranch
  · calc
      2 * Real.pi *
          (d39RotatedCircleRayHitTime α v - d39RotatedCircleRayHitTime α u) =
          y - x := hstep.symm
      _ = ccwTurn u v := hbranch
  · have hturn := d39_ccwTurn_lt_two_pi huv
    have hneg : y - x < 0 := by rw [hbranch]; linarith
    linarith

/-- Helper toward Proposition 5.16: a continuous angle avoiding one ray's
argument lattice on a closed parameter interval stays in a single open strip
on that interval. -/
theorem d39_continuous_angle_segment_avoids_lattice_stays_in_strip
    (θ : C(unitInterval, ℝ)) (a b cut : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (havoid : ∀ t : unitInterval, a ≤ (t : ℝ) → (t : ℝ) ≤ b →
      ∀ k : ℤ, θ t ≠ cut + 2 * Real.pi * (k : ℝ)) :
    ∃ k : ℤ, ∀ s : unitInterval,
      cut + 2 * Real.pi * (k : ℝ) <
          θ ⟨a + (b - a) * (s : ℝ), by
            have hmul := mul_nonneg (sub_nonneg.mpr hab) s.property.1
            nlinarith,
            by
              have hmul := mul_le_mul_of_nonneg_left s.property.2
                (sub_nonneg.mpr hab)
              nlinarith⟩ ∧
        θ ⟨a + (b - a) * (s : ℝ), by
            have hmul := mul_nonneg (sub_nonneg.mpr hab) s.property.1
            nlinarith,
            by
              have hmul := mul_le_mul_of_nonneg_left s.property.2
                (sub_nonneg.mpr hab)
              nlinarith⟩ <
          cut + 2 * Real.pi * ((k + 1 : ℤ) : ℝ) := by
  let q : C(unitInterval, unitInterval) :=
    ⟨fun s => ⟨a + (b - a) * (s : ℝ), by
        have hmul := mul_nonneg (sub_nonneg.mpr hab) s.property.1
        nlinarith,
      by
        have hmul := mul_le_mul_of_nonneg_left s.property.2
          (sub_nonneg.mpr hab)
        nlinarith⟩, by continuity⟩
  have hqlo (s : unitInterval) : a ≤ (q s : ℝ) := by
    dsimp [q]
    have hmul := mul_nonneg (sub_nonneg.mpr hab) s.property.1
    nlinarith
  have hqhi (s : unitInterval) : (q s : ℝ) ≤ b := by
    dsimp [q]
    have hmul := mul_le_mul_of_nonneg_left s.property.2
      (sub_nonneg.mpr hab)
    nlinarith
  have havoidSeg : ∀ s : unitInterval, ∀ k : ℤ,
      θ (q s) ≠ cut + 2 * Real.pi * (k : ℝ) := by
    intro s k
    exact havoid (q s) (hqlo s) (hqhi s) k
  obtain ⟨k, hk⟩ := d39_continuous_angle_avoids_lattice_stays_in_strip
    (fun s => θ (q s)) (θ.continuous.comp q.continuous) cut havoidSeg
  refine ⟨k, ?_⟩
  intro s
  simpa [q] using hk s

/-- Helper toward Proposition 5.16: when two lifted directions lie in the
same strip cut by a third direction, the clockwise increment branch is chosen
exactly when the third direction lies between the first two. -/
theorem d39_same_strip_clockwise_branch_iff_third_ray_between
    (u v w : ℂ) (x y g : ℝ)
    (huv : u.arg ≠ v.arg) (huw : u.arg ≠ w.arg) (hvw : v.arg ≠ w.arg)
    (hxstrip : g < x ∧ x < g + 2 * Real.pi)
    (hystrip : g < y ∧ y < g + 2 * Real.pi)
    (hx : ∃ m : ℤ, x = u.arg + 2 * Real.pi * (m : ℝ))
    (hy : ∃ n : ℤ, y = v.arg + 2 * Real.pi * (n : ℝ))
    (hg : ∃ k : ℤ, g = w.arg + 2 * Real.pi * (k : ℝ)) :
    y - x = ccwTurn u v - 2 * Real.pi ↔
      ccwTurn u w < ccwTurn u v := by
  have hxw : x - g = ccwTurn w u := by
    rcases hx with ⟨m, hm⟩
    rcases hg with ⟨k, hk⟩
    have hcongr : ∃ j : ℤ,
        x - g = u.arg - w.arg + 2 * Real.pi * (j : ℝ) := by
      refine ⟨m - k, ?_⟩
      rw [hm, hk]
      push_cast
      ring
    have hbound : -(2 * Real.pi) < x - g ∧ x - g < 2 * Real.pi := by
      constructor <;> linarith [hxstrip.1, hxstrip.2]
    rcases d39_lifted_angle_increment_has_two_turn_branches
        w u g x (Ne.symm huw) hcongr hbound with h | h
    · exact h
    · have hturn := d39_ccwTurn_lt_two_pi (u := w) (v := u) (Ne.symm huw)
      have hpos : 0 < x - g := by linarith [hxstrip.1]
      have hneg : x - g < 0 := by rw [h]; linarith
      linarith
  have hyw : y - g = ccwTurn w v := by
    rcases hy with ⟨n, hn⟩
    rcases hg with ⟨k, hk⟩
    have hcongr : ∃ j : ℤ,
        y - g = v.arg - w.arg + 2 * Real.pi * (j : ℝ) := by
      refine ⟨n - k, ?_⟩
      rw [hn, hk]
      push_cast
      ring
    have hbound : -(2 * Real.pi) < y - g ∧ y - g < 2 * Real.pi := by
      constructor <;> linarith [hystrip.1, hystrip.2]
    rcases d39_lifted_angle_increment_has_two_turn_branches
        w v g y (Ne.symm hvw) hcongr hbound with h | h
    · exact h
    · have hturn := d39_ccwTurn_lt_two_pi (u := w) (v := v) (Ne.symm hvw)
      have hpos : 0 < y - g := by linarith [hystrip.1]
      have hneg : y - g < 0 := by rw [h]; linarith
      linarith
  have hbetween := d39_between_cyclic
    (u := w) (v := u) (w := v) (Ne.symm huw) huv hvw
  have hbranches := d39_same_strip_increment_has_two_turn_branches
    u v x y g huv hxstrip hystrip hx hy
  constructor
  · intro hbranch
    have hyltx : y < x := by
      have hturn := d39_ccwTurn_lt_two_pi huv
      linarith
    have hsector : ccwTurn w v < ccwTurn w u := by
      rw [← hyw, ← hxw]
      linarith
    exact hbetween.mp hsector
  · intro hsector
    have hyltx : y < x := by
      calc
        y = (y - g) + g := by ring
        _ < (x - g) + g := by
          rw [hyw, hxw]
          exact add_lt_add_left (hbetween.mpr hsector) g
        _ = x := by ring
    rcases hbranches with hbranch | hbranch
    · have hpos : 0 < y - x := by rw [hbranch]; exact ccwTurn_pos u v
      linarith
    · exact hbranch

/-- Helper toward Proposition 5.16: at an interior parameter, the image loop
misses an image germ exactly when the source circle has not reached its
corresponding ray hit time. -/
theorem d39_imageRotatedCirclePath_avoids_image_germ_iff_not_hit_time
    (K : ℂ ≃ₜ ℂ) (u u' : ℂ) (r s ρ α : ℝ)
    (hu : u ≠ 0) (hu' : u' ≠ 0) (hρ : 0 < ρ) (hρr : ρ < r * ‖u‖)
    (himage : K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧
        z = (t : ℂ) * u} =
      {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * u'})
    (hmiss : ∀ k : ℤ, u.arg ≠ α + 2 * Real.pi * (k : ℝ))
    (t : unitInterval) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    (((d39RotatedCirclePath ρ α).map K.continuous) t ∉
      {z : ℂ | ∃ q : ℝ, 0 ≤ q ∧ q ≤ s ∧ z = (q : ℂ) * u'}) ↔
        (t : ℝ) ≠ d39RotatedCircleRayHitTime α u := by
  have hiff := d39_imageRotatedCirclePath_image_germ_hit_iff
    K u u' r s ρ α hu hu' hρ hρr himage hmiss t ht0 ht1
  exact not_congr hiff

/-- Helper toward Proposition 5.16: a loop lift witnessing winding one has
imaginary endpoint increment `2π`. -/
theorem d39_hasWinding_one_lift_imaginary_increment
    {z w : ℂ} {L : Path z z} (hwind : HasWinding L w 1) :
    ∃ φ : C(unitInterval, ℂ),
      (∀ t, Complex.exp (φ t) = L t - w) ∧
        (φ 1).im - (φ 0).im = 2 * Real.pi := by
  rcases hwind with ⟨φ, hφ, hend⟩
  refine ⟨φ, hφ, ?_⟩
  have him := congrArg Complex.im hend
  simpa using him





















































end DirectedDistances.PlanarMap

end
