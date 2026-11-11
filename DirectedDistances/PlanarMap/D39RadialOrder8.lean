/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39RadialOrder7

/-! # Argument strips toward Proposition 5.16

Helper toward Proposition 5.16. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16: if the imaginary part of a logarithm
differs from a nonzero ray's argument by an integer multiple of `2π`, then its
exponential lies on that positive ray. -/
theorem d39_exp_argument_congruent_to_ray_lies_on_ray
    (z u : ℂ) (hu : u ≠ 0) (k : ℤ)
    (harg : z.im = u.arg + 2 * Real.pi * (k : ℝ)) :
    ∃ r : ℝ, 0 < r ∧ Complex.exp z = (r : ℂ) * u := by
  have hz : z = (z.re : ℂ) + (u.arg : ℂ) * Complex.I +
      (k : ℂ) * (2 * Real.pi * Complex.I) := by
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re]
    · simp [Complex.add_im, Complex.mul_im, harg]
      ring_nf
  have hexp := (Complex.exp_eq_exp_iff_exists_int).2 ⟨k, hz⟩
  have hnorm : (‖u‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_pos_iff.mpr hu).ne'
  have hpolar : (‖u‖ : ℂ) *
      Complex.exp ((u.arg : ℂ) * Complex.I) = u :=
    Complex.norm_mul_exp_arg_mul_I u
  refine ⟨Real.exp z.re / ‖u‖,
    div_pos (Real.exp_pos _) (norm_pos_iff.mpr hu), ?_⟩
  calc
    Complex.exp z = Complex.exp (z.re : ℂ) *
        Complex.exp ((u.arg : ℂ) * Complex.I) := by
      rw [hexp, Complex.exp_add]
    _ = (Real.exp z.re / ‖u‖ : ℝ) * u := by
      calc
        _ = (Real.exp z.re / ‖u‖ : ℝ) *
            ((‖u‖ : ℂ) * Complex.exp ((u.arg : ℂ) * Complex.I)) := by
          push_cast
          field_simp [hnorm]
        _ = (Real.exp z.re / ‖u‖ : ℝ) * u := by rw [hpolar]

/-- Helper toward Proposition 5.16: if a continuous logarithm lift avoids a
positive ray, its imaginary part avoids every translate of that ray's
argument by an integer multiple of `2π`. -/
theorem d39_logarithm_lift_avoids_ray_argument_lattice
    {z w u : ℂ} (L : Path z z) (φ : C(unitInterval, ℂ)) (hu : u ≠ 0)
    (hφ : ∀ t, Complex.exp (φ t) = L t - w)
    (hray : ∀ t, L t - w ∉
      {q : ℂ | ∃ r : ℝ, 0 ≤ r ∧ q = (r : ℂ) * u}) :
    ∀ t, ∀ k : ℤ, (φ t).im ≠ u.arg + 2 * Real.pi * k := by
  intro t k hangle
  obtain ⟨r, hr, hexp⟩ :=
    d39_exp_argument_congruent_to_ray_lies_on_ray (φ t) u hu k hangle
  apply hray t
  refine ⟨r, hr.le, ?_⟩
  calc
    L t - w = Complex.exp (φ t) := (hφ t).symm
    _ = (r : ℂ) * u := hexp

/-- Helper toward Proposition 5.16: a continuous real angle that avoids every
translate of one ray angle by an integer multiple of `2π` stays in one open
strip between consecutive such translates on the whole parameter interval. -/
theorem d39_continuous_angle_avoids_lattice_stays_in_strip
    (θ : unitInterval → ℝ) (hθ : Continuous θ) (a : ℝ)
    (havoid : ∀ t, ∀ k : ℤ, θ t ≠ a + 2 * Real.pi * k) :
    ∃ k : ℤ, ∀ t,
      a + 2 * Real.pi * k < θ t ∧
        θ t < a + 2 * Real.pi * (k + 1) := by
  let k : ℤ := ⌊(θ 0 - a) / (2 * Real.pi)⌋
  have hperiod : 0 < 2 * Real.pi := by positivity
  have hklo : (k : ℝ) ≤ (θ 0 - a) / (2 * Real.pi) := by
    dsimp [k]
    exact Int.floor_le _
  have hkhi : (θ 0 - a) / (2 * Real.pi) < (k : ℝ) + 1 := by
    dsimp [k]
    exact Int.lt_floor_add_one _
  have h0lo : a + 2 * Real.pi * (k : ℝ) ≤ θ 0 := by
    have hmul := (le_div_iff₀ hperiod).mp hklo
    nlinarith
  have h0hi : θ 0 < a + 2 * Real.pi * ((k : ℝ) + 1) := by
    have hmul := (div_lt_iff₀ hperiod).mp hkhi
    nlinarith
  have h0lo' : a + 2 * Real.pi * (k : ℝ) < θ 0 := by
    by_contra hnot
    have heq : θ 0 = a + 2 * Real.pi * (k : ℝ) :=
      le_antisymm (le_of_not_gt hnot) h0lo
    exact havoid 0 k heq
  have h0hi' : θ 0 < a + 2 * Real.pi * ((k : ℝ) + 1) := h0hi
  refine ⟨k, ?_⟩
  intro t
  constructor
  · by_contra hnot
    have hval : a + 2 * Real.pi * (k : ℝ) ∈
        Set.Icc (θ t) (θ 0) := ⟨le_of_not_gt hnot, h0lo'.le⟩
    have himage : a + 2 * Real.pi * (k : ℝ) ∈ Set.range θ :=
      (intermediate_value_univ t 0 hθ) hval
    rcases himage with ⟨s, hθs⟩
    exact havoid s k hθs
  · by_contra hnot
    have hval : a + 2 * Real.pi * ((k : ℝ) + 1) ∈
        Set.Icc (θ 0) (θ t) := ⟨h0hi'.le, le_of_not_gt hnot⟩
    have himage : a + 2 * Real.pi * ((k : ℝ) + 1) ∈ Set.range θ :=
      (intermediate_value_univ 0 t hθ) hval
    rcases himage with ⟨s, hθs⟩
    have heq : θ s = a + 2 * Real.pi * (((k + 1 : ℤ) : ℝ)) := by
      simpa only [Int.cast_add, Int.cast_one] using hθs
    exact havoid s (k + 1) heq

/-- Helper toward Proposition 5.16: a winding lift whose loop avoids a
positive ray has imaginary part in one open angular strip determined by that
ray on the entire loop parameter interval. -/
theorem d39_winding_lift_avoiding_ray_stays_in_argument_strip
    {z w u : ℂ} (L : Path z z) (n : ℤ) (hu : u ≠ 0)
    (hwind : HasWinding L w n)
    (hray : ∀ t, L t - w ∉
      {q : ℂ | ∃ r : ℝ, 0 ≤ r ∧ q = (r : ℂ) * u}) :
    ∃ φ : C(unitInterval, ℂ),
      (∀ t, Complex.exp (φ t) = L t - w) ∧
        ∃ k : ℤ, ∀ t,
          u.arg + 2 * Real.pi * k < (φ t).im ∧
            (φ t).im < u.arg + 2 * Real.pi * (k + 1) := by
  rcases hwind with ⟨φ, hφ, _⟩
  have havoid := d39_logarithm_lift_avoids_ray_argument_lattice
    L φ hu hφ hray
  have hstrip := d39_continuous_angle_avoids_lattice_stays_in_strip
    (fun t => (φ t).im) (Complex.continuous_im.comp φ.continuous) u.arg havoid
  exact ⟨φ, hφ, hstrip⟩

/-- Helper toward Proposition 5.16: if two lifted angles differ by less than
one full turn in either direction and their difference is congruent to the
difference of two distinct ray arguments, then the increment is the
counterclockwise turn or that turn minus `2π`. -/
theorem d39_lifted_angle_increment_has_two_turn_branches
    (u v : ℂ) (x y : ℝ) (hangles : u.arg ≠ v.arg)
    (hcongr : ∃ k : ℤ,
      y - x = v.arg - u.arg + 2 * Real.pi * (k : ℝ))
    (hbound : -(2 * Real.pi) < y - x ∧ y - x < 2 * Real.pi) :
    y - x = ccwTurn u v ∨
      y - x = ccwTurn u v - 2 * Real.pi := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have huarg := Complex.arg_mem_Ioc u
  have hvarg := Complex.arg_mem_Ioc v
  change -Real.pi < u.arg ∧ u.arg ≤ Real.pi at huarg
  change -Real.pi < v.arg ∧ v.arg ≤ Real.pi at hvarg
  have hdiffLow : -(2 * Real.pi) < v.arg - u.arg := by linarith
  have hdiffHigh : v.arg - u.arg < 2 * Real.pi := by linarith
  rcases hcongr with ⟨k, hk⟩
  have hkLowReal : (-2 : ℝ) < (k : ℝ) := by
    nlinarith [hbound.1, hdiffHigh, hk, hpi]
  have hkHighReal : (k : ℝ) < 2 := by
    nlinarith [hbound.2, hdiffLow, hk, hpi]
  have hkLow : (-2 : ℤ) < k := by exact_mod_cast hkLowReal
  have hkHigh : k < 2 := by exact_mod_cast hkHighReal
  interval_cases k
  · have hdiffPos : 0 < v.arg - u.arg := by
      simp only [Int.cast_neg, Int.cast_one] at hk
      nlinarith [hbound.1, hk]
    right
    have harg : u.arg < v.arg := sub_pos.mp hdiffPos
    rw [ccwTurn_eq_turn_of_arg_lt harg]
    rw [hk]
    ring
  · by_cases harg : u.arg < v.arg
    · left
      simp [ccwTurn, harg, hk]
    · have hrev : v.arg < u.arg := by
        have hle : v.arg ≤ u.arg := le_of_not_gt harg
        exact lt_of_le_of_ne hle (Ne.symm hangles)
      right
      simp [ccwTurn, harg, hk]
  · have hdiffNeg : v.arg - u.arg < 0 := by
      simp only [Int.cast_one] at hk
      nlinarith [hbound.2, hk]
    left
    have hrev : v.arg < u.arg := sub_neg.mp hdiffNeg
    simp [ccwTurn, not_lt_of_ge hrev.le, hk]

/-- Helper toward Proposition 5.16: two lifted endpoint directions in the
same open angular strip have an increment equal to the counterclockwise turn
or to that turn minus `2π`. -/
theorem d39_same_strip_increment_has_two_turn_branches
    (u v : ℂ) (x y g : ℝ) (hangles : u.arg ≠ v.arg)
    (hxstrip : g < x ∧ x < g + 2 * Real.pi)
    (hystrip : g < y ∧ y < g + 2 * Real.pi)
    (hx : ∃ m : ℤ, x = u.arg + 2 * Real.pi * (m : ℝ))
    (hy : ∃ n : ℤ, y = v.arg + 2 * Real.pi * (n : ℝ)) :
    y - x = ccwTurn u v ∨
      y - x = ccwTurn u v - 2 * Real.pi := by
  rcases hx with ⟨m, hm⟩
  rcases hy with ⟨n, hn⟩
  have hcongr : ∃ k : ℤ,
      y - x = v.arg - u.arg + 2 * Real.pi * (k : ℝ) := by
    refine ⟨n - m, ?_⟩
    rw [hm, hn]
    push_cast
    ring
  have hbound : -(2 * Real.pi) < y - x ∧ y - x < 2 * Real.pi := by
    constructor <;> linarith [hxstrip.2, hystrip.1, hxstrip.1, hystrip.2]
  exact d39_lifted_angle_increment_has_two_turn_branches
    u v x y hangles hcongr hbound

/-- Helper toward Proposition 5.16: if each of three lifted increments takes
the clockwise branch exactly when the third image ray lies in that
counterclockwise sector, then their sum `2π` forces the image rays to have
positive cyclic order. -/
theorem d39_three_avoided_ray_increments_force_positive_order
    (u v w : ℂ) (a b c : ℝ)
    (huv : u.arg ≠ v.arg) (huw : u.arg ≠ w.arg) (hvw : v.arg ≠ w.arg)
    (hbranchUV : a = ccwTurn u v - 2 * Real.pi ↔
      ccwTurn u w < ccwTurn u v)
    (hbranchVW : b = ccwTurn v w - 2 * Real.pi ↔
      ccwTurn v u < ccwTurn v w)
    (hbranchWU : c = ccwTurn w u - 2 * Real.pi ↔
      ccwTurn w v < ccwTurn w u)
    (hsum : a + b + c = 2 * Real.pi) :
    ccwTurn u v < ccwTurn u w := by
  have hsectorUV_VW : ccwTurn u w < ccwTurn u v ↔
      ccwTurn v u < ccwTurn v w :=
    d39_between_cyclic huv hvw (Ne.symm huw)
  have hsectorVW_WU : ccwTurn v u < ccwTurn v w ↔
      ccwTurn w v < ccwTurn w u :=
    d39_between_cyclic hvw (Ne.symm huw) huv
  have hnotUV : ¬ ccwTurn u w < ccwTurn u v := by
    intro hUV
    have hVW := hsectorUV_VW.mp hUV
    have hWU := hsectorVW_WU.mp hVW
    have hincUV := hbranchUV.mpr hUV
    have hincVW := hbranchVW.mpr hVW
    have hincWU := hbranchWU.mpr hWU
    have hcomp := ccwTurn_comp_add hUV
    have hrevWV := ccwTurn_add_reverse w v (Ne.symm hvw)
    have hrevUW := ccwTurn_add_reverse u w huw
    have hsumTurns : ccwTurn u v + ccwTurn v w + ccwTurn w u =
        4 * Real.pi := by
      nlinarith [hcomp, hrevWV, hrevUW]
    have hsumIncrements : a + b + c = -(2 * Real.pi) := by
      rw [hincUV, hincVW, hincWU]
      nlinarith [hsumTurns]
    linarith [hsumIncrements, hsum, Real.pi_pos]
  have hturnNe : ccwTurn u v ≠ ccwTurn u w := by
    intro heq
    exact hvw (ccwTurn_left_injective heq)
  exact lt_of_le_of_ne (le_of_not_gt hnotUV) hturnNe









































































end DirectedDistances.PlanarMap

end
