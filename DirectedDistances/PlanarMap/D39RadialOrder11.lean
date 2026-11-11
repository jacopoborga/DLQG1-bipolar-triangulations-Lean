/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39RadialOrder10

/-! # Three-ray order helpers toward Proposition 5.16 -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16: when the rotated circle starts in the
direction of `u`, the hit time of a distinct ray `v` is its counterclockwise
turn from `u`, divided by one full turn. -/
theorem d39_rotatedCircleRayHitTime_eq_ccwTurn_div
    (u v : ℂ) (huv : u.arg ≠ v.arg) :
    d39RotatedCircleRayHitTime u.arg v =
      ccwTurn u v / (2 * Real.pi) := by
  have huarg := Complex.arg_mem_Ioc u
  have hvarg := Complex.arg_mem_Ioc v
  change -Real.pi < u.arg ∧ u.arg ≤ Real.pi at huarg
  change -Real.pi < v.arg ∧ v.arg ≤ Real.pi at hvarg
  by_cases huvlt : u.arg < v.arg
  · have hhigh : v.arg < u.arg + 2 * Real.pi := by
      linarith [huarg.1, hvarg.2]
    have hlow' : u.arg < v.arg + 2 * Real.pi * (0 : ℤ) := by
      simpa using huvlt
    have hhigh' : v.arg + 2 * Real.pi * (0 : ℤ) < u.arg + 2 * Real.pi := by
      simpa using hhigh
    calc
      d39RotatedCircleRayHitTime u.arg v =
          (v.arg + 2 * Real.pi * (0 : ℤ) - u.arg) / (2 * Real.pi) :=
        d39_rotatedCircleRayHitTime_eq_of_lift u.arg v 0 hlow' hhigh'
      _ = ccwTurn u v / (2 * Real.pi) := by
        rw [ccwTurn_eq_turn_of_arg_lt huvlt]
        ring
  · have hvult : v.arg < u.arg := by
      have hvle : v.arg ≤ u.arg := le_of_not_gt huvlt
      exact lt_of_le_of_ne hvle (Ne.symm huv)
    have hlow : u.arg < v.arg + 2 * Real.pi := by
      linarith [huarg.1, hvarg.2]
    have hhigh : v.arg + 2 * Real.pi < u.arg + 2 * Real.pi := by
      linarith
    have hlow' : u.arg < v.arg + 2 * Real.pi * (1 : ℤ) := by
      simpa using hlow
    have hhigh' : v.arg + 2 * Real.pi * (1 : ℤ) < u.arg + 2 * Real.pi := by
      simpa using hhigh
    calc
      d39RotatedCircleRayHitTime u.arg v =
          (v.arg + 2 * Real.pi * (1 : ℤ) - u.arg) / (2 * Real.pi) :=
        d39_rotatedCircleRayHitTime_eq_of_lift u.arg v 1 hlow' hhigh'
      _ = ccwTurn u v / (2 * Real.pi) := by
        rw [ccwTurn]
        simp [not_lt_of_ge hvult.le]
        ring

/-- Helper toward Proposition 5.16: from a starting ray, the ordering of two
distinct ray hit times agrees with the ordering of their counterclockwise
turns. -/
theorem d39_rotatedCircleRayHitTime_lt_iff_ccwTurn_lt
    (u v w : ℂ) (huv : u.arg ≠ v.arg) (huw : u.arg ≠ w.arg) :
    d39RotatedCircleRayHitTime u.arg v < d39RotatedCircleRayHitTime u.arg w ↔
      ccwTurn u v < ccwTurn u w := by
  rw [d39_rotatedCircleRayHitTime_eq_ccwTurn_div u v huv,
    d39_rotatedCircleRayHitTime_eq_ccwTurn_div u w huw]
  have hperiod : 0 < 2 * Real.pi := by positivity
  constructor <;> intro h
  · have h' := mul_lt_mul_of_pos_right h hperiod
    field_simp at h'
    exact h'
  · have h' := mul_lt_mul_of_pos_right h (inv_pos.mpr hperiod)
    simpa [div_eq_mul_inv] using h'

/-- Helper toward Proposition 5.16: a logarithm lift whose exponential is a
positive multiple of a nonzero ray has imaginary part congruent to that
ray's argument modulo `2π`. -/
theorem d39_exp_positive_ray_argument_lift
    (z u : ℂ) (r : ℝ) (hu : u ≠ 0) (hr : 0 < r)
    (hexp : Complex.exp z = (r : ℂ) * u) :
    ∃ k : ℤ, z.im = u.arg + 2 * Real.pi * (k : ℝ) := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hru : (r : ℂ) * u ≠ 0 := mul_ne_zero hrc hu
  have hcanonical : Complex.exp (Complex.log ((r : ℂ) * u)) = (r : ℂ) * u :=
    Complex.exp_log hru
  have heq : Complex.exp z = Complex.exp (Complex.log ((r : ℂ) * u)) :=
    hexp.trans hcanonical.symm
  obtain ⟨k, hk⟩ := (Complex.exp_eq_exp_iff_exists_int).1 heq
  refine ⟨k, ?_⟩
  have him := congrArg Complex.im hk
  have himarg : (Complex.log ((r : ℂ) * u)).im = u.arg := by
    rw [Complex.log_im, Complex.arg_real_mul _ hr]
  have hcongr : z.im = u.arg + (k : ℝ) * (2 * Real.pi) := by
    simpa [himarg] using him
  nlinarith [hcongr]

/-- Helper toward Proposition 5.16: distinct complex directions are not
congruent modulo a full turn when measured from one of those directions. -/
theorem d39_distinct_args_not_congruent_mod_two_pi
    (u v : ℂ) (huv : u.arg ≠ v.arg) :
    ∀ k : ℤ, v.arg ≠ u.arg + 2 * Real.pi * (k : ℝ) := by
  intro k h
  have huarg := Complex.arg_mem_Ioc u
  have hvarg := Complex.arg_mem_Ioc v
  change -Real.pi < u.arg ∧ u.arg ≤ Real.pi at huarg
  change -Real.pi < v.arg ∧ v.arg ≤ Real.pi at hvarg
  have hperiod : 0 < 2 * Real.pi := by positivity
  have hlow : -(2 * Real.pi) < v.arg - u.arg := by
    linarith [huarg.2, hvarg.1]
  have hhigh : v.arg - u.arg < 2 * Real.pi := by
    linarith [huarg.1, hvarg.2]
  have hklo : (-1 : ℝ) < (k : ℝ) := by nlinarith [h, hlow, hperiod]
  have hkhi : (k : ℝ) < 1 := by nlinarith [h, hhigh, hperiod]
  have hk : k = 0 := by
    have hklo' : (-1 : ℤ) < k := by exact_mod_cast hklo
    have hkhi' : k < 1 := by exact_mod_cast hkhi
    omega
  apply huv
  rw [h, hk]
  ring

/- ∀ (K : ℂ ≃ₜ ℂ) (hK : OrientationPreserving K) (hK0 : K 0 = 0)
  (u v w u' v' w' : ℂ)
  (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
  (hu' : u' ≠ 0) (hv' : v' ≠ 0) (hw' : w' ≠ 0)
  (huv : u.arg ≠ v.arg) (huw : u.arg ≠ w.arg)
  (hvw : v.arg ≠ w.arg)
  (hsegmentsU : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
    K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * u} =
      {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * u'})
  (hsegmentsV : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
    K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * v} =
      {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * v'})
  (hsegmentsW : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
    K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * w} =
      {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * w'}),
  ccwTurn u w < ccwTurn u v ↔ ccwTurn u' w' < ccwTurn u' v'.

Approaches attempted:
1. Parameterize the source circle from `u.arg`. The proved hit-time formula
   converts the source turn comparison into an order of hit times, and the
   modular noncongruence lemma supplies the strict interior hit hypotheses.
   The remaining work is to carry those times through the image germ equalities
   and establish the image-angle strip data.
2. Use one winding-one lift of the image loop. The positive-ray lift lemma
   supplies endpoint argument congruences. The remaining work is to prove
   avoidance at interval endpoints and glue the strips across parameters 0/1
   for the wrap-around increment.
3. Apply `d39_three_avoided_ray_increments_force_positive_order` after proving
   the three branch equivalences. The algebraic lemma and branch criterion are
   available, but the geometric avoidance and wrap-around inputs are not yet
   established from the source segment assumptions. -/

end DirectedDistances.PlanarMap

end
