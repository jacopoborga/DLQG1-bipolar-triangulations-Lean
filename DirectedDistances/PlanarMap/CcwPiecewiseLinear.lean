/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlaneRealization
public import DirectedDistances.PlanarMap.SlopeAngularOrder

/-! # Direction order under the past drawing transfer

Helpers toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result. See -/

public section
namespace DirectedDistances.PlanarMap

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result. See -/
@[expose] noncomputable def pastDirection (aPos aNeg bPos bNeg : ℝ) (v : ℂ) : ℂ :=
  if 0 < v.re then ⟨-aPos * v.re, -v.im + bPos * v.re⟩
  else ⟨-aNeg * v.re, -v.im + bNeg * v.re⟩

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result. See -/
@[expose] def planarCross (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result. See -/
theorem planarCross_pastLinear (a b : ℝ) (u v : ℂ) :
    planarCross ⟨-a * u.re, -u.im + b * u.re⟩
      ⟨-a * v.re, -v.im + b * v.re⟩ = a * planarCross u v := by
  simp only [planarCross]
  ring

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result. See
positive determinant `aPos`. -/
theorem pastDirection_cross_right (aPos aNeg bPos bNeg : ℝ) {u v : ℂ}
    (hu : 0 < u.re) (hv : 0 < v.re) :
    planarCross (pastDirection aPos aNeg bPos bNeg u)
      (pastDirection aPos aNeg bPos bNeg v) = aPos * planarCross u v := by
  simp only [pastDirection, ite_eq_left hu, ite_eq_left hv]
  exact planarCross_pastLinear aPos bPos u v

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result. See
positive determinant `aNeg`. -/
theorem pastDirection_cross_left (aPos aNeg bPos bNeg : ℝ) {u v : ℂ}
    (hu : u.re < 0) (hv : v.re < 0) :
    planarCross (pastDirection aPos aNeg bPos bNeg u)
      (pastDirection aPos aNeg bPos bNeg v) = aNeg * planarCross u v := by
  have hu' : ¬ 0 < u.re := not_lt.mpr hu.le
  have hv' : ¬ 0 < v.re := not_lt.mpr hv.le
  simp only [pastDirection, ite_eq_right hu', ite_eq_right hv']
  exact planarCross_pastLinear aNeg bNeg u v

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result. See
of the cross product within the right half-plane piece. -/
theorem pastDirection_cross_right_pos (aPos aNeg bPos bNeg : ℝ)
    (haPos : 0 < aPos) {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re)
    (hcross : 0 < planarCross u v) :
    0 < planarCross (pastDirection aPos aNeg bPos bNeg u)
      (pastDirection aPos aNeg bPos bNeg v) := by
  rw [pastDirection_cross_right aPos aNeg bPos bNeg hu hv]
  exact mul_pos haPos hcross

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result. See
of the cross product within the left half-plane piece. -/
theorem pastDirection_cross_left_pos (aPos aNeg bPos bNeg : ℝ)
    (haNeg : 0 < aNeg) {u v : ℂ} (hu : u.re < 0) (hv : v.re < 0)
    (hcross : 0 < planarCross u v) :
    0 < planarCross (pastDirection aPos aNeg bPos bNeg u)
      (pastDirection aPos aNeg bPos bNeg v) := by
  rw [pastDirection_cross_left aPos aNeg bPos bNeg hu hv]
  exact mul_pos haNeg hcross

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result. The right piece maps
strictly into the left half-plane. -/
theorem pastDirection_re_right_neg (aPos aNeg bPos bNeg : ℝ) (haPos : 0 < aPos)
    {u : ℂ} (hu : 0 < u.re) :
    (pastDirection aPos aNeg bPos bNeg u).re < 0 := by
  simp only [pastDirection, ite_eq_left hu]
  nlinarith [mul_pos haPos hu]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result. The left piece maps
strictly into the right half-plane. -/
theorem pastDirection_re_left_pos (aPos aNeg bPos bNeg : ℝ) (haNeg : 0 < aNeg)
    {u : ℂ} (hu : u.re < 0) :
    0 < (pastDirection aPos aNeg bPos bNeg u).re := by
  have hnot : ¬ 0 < u.re := not_lt.mpr hu.le
  simp only [pastDirection, ite_eq_right hnot]
  have hmul : 0 < aNeg * (-u.re) := mul_pos haNeg (neg_pos.mpr hu)
  nlinarith

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result. Translation of slope
by the positive linear piece preserves its strict order. -/
private theorem div_sub_pos_denom_lt_iff {x y b a : ℝ} (ha : 0 < a) :
    (x - b) / a < (y - b) / a ↔ x < y := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  constructor
  · intro h
    have hm := mul_lt_mul_of_pos_right h ha
    field_simp [ha0] at hm
    linarith
  · intro h
    have hm : x - b < y - b := by linarith
    exact div_lt_div_of_pos_right hm ha

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result. Slopes are strictly
ordered on the right half-plane piece. -/
theorem pastDirection_slope_order_right (aPos aNeg bPos bNeg : ℝ)
    (haPos : 0 < aPos) {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    (pastDirection aPos aNeg bPos bNeg u).im /
        (pastDirection aPos aNeg bPos bNeg u).re <
      (pastDirection aPos aNeg bPos bNeg v).im /
        (pastDirection aPos aNeg bPos bNeg v).re ↔
      u.im / u.re < v.im / v.re := by
  have hu0 : u.re ≠ 0 := ne_of_gt hu
  have hv0 : v.re ≠ 0 := ne_of_gt hv
  have hslope (z : ℂ) (hz : 0 < z.re) (hz0 : z.re ≠ 0) :
      (pastDirection aPos aNeg bPos bNeg z).im /
          (pastDirection aPos aNeg bPos bNeg z).re =
        (z.im / z.re - bPos) / aPos := by
    simp only [pastDirection, ite_eq_left hz]
    field_simp [haPos.ne', hz0]
    ring
  rw [hslope u hu hu0, hslope v hv hv0]
  exact div_sub_pos_denom_lt_iff (a := aPos) (b := bPos) haPos

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result. Slopes are strictly
ordered on the left half-plane piece. -/
theorem pastDirection_slope_order_left (aPos aNeg bPos bNeg : ℝ)
    (haNeg : 0 < aNeg) {u v : ℂ} (hu : u.re < 0) (hv : v.re < 0) :
    (pastDirection aPos aNeg bPos bNeg u).im /
        (pastDirection aPos aNeg bPos bNeg u).re <
      (pastDirection aPos aNeg bPos bNeg v).im /
        (pastDirection aPos aNeg bPos bNeg v).re ↔
      u.im / u.re < v.im / v.re := by
  have hu0 : u.re ≠ 0 := ne_of_lt hu
  have hv0 : v.re ≠ 0 := ne_of_lt hv
  have hu' : ¬ 0 < u.re := not_lt.mpr hu.le
  have hv' : ¬ 0 < v.re := not_lt.mpr hv.le
  have hslope (z : ℂ) (hz : z.re < 0) (hnot : ¬ 0 < z.re)
      (hz0 : z.re ≠ 0) :
      (pastDirection aPos aNeg bPos bNeg z).im /
          (pastDirection aPos aNeg bPos bNeg z).re =
        (z.im / z.re - bNeg) / aNeg := by
    simp only [pastDirection, ite_eq_right hnot]
    field_simp [haNeg.ne', hz0]
    ring
  rw [hslope u hu hu' hu0, hslope v hv hv' hv0]
  exact div_sub_pos_denom_lt_iff (a := aNeg) (b := bNeg) haNeg

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result. An argument shifted
to a cut at the downward vertical direction. -/
private noncomputable def ccwPhase (z : ℂ) : ℝ :=
  if Complex.arg z < -(Real.pi / 2) then Complex.arg z + 5 * Real.pi / 2
  else Complex.arg z + Real.pi / 2

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result. Positive cyclic
distance between two real coordinates modulo `2 * pi`. -/
private noncomputable def phaseTurn (x y : ℝ) : ℝ :=
  if x < y then y - x else y - x + 2 * Real.pi

/-- The shifted argument coordinate computes the same cyclic turn as `ccwTurn`. -/
private theorem ccwTurn_eq_phaseTurn (u v : ℂ) :
    ccwTurn u v = phaseTurn (ccwPhase u) (ccwPhase v) := by
  unfold ccwTurn ccwPhase phaseTurn
  have hu := Complex.arg_mem_Ioc u
  have hv := Complex.arg_mem_Ioc v
  change -Real.pi < Complex.arg u ∧ Complex.arg u ≤ Real.pi at hu
  change -Real.pi < Complex.arg v ∧ Complex.arg v ≤ Real.pi at hv
  split_ifs <;> nlinarith [hu.1, hu.2, hv.1, hv.2, Real.pi_pos]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result. On the right
half-plane the shifted argument is the arctangent slope plus `pi / 2`. -/
private theorem ccwPhase_right {z : ℂ} (hz : 0 < z.re) :
    ccwPhase z = Real.arctan (z.im / z.re) + Real.pi / 2 := by
  have harg := east_arg_eq_arctan hz
  have hcut : ¬ Complex.arg z < -(Real.pi / 2) := by
    rw [harg]
    exact not_lt.mpr (Real.neg_pi_div_two_lt_arctan _).le
  rw [ccwPhase, ite_eq_right hcut, harg]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result. On the left
half-plane the shifted argument is the arctangent slope plus `3 * pi / 2`. -/
private theorem ccwPhase_left {z : ℂ} (hz : z.re < 0) :
    ccwPhase z = Real.arctan (z.im / z.re) + 3 * Real.pi / 2 := by
  have hnorm := west_arg_normalized hz
  have hslope := west_arg_eq_arctan hz
  by_cases him : z.im < 0
  · have hcut := west_arg_lt_lower hz him
    rw [ccwPhase, ite_eq_left hcut, hnorm, ite_eq_left him, hslope]
    ring
  · have himnonneg : 0 ≤ z.im := le_of_not_gt him
    have hcut : ¬ Complex.arg z < -(Real.pi / 2) := by
      have harg := west_arg_gt_upper hz himnonneg
      linarith [Real.pi_pos]
    rw [ccwPhase, ite_eq_right hcut, hnorm, ite_eq_right him, hslope]
    ring

/-- The shifted argument increases exactly with slope on the right arc. -/
private theorem ccwPhase_order_right {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    ccwPhase u < ccwPhase v ↔ u.im / u.re < v.im / v.re := by
  rw [ccwPhase_right hu, ccwPhase_right hv]
  rw [add_lt_add_iff_right (Real.pi / 2)]
  exact Real.arctan_lt_arctan_iff

/-- The shifted argument increases exactly with slope on the left arc. -/
private theorem ccwPhase_order_left {u v : ℂ} (hu : u.re < 0) (hv : v.re < 0) :
    ccwPhase u < ccwPhase v ↔ u.im / u.re < v.im / v.re := by
  rw [ccwPhase_left hu, ccwPhase_left hv]
  rw [add_lt_add_iff_right (3 * Real.pi / 2)]
  exact Real.arctan_lt_arctan_iff

/-- The right half-plane occupies the first open half of the phase interval. -/
private theorem ccwPhase_range_right {z : ℂ} (hz : 0 < z.re) :
    0 < ccwPhase z ∧ ccwPhase z < Real.pi := by
  rw [ccwPhase_right hz]
  constructor <;> linarith [Real.neg_pi_div_two_lt_arctan (z.im / z.re),
    Real.arctan_lt_pi_div_two (z.im / z.re), Real.pi_pos]

/-- The left half-plane occupies the second open half of the phase interval. -/
private theorem ccwPhase_range_left {z : ℂ} (hz : z.re < 0) :
    Real.pi < ccwPhase z ∧ ccwPhase z < 2 * Real.pi := by
  rw [ccwPhase_left hz]
  constructor <;> linarith [Real.neg_pi_div_two_lt_arctan (z.im / z.re),
    Real.arctan_lt_pi_div_two (z.im / z.re), Real.pi_pos]

/-- Lift the output phase to the next interval when the input is left-going. -/
private noncomputable def pastPhaseLift (aPos aNeg bPos bNeg : ℝ) (z : ℂ) : ℝ :=
  if 0 < z.re then ccwPhase (pastDirection aPos aNeg bPos bNeg z)
  else ccwPhase (pastDirection aPos aNeg bPos bNeg z) + 2 * Real.pi

/-- The lifted output phase is strictly increasing along the input circle cut at
the downward vertical direction. -/
private theorem pastPhaseLift_strict (aPos aNeg bPos bNeg : ℝ)
    (haPos : 0 < aPos) (haNeg : 0 < aNeg) {u v : ℂ}
    (hunv : u.re ≠ 0) (hvn : v.re ≠ 0)
    (hphase : ccwPhase u < ccwPhase v) :
    pastPhaseLift aPos aNeg bPos bNeg u < pastPhaseLift aPos aNeg bPos bNeg v := by
  by_cases huR : 0 < u.re
  · by_cases hvR : 0 < v.re
    · have hs := (ccwPhase_order_right huR hvR).mp hphase
      have hsd := (pastDirection_slope_order_right aPos aNeg bPos bNeg haPos
        huR hvR).mpr hs
      have hdu := pastDirection_re_right_neg aPos aNeg bPos bNeg haPos huR
      have hdv := pastDirection_re_right_neg aPos aNeg bPos bNeg haPos hvR
      have hout := (ccwPhase_order_left hdu hdv).mpr hsd
      simpa [pastPhaseLift, huR, hvR] using hout
    · have hvL : v.re < 0 := lt_of_le_of_ne (le_of_not_gt hvR) hvn
      have hdu := pastDirection_re_right_neg aPos aNeg bPos bNeg haPos huR
      have hdv := pastDirection_re_left_pos aPos aNeg bPos bNeg haNeg hvL
      have hleft := ccwPhase_range_left hdu
      have hright := ccwPhase_range_right hdv
      simp [pastPhaseLift, huR, hvR]
      linarith [hleft.2, hright.1, Real.pi_pos]
  · have huL : u.re < 0 := lt_of_le_of_ne (le_of_not_gt huR) hunv
    by_cases hvR : 0 < v.re
    · have hright := ccwPhase_range_right hvR
      have hleft := ccwPhase_range_left huL
      linarith [hphase, hleft.1, hright.2]
    · have hvL : v.re < 0 := lt_of_le_of_ne (le_of_not_gt hvR) hvn
      have hs := (ccwPhase_order_left huL hvL).mp hphase
      have hsd := (pastDirection_slope_order_left aPos aNeg bPos bNeg haNeg
        huL hvL).mpr hs
      have hdu := pastDirection_re_left_pos aPos aNeg bPos bNeg haNeg huL
      have hdv := pastDirection_re_left_pos aPos aNeg bPos bNeg haNeg hvL
      have hout := (ccwPhase_order_right hdu hdv).mpr hsd
      simpa [pastPhaseLift, huR, hvR] using add_lt_add_right hout (2 * Real.pi)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result. See
missing cyclic-turn comparison theorem for the direction map. -/
theorem ccwSuccessor_comp_of_turnOrder {D : Type*} (star : Set D)
    (dir : D → ℂ) (g : ℂ → ℂ) (d e : D)
    (hturn : ∀ x y z : ℂ,
      (ccwTurn (g x) (g y) ≤ ccwTurn (g x) (g z) ↔
        ccwTurn x y ≤ ccwTurn x z)) :
    CcwSuccessor star (g ∘ dir) d e ↔ CcwSuccessor star dir d e := by
  constructor
  · rintro ⟨hfin, hd, he, hnext⟩
    refine ⟨hfin, hd, he, ?_⟩
    rcases hnext with hs | hnext
    · exact Or.inl hs
    · rcases hnext with ⟨hne, hmin⟩
      refine Or.inr ⟨hne, ?_⟩
      intro f hf hfd
      exact (hturn (dir d) (dir e) (dir f)).mp (hmin f hf hfd)
  · rintro ⟨hfin, hd, he, hnext⟩
    refine ⟨hfin, hd, he, ?_⟩
    rcases hnext with hs | hnext
    · exact Or.inl hs
    · rcases hnext with ⟨hne, hmin⟩
      refine Or.inr ⟨hne, ?_⟩
      intro f hf hfd
      exact (hturn (dir d) (dir e) (dir f)).mpr (hmin f hf hfd)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result.
Restricts the comparison premise to directions in the star. -/
theorem ccwSuccessor_comp_of_turnOrder_on {D : Type*} (star : Set D)
    (dir : D → ℂ) (g : ℂ → ℂ) (d e : D)
    (hturn : ∀ f ∈ star, ∀ h ∈ star, ∀ k ∈ star,
      (ccwTurn (g (dir f)) (g (dir h)) ≤ ccwTurn (g (dir f)) (g (dir k)) ↔
        ccwTurn (dir f) (dir h) ≤ ccwTurn (dir f) (dir k))) :
    CcwSuccessor star (g ∘ dir) d e ↔ CcwSuccessor star dir d e := by
  constructor
  · rintro ⟨hfin, hd, he, hnext⟩
    refine ⟨hfin, hd, he, ?_⟩
    rcases hnext with hs | ⟨hne, hmin⟩
    · exact Or.inl hs
    · exact Or.inr ⟨hne, fun f hf hfd =>
        (hturn d hd e he f hf).mp (hmin f hf hfd)⟩
  · rintro ⟨hfin, hd, he, hnext⟩
    refine ⟨hfin, hd, he, ?_⟩
    rcases hnext with hs | ⟨hne, hmin⟩
    · exact Or.inl hs
    · exact Or.inr ⟨hne, fun f hf hfd =>
        (hturn d hd e he f hf).mpr (hmin f hf hfd)⟩

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result.
The lifted phase lies in an open interval of length two pi. -/
private theorem pastPhaseLift_range (aPos aNeg bPos bNeg : ℝ)
    (haPos : 0 < aPos) (haNeg : 0 < aNeg) {z : ℂ} (hz : z.re ≠ 0) :
    Real.pi < pastPhaseLift aPos aNeg bPos bNeg z ∧
      pastPhaseLift aPos aNeg bPos bNeg z < 3 * Real.pi := by
  by_cases h : 0 < z.re
  · have hr := ccwPhase_range_left
      (pastDirection_re_right_neg aPos aNeg bPos bNeg haPos h)
    simp only [pastPhaseLift, ite_eq_left h]
    constructor <;> linarith [hr.1, hr.2, Real.pi_pos]
  · have hl : z.re < 0 := lt_of_le_of_ne (le_of_not_gt h) hz
    have hr := ccwPhase_range_right
      (pastDirection_re_left_pos aPos aNeg bPos bNeg haNeg hl)
    simp only [pastPhaseLift, ite_eq_right h]
    constructor <;> linarith [hr.1, hr.2, Real.pi_pos]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result.
The lift differs from the output phase by zero or two pi. -/
private theorem pastPhaseLift_phase (aPos aNeg bPos bNeg : ℝ) (z : ℂ) :
    ccwPhase (pastDirection aPos aNeg bPos bNeg z) =
        pastPhaseLift aPos aNeg bPos bNeg z ∨
      ccwPhase (pastDirection aPos aNeg bPos bNeg z) =
        pastPhaseLift aPos aNeg bPos bNeg z - 2 * Real.pi := by
  by_cases hz : 0 < z.re
  · exact Or.inl (by simp only [pastPhaseLift, ite_eq_left hz])
  · right
    simp only [pastPhaseLift, ite_eq_right hz, add_sub_cancel_right]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result.
The lifted phase also reflects strict order. -/
private theorem pastPhaseLift_lt_iff (aPos aNeg bPos bNeg : ℝ)
    (haPos : 0 < aPos) (haNeg : 0 < aNeg) {u v : ℂ}
    (hu : u.re ≠ 0) (hv : v.re ≠ 0) :
    pastPhaseLift aPos aNeg bPos bNeg u < pastPhaseLift aPos aNeg bPos bNeg v ↔
      ccwPhase u < ccwPhase v := by
  refine ⟨?_, pastPhaseLift_strict aPos aNeg bPos bNeg haPos haNeg hu hv⟩
  intro h
  by_cases hur : 0 < u.re
  · by_cases hvr : 0 < v.re
    · have hdu := pastDirection_re_right_neg aPos aNeg bPos bNeg haPos hur
      have hdv := pastDirection_re_right_neg aPos aNeg bPos bNeg haPos hvr
      simp only [pastPhaseLift, ite_eq_left hur, ite_eq_left hvr] at h
      exact (ccwPhase_order_right hur hvr).mpr
        ((pastDirection_slope_order_right aPos aNeg bPos bNeg haPos hur hvr).mp
          ((ccwPhase_order_left hdu hdv).mp h))
    · have hvl : v.re < 0 := lt_of_le_of_ne (le_of_not_gt hvr) hv
      have hr := ccwPhase_range_right hur
      have hl := ccwPhase_range_left hvl
      linarith [hr.2, hl.1]
  · have hul : u.re < 0 := lt_of_le_of_ne (le_of_not_gt hur) hu
    by_cases hvr : 0 < v.re
    · have hdu := ccwPhase_range_right
        (pastDirection_re_left_pos aPos aNeg bPos bNeg haNeg hul)
      have hdv := ccwPhase_range_left
        (pastDirection_re_right_neg aPos aNeg bPos bNeg haPos hvr)
      simp only [pastPhaseLift, ite_eq_right hur, ite_eq_left hvr] at h
      linarith [hdu.1, hdv.2]
    · have hvl : v.re < 0 := lt_of_le_of_ne (le_of_not_gt hvr) hv
      have hdu := pastDirection_re_left_pos aPos aNeg bPos bNeg haNeg hul
      have hdv := pastDirection_re_left_pos aPos aNeg bPos bNeg haNeg hvl
      simp only [pastPhaseLift, ite_eq_right hur, ite_eq_right hvr,
        add_lt_add_iff_right] at h
      exact (ccwPhase_order_left hul hvl).mpr
        ((pastDirection_slope_order_left aPos aNeg bPos bNeg haNeg hul hvl).mp
          ((ccwPhase_order_right hdu hdv).mp h))

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result.
Equality of lifted phases is exactly equality of input phases. -/
private theorem pastPhaseLift_eq_iff (aPos aNeg bPos bNeg : ℝ)
    (haPos : 0 < aPos) (haNeg : 0 < aNeg) {u v : ℂ}
    (hu : u.re ≠ 0) (hv : v.re ≠ 0) :
    pastPhaseLift aPos aNeg bPos bNeg u = pastPhaseLift aPos aNeg bPos bNeg v ↔
      ccwPhase u = ccwPhase v := by
  have h₁ := pastPhaseLift_lt_iff aPos aNeg bPos bNeg haPos haNeg hu hv
  have h₂ := pastPhaseLift_lt_iff aPos aNeg bPos bNeg haPos haNeg hv hu
  constructor
  · intro h
    exact le_antisymm (le_of_not_gt (fun hlt => (h₂.mpr hlt).ne h.symm))
      (le_of_not_gt (fun hlt => (h₁.mpr hlt).ne h))
  · intro h
    exact le_antisymm (le_of_not_gt (fun hlt => (h₂.mp hlt).ne h.symm))
      (le_of_not_gt (fun hlt => (h₁.mp hlt).ne h))

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result.
Comparison of cyclic turns uses only order in one full-period interval. -/
private theorem phaseTurn_compare (x y z X Y Z : ℝ)
    (hyz : y < z + 2 * Real.pi) (hzy : z < y + 2 * Real.pi)
    (hYZ : Y < Z + 2 * Real.pi) (hZY : Z < Y + 2 * Real.pi)
    (hxy : x < y ↔ X < Y) (hxz : x < z ↔ X < Z)
    (hyz' : y ≤ z ↔ Y ≤ Z) :
    phaseTurn x y ≤ phaseTurn x z ↔ phaseTurn X Y ≤ phaseTurn X Z := by
  by_cases hxy' : x < y
  · have hXY := hxy.mp hxy'
    by_cases hxz' : x < z
    · have hXZ := hxz.mp hxz'
      simpa only [phaseTurn, ite_eq_left hxy', ite_eq_left hxz', ite_eq_left hXY,
        ite_eq_left hXZ, sub_le_sub_iff_right] using hyz'
    · have hXZ : ¬ X < Z := fun h => hxz' (hxz.mpr h)
      simp only [phaseTurn, ite_eq_left hxy', ite_eq_right hxz', ite_eq_left hXY, ite_eq_right hXZ]
      constructor <;> intro h <;> linarith
  · have hXY : ¬ X < Y := fun h => hxy' (hxy.mpr h)
    by_cases hxz' : x < z
    · have hXZ := hxz.mp hxz'
      simp only [phaseTurn, ite_eq_right hxy', ite_eq_left hxz', ite_eq_right hXY, ite_eq_left hXZ]
      constructor <;> intro h <;> linarith
    · have hXZ : ¬ X < Z := fun h => hxz' (hxz.mpr h)
      simpa only [phaseTurn, ite_eq_right hxy', ite_eq_right hxz', ite_eq_right hXY,
        ite_eq_right hXZ, add_le_add_iff_right, sub_le_sub_iff_right] using hyz'

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result.
Changing from the lifted interval back to the phase interval preserves turns. -/
private theorem pastPhaseLift_turn (aPos aNeg bPos bNeg : ℝ)
    (haPos : 0 < aPos) (haNeg : 0 < aNeg) {u v : ℂ}
    (hu : u.re ≠ 0) (hv : v.re ≠ 0) :
    phaseTurn (pastPhaseLift aPos aNeg bPos bNeg u)
        (pastPhaseLift aPos aNeg bPos bNeg v) =
      phaseTurn (ccwPhase (pastDirection aPos aNeg bPos bNeg u))
        (ccwPhase (pastDirection aPos aNeg bPos bNeg v)) := by
  by_cases hur : 0 < u.re
  · by_cases hvr : 0 < v.re
    · simp only [pastPhaseLift, ite_eq_left hur, ite_eq_left hvr]
    · have hvl : v.re < 0 := lt_of_le_of_ne (le_of_not_gt hvr) hv
      have hdu := ccwPhase_range_left
        (pastDirection_re_right_neg aPos aNeg bPos bNeg haPos hur)
      have hdv := ccwPhase_range_right
        (pastDirection_re_left_pos aPos aNeg bPos bNeg haNeg hvl)
      simp only [pastPhaseLift, ite_eq_left hur, ite_eq_right hvr, phaseTurn]
      split_ifs <;> linarith [hdu.1, hdu.2, hdv.1, hdv.2]
  · have hul : u.re < 0 := lt_of_le_of_ne (le_of_not_gt hur) hu
    by_cases hvr : 0 < v.re
    · have hdu := ccwPhase_range_right
        (pastDirection_re_left_pos aPos aNeg bPos bNeg haNeg hul)
      have hdv := ccwPhase_range_left
        (pastDirection_re_right_neg aPos aNeg bPos bNeg haPos hvr)
      simp only [pastPhaseLift, ite_eq_right hur, ite_eq_left hvr, phaseTurn]
      split_ifs <;> linarith [hdu.1, hdu.2, hdv.1, hdv.2]
    · simp only [pastPhaseLift, ite_eq_right hur, ite_eq_right hvr, phaseTurn,
        add_lt_add_iff_right]
      split_ifs <;> ring

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result.
The input phase is in the standard full-period interval. -/
private theorem ccwPhase_range {z : ℂ} (hz : z.re ≠ 0) :
    0 < ccwPhase z ∧ ccwPhase z < 2 * Real.pi := by
  rcases lt_or_gt_of_ne hz with h | h
  · have hr := ccwPhase_range_left h
    exact ⟨by linarith [hr.1, Real.pi_pos], hr.2⟩
  · have hr := ccwPhase_range_right h
    exact ⟨hr.1, by linarith [hr.2, Real.pi_pos]⟩

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result.
The piecewise transfer preserves cyclic-turn comparisons off the vertical axis. -/
theorem pastDirection_turn_le_iff (aPos aNeg bPos bNeg : ℝ)
    (haPos : 0 < aPos) (haNeg : 0 < aNeg) {x y z : ℂ}
    (hx : x.re ≠ 0) (hy : y.re ≠ 0) (hz : z.re ≠ 0) :
    ccwTurn (pastDirection aPos aNeg bPos bNeg x)
        (pastDirection aPos aNeg bPos bNeg y) ≤
      ccwTurn (pastDirection aPos aNeg bPos bNeg x)
        (pastDirection aPos aNeg bPos bNeg z) ↔
      ccwTurn x y ≤ ccwTurn x z := by
  rw [ccwTurn_eq_phaseTurn, ccwTurn_eq_phaseTurn, ccwTurn_eq_phaseTurn,
    ccwTurn_eq_phaseTurn,
    ← pastPhaseLift_turn aPos aNeg bPos bNeg haPos haNeg hx hy,
    ← pastPhaseLift_turn aPos aNeg bPos bNeg haPos haNeg hx hz]
  have hpY := ccwPhase_range hy
  have hpZ := ccwPhase_range hz
  have hLY := pastPhaseLift_range aPos aNeg bPos bNeg haPos haNeg hy
  have hLZ := pastPhaseLift_range aPos aNeg bPos bNeg haPos haNeg hz
  apply phaseTurn_compare
  · linarith [hLY.2, hLZ.1]
  · linarith [hLZ.2, hLY.1]
  · linarith [hpY.2, hpZ.1]
  · linarith [hpZ.2, hpY.1]
  · exact pastPhaseLift_lt_iff aPos aNeg bPos bNeg haPos haNeg hx hy
  · exact pastPhaseLift_lt_iff aPos aNeg bPos bNeg haPos haNeg hx hz
  · exact not_lt.symm.trans
      ((not_congr (pastPhaseLift_lt_iff aPos aNeg bPos bNeg haPos haNeg hz hy)).trans
        not_lt)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result.
The piecewise transfer preserves successors in stars without vertical directions. -/
theorem ccwSuccessor_comp_pwLinear {D : Type*} (star : Set D) (dir : D → ℂ)
    (aPos aNeg bPos bNeg : ℝ) (haPos : 0 < aPos) (haNeg : 0 < aNeg)
    (hdir : ∀ f ∈ star, (dir f).re ≠ 0) (d e : D) :
    CcwSuccessor star (pastDirection aPos aNeg bPos bNeg ∘ dir) d e ↔
      CcwSuccessor star dir d e := by
  apply ccwSuccessor_comp_of_turnOrder_on
  intro f hf h hh k hk
  exact pastDirection_turn_le_iff aPos aNeg bPos bNeg haPos haNeg
    (hdir f hf) (hdir h hh) (hdir k hk)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result.
Independent positive real rescaling of the two directions preserves the turn. -/
theorem ccwTurn_smul_pos (a b : ℂ) (c c' : ℝ) (hc : 0 < c) (hc' : 0 < c') :
    ccwTurn ((c : ℂ) * a) ((c' : ℂ) * b) = ccwTurn a b := by
  simp only [ccwTurn, Complex.arg_real_mul a hc, Complex.arg_real_mul b hc']

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: ccw order under the
orientation-preserving past transfer); not a paper result.
Positive real rescaling of each direction preserves successors. -/
theorem ccwSuccessor_smul_pos {D : Type*} (star : Set D) (dir : D → ℂ)
    (c : D → ℝ) (hc : ∀ f ∈ star, 0 < c f) (d e : D) :
    CcwSuccessor star (fun f => (c f : ℂ) * dir f) d e ↔
      CcwSuccessor star dir d e := by
  constructor
  · rintro ⟨hfin, hd, he, hnext⟩
    refine ⟨hfin, hd, he, ?_⟩
    rcases hnext with hs | ⟨hne, hmin⟩
    · exact Or.inl hs
    · refine Or.inr ⟨hne, ?_⟩
      intro f hf hfd
      have h := hmin f hf hfd
      simpa only [ccwTurn_smul_pos _ _ _ _ (hc d hd) (hc e he),
        ccwTurn_smul_pos _ _ _ _ (hc d hd) (hc f hf)] using h
  · rintro ⟨hfin, hd, he, hnext⟩
    refine ⟨hfin, hd, he, ?_⟩
    rcases hnext with hs | ⟨hne, hmin⟩
    · exact Or.inl hs
    · refine Or.inr ⟨hne, ?_⟩
      intro f hf hfd
      simpa only [ccwTurn_smul_pos _ _ _ _ (hc d hd) (hc e he),
        ccwTurn_smul_pos _ _ _ _ (hc d hd) (hc f hf)] using hmin f hf hfd

end DirectedDistances.PlanarMap
