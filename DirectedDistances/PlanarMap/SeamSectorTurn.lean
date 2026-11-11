/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlaneRealization

/-! # Angular sectors at seam vertices

The boundary directions are `eR = (1, sR)` and `eL = (-1, -sL)`.
These are local geometric helpers, not statements of paper results. -/

public section
namespace DirectedDistances.PlanarMap

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: angular sectors at seam vertices);
not a paper result. Strictly above the two rays of a seam graph. -/
@[expose] def AboveSector (sL sR : ℝ) (u : ℂ) : Prop :=
  (0 < u.re → sR * u.re < u.im) ∧
    (u.re < 0 → sL * u.re < u.im) ∧ (u.re = 0 → 0 < u.im)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: angular sectors at seam vertices);
not a paper result. Strictly below the two rays of a seam graph. -/
@[expose] def BelowSector (sL sR : ℝ) (u : ℂ) : Prop :=
  (0 < u.re → u.im < sR * u.re) ∧
    (u.re < 0 → u.im < sL * u.re) ∧ (u.re = 0 → u.im < 0)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: angular sectors at seam vertices);
not a paper result. Argument with its cut at the downward vertical ray. -/
private noncomputable def ccwPhase (z : ℂ) : ℝ :=
  if Complex.arg z < -(Real.pi / 2) then Complex.arg z + 5 * Real.pi / 2
  else Complex.arg z + Real.pi / 2

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: angular sectors at seam vertices);
not a paper result. Positive cyclic displacement in phase coordinates. -/
private noncomputable def phaseTurn (x y : ℝ) : ℝ :=
  if x < y then y - x else y - x + 2 * Real.pi

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: angular sectors at seam vertices);
not a paper result. Changing the argument cut preserves cyclic displacement. -/
private theorem ccwTurn_eq_phaseTurn (u v : ℂ) :
    ccwTurn u v = phaseTurn (ccwPhase u) (ccwPhase v) := by
  unfold ccwTurn ccwPhase phaseTurn
  have hu := Complex.arg_mem_Ioc u
  have hv := Complex.arg_mem_Ioc v
  change -Real.pi < Complex.arg u ∧ Complex.arg u ≤ Real.pi at hu
  change -Real.pi < Complex.arg v ∧ Complex.arg v ≤ Real.pi at hv
  split_ifs <;> nlinarith [hu.1, hu.2, hv.1, hv.2, Real.pi_pos]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: angular sectors at seam vertices);
not a paper result. The phase lies in the half-open interval of length one turn. -/
private theorem ccwPhase_range (z : ℂ) :
    0 ≤ ccwPhase z ∧ ccwPhase z < 2 * Real.pi := by
  have hz := Complex.arg_mem_Ioc z
  change -Real.pi < Complex.arg z ∧ Complex.arg z ≤ Real.pi at hz
  unfold ccwPhase
  split_ifs <;> constructor <;> linarith [hz.1, hz.2, Real.pi_pos]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: angular sectors at seam vertices);
not a paper result. On the right half-plane argument is arctangent of slope. -/
private theorem sectorArgRight {z : ℂ} (hz : 0 < z.re) :
    Complex.arg z = Real.arctan (z.im / z.re) := by
  have harg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have hlow := (abs_lt.mp harg).1
  have hup := (abs_lt.mp harg).2
  rw [← Real.arctan_tan hlow hup, Complex.tan_arg]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: angular sectors at seam vertices);
not a paper result. The right half-plane phase is arctangent slope plus pi/2. -/
private theorem ccwPhase_right {z : ℂ} (hz : 0 < z.re) :
    ccwPhase z = Real.arctan (z.im / z.re) + Real.pi / 2 := by
  have harg := sectorArgRight hz
  have hcut : ¬ Complex.arg z < -(Real.pi / 2) := by
    rw [harg]
    exact not_lt.mpr (Real.neg_pi_div_two_lt_arctan _).le
  rw [ccwPhase, ite_eq_right hcut, harg]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: angular sectors at seam vertices);
not a paper result. The left half-plane phase is arctangent slope plus 3pi/2. -/
private theorem ccwPhase_left {z : ℂ} (hz : z.re < 0) :
    ccwPhase z = Real.arctan (z.im / z.re) + 3 * Real.pi / 2 := by
  have hnre : 0 < (-z).re := by simpa only [Complex.neg_re] using neg_pos.mpr hz
  have hnarg : Complex.arg (-z) = Real.arctan (z.im / z.re) := by
    simpa only [Complex.neg_im, Complex.neg_re, neg_div_neg_eq] using
      sectorArgRight hnre
  have hbounds := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hnre)
  have hlo := (abs_lt.mp hbounds).1
  have hhi := (abs_lt.mp hbounds).2
  by_cases him : z.im < 0
  · have hn : 0 < (-z).im := by simpa only [Complex.neg_im] using neg_pos.mpr him
    have harg : Complex.arg z = Complex.arg (-z) - Real.pi := by
      simpa only [neg_neg] using Complex.arg_neg_eq_arg_sub_pi_of_im_pos hn
    have hcut : Complex.arg z < -(Real.pi / 2) := by rw [harg]; linarith
    rw [ccwPhase, ite_eq_left hcut, harg, hnarg]
    ring
  · have harg : Complex.arg z = Complex.arg (-z) + Real.pi := by
      by_cases hzero : z.im = 0
      · have hzarg := Complex.arg_eq_pi_iff.mpr ⟨hz, hzero⟩
        have hnzero : Complex.arg (-z) = 0 := by
          apply Complex.arg_eq_zero_iff.mpr
          exact ⟨hnre.le, by simpa only [Complex.neg_im, neg_eq_zero] using hzero⟩
        rw [hzarg, hnzero, zero_add]
      · have hpos : 0 < z.im := lt_of_le_of_ne (le_of_not_gt him) (Ne.symm hzero)
        have hn : (-z).im < 0 := by
          simpa only [Complex.neg_im] using neg_neg_of_pos hpos
        simpa only [neg_neg] using Complex.arg_neg_eq_arg_add_pi_of_im_neg hn
    have hcut : ¬ Complex.arg z < -(Real.pi / 2) := by
      rw [harg]
      linarith [Real.pi_pos]
    rw [ccwPhase, ite_eq_right hcut, harg, hnarg]
    ring

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: angular sectors at seam vertices);
not a paper result. Right-going phases lie strictly between zero and pi. -/
private theorem ccwPhase_range_right {z : ℂ} (hz : 0 < z.re) :
    0 < ccwPhase z ∧ ccwPhase z < Real.pi := by
  rw [ccwPhase_right hz]
  constructor <;> linarith [Real.neg_pi_div_two_lt_arctan (z.im / z.re),
    Real.arctan_lt_pi_div_two (z.im / z.re)]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: angular sectors at seam vertices);
not a paper result. Left-going phases lie strictly between pi and two pi. -/
private theorem ccwPhase_range_left {z : ℂ} (hz : z.re < 0) :
    Real.pi < ccwPhase z ∧ ccwPhase z < 2 * Real.pi := by
  rw [ccwPhase_left hz]
  constructor <;> linarith [Real.neg_pi_div_two_lt_arctan (z.im / z.re),
    Real.arctan_lt_pi_div_two (z.im / z.re)]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: angular sectors at seam vertices);
not a paper result. The upward vertical ray has phase pi. -/
private theorem ccwPhase_up {z : ℂ} (hre : z.re = 0) (him : 0 < z.im) :
    ccwPhase z = Real.pi := by
  have harg := Complex.arg_eq_pi_div_two_iff.mpr ⟨hre, him⟩
  have hcut : ¬ Complex.arg z < -(Real.pi / 2) := by rw [harg]; linarith [Real.pi_pos]
  rw [ccwPhase, ite_eq_right hcut, harg]
  ring

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: angular sectors at seam vertices);
not a paper result. The downward vertical ray has phase zero. -/
private theorem ccwPhase_down {z : ℂ} (hre : z.re = 0) (him : z.im < 0) :
    ccwPhase z = 0 := by
  have harg := Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨hre, him⟩
  have hcut : ¬ Complex.arg z < -(Real.pi / 2) := by rw [harg]; exact lt_irrefl _
  rw [ccwPhase, ite_eq_right hcut, harg]
  ring

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: angular sectors at seam vertices);
not a paper result. Opposite open half-planes give a turn strictly less than a full turn. -/
theorem ccwTurn_eR_eL {eR eL : ℂ} (hR : 0 < eR.re) (hL : eL.re < 0) :
    0 < ccwTurn eR eL ∧ ccwTurn eR eL < 2 * Real.pi := by
  have hr := ccwPhase_range_right hR
  have hl := ccwPhase_range_left hL
  have hrl : ccwPhase eR < ccwPhase eL := hr.2.trans hl.1
  rw [ccwTurn_eq_phaseTurn, phaseTurn, ite_eq_left hrl]
  constructor <;> linarith [hr.1, hl.2]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: angular sectors at seam vertices);
not a paper result. The above sector is the open phase interval between the seam rays. -/
private theorem aboveSector_phase {sL sR : ℝ} {u : ℂ} (hu : AboveSector sL sR u) :
    ccwPhase (⟨1, sR⟩ : ℂ) < ccwPhase u ∧
      ccwPhase u < ccwPhase (⟨-1, -sL⟩ : ℂ) := by
  have hr := ccwPhase_range_right (z := (⟨1, sR⟩ : ℂ)) (by norm_num)
  have hl := ccwPhase_range_left (z := (⟨-1, -sL⟩ : ℂ)) (by norm_num)
  rcases lt_trichotomy u.re 0 with hn | he | hp
  · have hU := ccwPhase_range_left hn
    have hs : u.im / u.re < sL := (div_lt_iff_of_neg hn).mpr (hu.2.1 hn)
    have hat := Real.arctan_lt_arctan_iff.mpr hs
    refine ⟨hr.2.trans hU.1, ?_⟩
    rw [ccwPhase_left hn, ccwPhase_left (z := (⟨-1, -sL⟩ : ℂ)) (by norm_num)]
    simp only [div_neg, div_one, neg_neg]
    linarith
  · rw [ccwPhase_up he (hu.2.2 he)]
    exact ⟨hr.2, hl.1⟩
  · have hU := ccwPhase_range_right hp
    have hs : sR < u.im / u.re := (lt_div_iff₀ hp).mpr (hu.1 hp)
    have hat := Real.arctan_lt_arctan_iff.mpr hs
    refine ⟨?_, hU.2.trans hl.1⟩
    rw [ccwPhase_right hp, ccwPhase_right (z := (⟨1, sR⟩ : ℂ)) (by norm_num)]
    simp only [div_one]
    linarith

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: angular sectors at seam vertices);
not a paper result. The below sector is outside the closed interval between seam phases. -/
private theorem belowSector_phase {sL sR : ℝ} {u : ℂ} (hu : BelowSector sL sR u) :
    ccwPhase u < ccwPhase (⟨1, sR⟩ : ℂ) ∨
      ccwPhase (⟨-1, -sL⟩ : ℂ) < ccwPhase u := by
  rcases lt_trichotomy u.re 0 with hn | he | hp
  · right
    have hs : sL < u.im / u.re := (lt_div_iff_of_neg hn).mpr (hu.2.1 hn)
    have hat := Real.arctan_lt_arctan_iff.mpr hs
    rw [ccwPhase_left hn, ccwPhase_left (z := (⟨-1, -sL⟩ : ℂ)) (by norm_num)]
    simp only [div_neg, div_one, neg_neg]
    linarith
  · left
    rw [ccwPhase_down he (hu.2.2 he)]
    exact (ccwPhase_range_right (z := (⟨1, sR⟩ : ℂ)) (by norm_num)).1
  · left
    have hs : u.im / u.re < sR := (div_lt_iff₀ hp).mpr (hu.1 hp)
    have hat := Real.arctan_lt_arctan_iff.mpr hs
    rw [ccwPhase_right hp, ccwPhase_right (z := (⟨1, sR⟩ : ℂ)) (by norm_num)]
    simp only [div_one]
    linarith

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: angular sectors at seam vertices);
not a paper result. Above-seam directions occur strictly before the left boundary ray. -/
theorem aboveSector_turn {sL sR : ℝ} {u : ℂ} (hu : AboveSector sL sR u) :
    0 < ccwTurn (⟨1, sR⟩ : ℂ) u ∧
      ccwTurn (⟨1, sR⟩ : ℂ) u <
        ccwTurn (⟨1, sR⟩ : ℂ) (⟨-1, -sL⟩ : ℂ) := by
  obtain ⟨hRu, huL⟩ := aboveSector_phase hu
  have hRL := hRu.trans huL
  rw [ccwTurn_eq_phaseTurn, ccwTurn_eq_phaseTurn]
  simp only [phaseTurn, ite_eq_left hRu, ite_eq_left hRL]
  constructor <;> linarith

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: angular sectors at seam vertices);
not a paper result. Below-seam directions occur strictly after the left boundary ray. -/
theorem belowSector_turn {sL sR : ℝ} {u : ℂ} (hu : BelowSector sL sR u) :
    ccwTurn (⟨1, sR⟩ : ℂ) (⟨-1, -sL⟩ : ℂ) <
        ccwTurn (⟨1, sR⟩ : ℂ) u ∧
      ccwTurn (⟨1, sR⟩ : ℂ) u ≤ 2 * Real.pi := by
  have hr := ccwPhase_range_right (z := (⟨1, sR⟩ : ℂ)) (by norm_num)
  have hl := ccwPhase_range_left (z := (⟨-1, -sL⟩ : ℂ)) (by norm_num)
  have hRL := hr.2.trans hl.1
  have hU := ccwPhase_range u
  rw [ccwTurn_eq_phaseTurn, ccwTurn_eq_phaseTurn]
  rcases belowSector_phase hu with hbefore | hafter
  · have hnot := not_lt.mpr hbefore.le
    simp only [phaseTurn, ite_eq_left hRL, ite_eq_right hnot]
    constructor <;> linarith [hr.1, hl.2, hU.1]
  · have hRu := hRL.trans hafter
    simp only [phaseTurn, ite_eq_left hRL, ite_eq_left hRu]
    constructor <;> linarith [hr.1, hU.2]

end DirectedDistances.PlanarMap
