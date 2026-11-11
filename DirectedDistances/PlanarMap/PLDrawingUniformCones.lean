/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.CcwPiecewiseLinear
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Uniform coordinate bounds for transferred dart wedges

Pure coordinate helpers toward the Q-M0-repr face correspondence; these are not
paper results. The wedge convention here is the left wedge
`p + t * (dir + ε * I * dir)` used by `PLDrawing.dartBorders`. -/

public section

namespace DirectedDistances.PlanarMap

noncomputable section

/-- The linear coordinate map on one side of the past transfer. Helper toward
the Q-M0-repr face correspondence; not a paper result. -/
@[expose] def pastLinear (a b : ℝ) (z : ℂ) : ℂ :=
  ⟨-a * z.re, -z.im + b * z.re⟩

/-- The aperture permitted by the real-coordinate cut for a direction. Helper
toward the Q-M0-repr face correspondence; not a paper result. -/
def pastConeEta (u : ℂ) : ℝ :=
  if u.re = 0 then 1 else |u.re| / (2 * (|u.im| + 1))

/-- Whether the positive-real-side piece controls a direction's left wedge.
For a vertical direction, the sign of `-(u.im)` is the sign of `(I*u).re`.
Helper toward the Q-M0-repr face correspondence; not a paper result. -/
noncomputable def pastConeUsesPositivePiece (u : ℂ) : Prop := by
  classical
  exact if u.re = 0 then 0 < -u.im else 0 < u.re

/-- The selected horizontal slope. Helper toward the Q-M0-repr face
correspondence; not a paper result. -/
noncomputable def pastConeSlopeA (aPos aNeg : ℝ) (u : ℂ) : ℝ := by
  classical
  exact if pastConeUsesPositivePiece u then aPos else aNeg

/-- The selected shear slope. Helper toward the Q-M0-repr face correspondence;
not a paper result. -/
noncomputable def pastConeSlopeB (bPos bNeg : ℝ) (u : ℂ) : ℝ := by
  classical
  exact if pastConeUsesPositivePiece u then bPos else bNeg

/-- The image direction under the piecewise-linear past map. Helper toward the
Q-M0-repr face correspondence; not a paper result. -/
def pastConeV (aPos aNeg bPos bNeg : ℝ) (u : ℂ) : ℂ :=
  pastDirection aPos aNeg bPos bNeg u

/-- The image of the quarter-turn direction under the side selected by `u`.
Helper toward the Q-M0-repr face correspondence; not a paper result. -/
def pastConeW (aPos aNeg bPos bNeg : ℝ) (u : ℂ) : ℂ :=
  pastLinear (pastConeSlopeA aPos aNeg u) (pastConeSlopeB bPos bNeg u)
    (Complex.I * u)

/-- Euclidean dot product of the coordinate pairs. -/
def pastDot (v w : ℂ) : ℝ := v.re * w.re + v.im * w.im

/-- The coefficient parallel to `v`; the denominator is `|v|^2`. Helper
toward the Q-M0-repr face correspondence; not a paper result. -/
def pastConeAlpha (v w : ℂ) : ℝ := pastDot v w / Complex.normSq v

/-- The coefficient in the `I*v` direction. Helper toward the Q-M0-repr face
correspondence; not a paper result. -/
def pastConeBeta (v w : ℂ) : ℝ := planarCross v w / Complex.normSq v

/-- One positive radius controls the source strip and both image parameters.
Helper toward the Q-M0-repr face correspondence; not a paper result. -/
def pastConeRadius (aPos aNeg bPos bNeg c r Delta : ℝ) (u : ℂ) : ℝ :=
  min 1 (min (pastConeEta u)
    (min (1 / (2 * (|pastConeAlpha (pastConeV aPos aNeg bPos bNeg u)
      (pastConeW aPos aNeg bPos bNeg u)| + 1)))
      (min (r / (|u.re| + |u.im| + 1))
        (min (c * Delta / 2)
          (Delta / (2 * (pastConeBeta (pastConeV aPos aNeg bPos bNeg u)
            (pastConeW aPos aNeg bPos bNeg u) + 1)))))))

/-- On the vertical axis the two pieces of the past map agree. Helper toward
the Q-M0-repr face correspondence; not a paper result. -/
theorem pastDirection_vertical (aPos aNeg bPos bNeg y : ℝ) :
    pastDirection aPos aNeg bPos bNeg (Complex.I * (y : ℂ)) =
      -Complex.I * (y : ℂ) := by
  apply Complex.ext <;> simp [pastDirection, Complex.mul_re, Complex.mul_im] <;> ring

/-- The selected linear piece at `u` agrees with `pastDirection`, including on
the vertical axis. Helper toward the Q-M0-repr face correspondence; not a paper
result. -/
theorem pastConeV_eq_selectedLinear (aPos aNeg bPos bNeg : ℝ) (u : ℂ) :
    pastConeV aPos aNeg bPos bNeg u =
      pastLinear (pastConeSlopeA aPos aNeg u) (pastConeSlopeB bPos bNeg u) u := by
  classical
  by_cases hp : 0 < u.re
  · have hn : u.re ≠ 0 := ne_of_gt hp
    simp [pastConeV, pastConeSlopeA, pastConeSlopeB,
      pastConeUsesPositivePiece, pastDirection, pastLinear, hp, hn]
  · by_cases hm : u.re < 0
    · have hn : u.re ≠ 0 := ne_of_lt hm
      simp [pastConeV, pastConeSlopeA, pastConeSlopeB,
        pastConeUsesPositivePiece, pastDirection, pastLinear, hp, hm, hn]
    · have hz : u.re = 0 := by linarith
      apply Complex.ext <;>
        simp [pastConeV, pastConeSlopeA, pastConeSlopeB,
          pastConeUsesPositivePiece, pastDirection, pastLinear, hz] <;> ring

/-- Positive-slope pieces do not send a nonzero direction to zero. Helper
toward the Q-M0-repr face correspondence; not a paper result. -/
theorem pastDirection_ne_zero {aPos aNeg bPos bNeg : ℝ}
    (haPos : 0 < aPos) (haNeg : 0 < aNeg) {u : ℂ} (hu : u ≠ 0) :
    pastDirection aPos aNeg bPos bNeg u ≠ 0 := by
  classical
  intro hv
  have hre := congrArg Complex.re hv
  have him := congrArg Complex.im hv
  by_cases hp : 0 < u.re
  · simp only [pastDirection, if_pos hp, Complex.zero_re, Complex.zero_im] at hre him
    have hz : u.re = 0 := by
      have := mul_eq_zero.mp hre
      exact this.resolve_left (neg_ne_zero.mpr (ne_of_gt haPos))
    have hi : u.im = 0 := by rw [hz] at him; linarith
    exact hu (Complex.ext hz hi)
  · have hn : ¬ 0 < u.re := hp
    simp only [pastDirection, if_neg hn, Complex.zero_re, Complex.zero_im] at hre him
    have hz : u.re = 0 := by
      have := mul_eq_zero.mp hre
      exact this.resolve_left (neg_ne_zero.mpr (ne_of_gt haNeg))
    have hi : u.im = 0 := by rw [hz] at him; linarith
    exact hu (Complex.ext hz hi)

/-- Coordinate decomposition in the basis `v, I*v`. Helper toward the
Q-M0-repr face correspondence; not a paper result. -/
theorem pastCone_decompose (v w : ℂ) (hv : v ≠ 0) :
    w = (pastConeAlpha v w : ℂ) * v +
      (pastConeBeta v w : ℂ) * (Complex.I * v) := by
  have hden : Complex.normSq v ≠ 0 := (Complex.normSq_pos.mpr hv).ne'
  have hden' : v.re ^ 2 + v.im ^ 2 ≠ 0 := by
    simpa [Complex.normSq_apply, pow_two] using hden
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, zero_add]
    dsimp [pastConeAlpha, pastConeBeta, pastDot, planarCross]
    rw [Complex.normSq_apply]
    field_simp [hden']
    <;> ring
  · simp only [Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, zero_add]
    dsimp [pastConeAlpha, pastConeBeta, pastDot, planarCross]
    rw [Complex.normSq_apply]
    field_simp [hden']
    <;> ring

/-- The cross coefficient is the selected positive slope times `|u|^2`.
Helper toward the Q-M0-repr face correspondence; not a paper result. -/
theorem pastCone_cross_eq (aPos aNeg bPos bNeg : ℝ) (u : ℂ) :
    planarCross (pastConeV aPos aNeg bPos bNeg u)
      (pastConeW aPos aNeg bPos bNeg u) =
        pastConeSlopeA aPos aNeg u * Complex.normSq u := by
  rw [pastConeV_eq_selectedLinear]
  change planarCross
      ⟨-pastConeSlopeA aPos aNeg u * u.re,
        -u.im + pastConeSlopeB bPos bNeg u * u.re⟩
      ⟨-pastConeSlopeA aPos aNeg u * (Complex.I * u).re,
        -(Complex.I * u).im + pastConeSlopeB bPos bNeg u * (Complex.I * u).re⟩ = _
  rw [planarCross_pastLinear]
  rw [show planarCross u (Complex.I * u) = Complex.normSq u by
    simp only [planarCross, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    rw [Complex.normSq_apply]
    ring]

/-- The transverse coefficient is positive for positive slopes and nonzero `u`.
Helper toward the Q-M0-repr face correspondence; not a paper result. -/
theorem pastConeBeta_pos {aPos aNeg bPos bNeg : ℝ}
    (haPos : 0 < aPos) (haNeg : 0 < aNeg) {u : ℂ} (hu : u ≠ 0) :
    0 < pastConeBeta (pastConeV aPos aNeg bPos bNeg u)
      (pastConeW aPos aNeg bPos bNeg u) := by
  rw [pastConeBeta, pastCone_cross_eq]
  have ha : 0 < pastConeSlopeA aPos aNeg u := by
    by_cases h : pastConeUsesPositivePiece u
    · simp [pastConeSlopeA, h, haPos]
    · simp [pastConeSlopeA, h, haNeg]
  have huN : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu
  have hvN : 0 < Complex.normSq (pastConeV aPos aNeg bPos bNeg u) :=
    Complex.normSq_pos.mpr (pastDirection_ne_zero haPos haNeg hu)
  exact div_pos (mul_pos ha huN) hvN

/-- Evaluation on the positive-real branch. Helper toward the Q-M0-repr face
correspondence; not a paper result. -/
theorem pastDirection_eq_pastLinear_of_pos
    (aPos aNeg bPos bNeg : ℝ) {z : ℂ} (hz : 0 < z.re) :
    pastDirection aPos aNeg bPos bNeg z = pastLinear aPos bPos z := by
  simp [pastDirection, pastLinear, hz]

/-- Evaluation on the negative-real branch. Helper toward the Q-M0-repr face
correspondence; not a paper result. -/
theorem pastDirection_eq_pastLinear_of_neg
    (aPos aNeg bPos bNeg : ℝ) {z : ℂ} (hz : z.re < 0) :
    pastDirection aPos aNeg bPos bNeg z = pastLinear aNeg bNeg z := by
  have hnot : ¬ 0 < z.re := not_lt.mpr hz.le
  simp [pastDirection, pastLinear, hnot]

/-- Evaluation on the central line; the two pieces agree there. Helper toward
the Q-M0-repr face correspondence; not a paper result. -/
theorem pastDirection_eq_pastLinear_of_zero
    (aPos aNeg bPos bNeg : ℝ) {z : ℂ} (hz : z.re = 0) :
    pastDirection aPos aNeg bPos bNeg z = pastLinear aNeg bNeg z := by
  simp [pastDirection, pastLinear, hz]

/-- The piecewise-linear past map commutes with multiplication by a positive
real scalar. Helper toward the Q-M0-repr face correspondence; not a paper
result. -/
theorem pastDirection_smul_pos (aPos aNeg bPos bNeg t : ℝ) (ht : 0 < t)
    (z : ℂ) :
    pastDirection aPos aNeg bPos bNeg ((t : ℂ) * z) =
      (t : ℂ) * pastDirection aPos aNeg bPos bNeg z := by
  classical
  by_cases hp : 0 < z.re
  · have htp : 0 < ((t : ℂ) * z).re := by
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] using mul_pos ht hp
    rw [pastDirection_eq_pastLinear_of_pos aPos aNeg bPos bNeg htp,
      pastDirection_eq_pastLinear_of_pos aPos aNeg bPos bNeg hp]
    apply Complex.ext <;> simp [pastLinear, Complex.mul_re, Complex.mul_im] <;> ring
  · by_cases hm : z.re < 0
    · have htn : ((t : ℂ) * z).re < 0 := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
        exact mul_neg_of_pos_of_neg ht hm
      rw [pastDirection_eq_pastLinear_of_neg aPos aNeg bPos bNeg htn,
        pastDirection_eq_pastLinear_of_neg aPos aNeg bPos bNeg hm]
      apply Complex.ext <;> simp [pastLinear, Complex.mul_re, Complex.mul_im] <;> ring
    · have hz : z.re = 0 := by linarith
      have htz : ((t : ℂ) * z).re = 0 := by
        simp [Complex.mul_re, hz]
      rw [pastDirection_eq_pastLinear_of_zero aPos aNeg bPos bNeg htz,
        pastDirection_eq_pastLinear_of_zero aPos aNeg bPos bNeg hz]
      apply Complex.ext <;> simp [pastLinear, Complex.mul_re, Complex.mul_im, hz, htz] <;> ring

/-- A sufficiently narrow left wedge stays in the selected linear piece,
including for vertical directions. Helper toward the Q-M0-repr face
correspondence; not a paper result. -/
theorem pastDirection_perturbed_selected
    (aPos aNeg bPos bNeg : ℝ) (u : ℂ) (hu : u ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hεη : ε < pastConeEta u) :
    pastDirection aPos aNeg bPos bNeg (u + (ε : ℂ) * Complex.I * u) =
      pastLinear (pastConeSlopeA aPos aNeg u) (pastConeSlopeB bPos bNeg u)
        (u + (ε : ℂ) * Complex.I * u) := by
  classical
  by_cases hz : u.re = 0
  · have him : u.im ≠ 0 := by
      intro hi
      exact hu (Complex.ext hz hi)
    by_cases hside : 0 < -u.im
    · have hnew : 0 < (u + (ε : ℂ) * Complex.I * u).re := by
        have hre : (u + (ε : ℂ) * Complex.I * u).re = u.re - ε * u.im := by
          simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im]
          ring
        rw [hre, hz]
        nlinarith [mul_pos hε hside]
      have hsel : pastConeUsesPositivePiece u := by
        simp [pastConeUsesPositivePiece, hz, hside]
      rw [pastDirection_eq_pastLinear_of_pos aPos aNeg bPos bNeg hnew]
      simp [pastConeSlopeA, pastConeSlopeB, hsel]
    · have hside' : 0 < u.im := by
        by_contra hn
        have hle : u.im ≤ 0 := le_of_not_gt hn
        have hge : 0 ≤ u.im := by linarith [le_of_not_gt hside]
        exact him (le_antisymm hle hge)
      have hnew : (u + (ε : ℂ) * Complex.I * u).re < 0 := by
        have hre : (u + (ε : ℂ) * Complex.I * u).re = u.re - ε * u.im := by
          simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im]
          ring
        rw [hre, hz]
        nlinarith [mul_pos hε hside']
      have hsel : ¬ pastConeUsesPositivePiece u := by
        simp [pastConeUsesPositivePiece, hz, hside]
      rw [pastDirection_eq_pastLinear_of_neg aPos aNeg bPos bNeg hnew]
      simp [pastConeSlopeA, pastConeSlopeB, hsel]
  · have hsmall0 : ε * |u.im| < |u.re| / 2 := by
      have hden : 0 < 2 * (|u.im| + 1) := by positivity
      have hmul := (lt_div_iff₀ hden).mp (by simpa [pastConeEta, hz] using hεη)
      nlinarith [abs_nonneg u.im, hε1]
    have hre : (u + (ε : ℂ) * Complex.I * u).re = u.re - ε * u.im := by
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    by_cases hp : 0 < u.re
    · have hpert : 0 < u.re - ε * u.im := by
        have himle : ε * u.im ≤ ε * |u.im| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hε.le
        have huabs : |u.re| = u.re := abs_of_pos hp
        nlinarith
      have hnew : 0 < (u + (ε : ℂ) * Complex.I * u).re := by
        rw [hre]
        exact hpert
      have hsel : pastConeUsesPositivePiece u := by
        simp [pastConeUsesPositivePiece, hz, hp]
      rw [pastDirection_eq_pastLinear_of_pos aPos aNeg bPos bNeg hnew]
      simp [pastConeSlopeA, pastConeSlopeB, hsel]
    · have hm : u.re < 0 := lt_of_le_of_ne (not_lt.mp hp) hz
      have hpert : u.re - ε * u.im < 0 := by
        have himge : -ε * |u.im| ≤ ε * u.im := by
          calc
            -ε * |u.im| = ε * (-|u.im|) := by ring
            _ ≤ ε * u.im := mul_le_mul_of_nonneg_left (neg_abs_le u.im) hε.le
        have huabs : |u.re| = -u.re := abs_of_neg hm
        nlinarith
      have hnew : (u + (ε : ℂ) * Complex.I * u).re < 0 := by
        rw [hre]
        exact hpert
      have hsel : ¬ pastConeUsesPositivePiece u := by
        simp [pastConeUsesPositivePiece, hz, hp]
      rw [pastDirection_eq_pastLinear_of_neg aPos aNeg bPos bNeg hnew]
      simp [pastConeSlopeA, pastConeSlopeB, hsel]

/-- The selected image of a small wedge is exactly `t * (v + ε*w)`.
Helper toward the Q-M0-repr face correspondence; not a paper result. -/
theorem pastCone_map_wedge
    (aPos aNeg bPos bNeg t ε : ℝ) (ht : 0 < t) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (u : ℂ) (hu : u ≠ 0)
    (hεη : ε < pastConeEta u) :
    pastDirection aPos aNeg bPos bNeg
      ((t : ℂ) * (u + (ε : ℂ) * Complex.I * u)) =
        (t : ℂ) * (pastConeV aPos aNeg bPos bNeg u +
          (ε : ℂ) * pastConeW aPos aNeg bPos bNeg u) := by
  rw [pastDirection_smul_pos aPos aNeg bPos bNeg t ht]
  rw [pastDirection_perturbed_selected aPos aNeg bPos bNeg u hu ε hε hε1 hεη]
  rw [pastConeV_eq_selectedLinear]
  have hadd : pastLinear (pastConeSlopeA aPos aNeg u)
      (pastConeSlopeB bPos bNeg u) (u + (ε : ℂ) * Complex.I * u) =
        pastLinear (pastConeSlopeA aPos aNeg u)
          (pastConeSlopeB bPos bNeg u) u +
        (ε : ℂ) * pastLinear (pastConeSlopeA aPos aNeg u)
          (pastConeSlopeB bPos bNeg u) (Complex.I * u) := by
    apply Complex.ext <;> simp [pastLinear, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] <;> ring
  rw [hadd]
  rfl

/-- The selected horizontal slope is positive when both past slopes are
positive. Helper toward the Q-M0-repr face correspondence; not a paper result. -/
theorem pastConeSlopeA_pos {aPos aNeg : ℝ} (u : ℂ)
    (haPos : 0 < aPos) (haNeg : 0 < aNeg) :
    0 < pastConeSlopeA aPos aNeg u := by
  by_cases h : pastConeUsesPositivePiece u
  · simp [pastConeSlopeA, h, haPos]
  · simp [pastConeSlopeA, h, haNeg]

/-- Positivity and the six cap bounds for the uniform cone radius. Helper
toward the Q-M0-repr face correspondence; not a paper result. -/
theorem pastConeRadius_pos_caps (aPos aNeg bPos bNeg c r Delta : ℝ)
    (u : ℂ) (haPos : 0 < aPos) (haNeg : 0 < aNeg)
    (hc : 0 < c) (hr : 0 < r) (hDelta : 0 < Delta) (hu : u ≠ 0) :
    0 < pastConeRadius aPos aNeg bPos bNeg c r Delta u ∧
      pastConeRadius aPos aNeg bPos bNeg c r Delta u ≤ 1 ∧
      pastConeRadius aPos aNeg bPos bNeg c r Delta u ≤ pastConeEta u ∧
      pastConeRadius aPos aNeg bPos bNeg c r Delta u ≤
        1 / (2 * (|pastConeAlpha (pastConeV aPos aNeg bPos bNeg u)
          (pastConeW aPos aNeg bPos bNeg u)| + 1)) ∧
      pastConeRadius aPos aNeg bPos bNeg c r Delta u ≤
        r / (|u.re| + |u.im| + 1) ∧
      pastConeRadius aPos aNeg bPos bNeg c r Delta u ≤ c * Delta / 2 ∧
      pastConeRadius aPos aNeg bPos bNeg c r Delta u ≤
        Delta / (2 * (pastConeBeta (pastConeV aPos aNeg bPos bNeg u)
          (pastConeW aPos aNeg bPos bNeg u) + 1)) := by
  have hEta : 0 < pastConeEta u := by
    by_cases hz : u.re = 0
    · simp [pastConeEta, hz]
    · simp only [pastConeEta, hz, ↓reduceIte]
      exact div_pos (abs_pos.mpr hz) (by positivity)
  have hV : pastConeV aPos aNeg bPos bNeg u ≠ 0 :=
    pastDirection_ne_zero haPos haNeg hu
  have hBeta : 0 < pastConeBeta
      (pastConeV aPos aNeg bPos bNeg u) (pastConeW aPos aNeg bPos bNeg u) :=
    pastConeBeta_pos haPos haNeg hu
  have hBetaDen : 0 < 2 *
      (pastConeBeta (pastConeV aPos aNeg bPos bNeg u)
        (pastConeW aPos aNeg bPos bNeg u) + 1) := by positivity
  have hRden : 0 < |u.re| + |u.im| + 1 := by positivity
  have hAlphaCap : 0 < 1 / (2 *
      (|pastConeAlpha (pastConeV aPos aNeg bPos bNeg u)
        (pastConeW aPos aNeg bPos bNeg u)| + 1)) := by
    apply div_pos one_pos
    positivity
  have hRcap : 0 < r / (|u.re| + |u.im| + 1) := div_pos hr hRden
  have hCcap : 0 < c * Delta / 2 := by positivity
  have hBetacap : 0 < Delta / (2 *
      (pastConeBeta (pastConeV aPos aNeg bPos bNeg u)
        (pastConeW aPos aNeg bPos bNeg u) + 1)) :=
    div_pos hDelta hBetaDen
  constructor
  · unfold pastConeRadius
    positivity
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold pastConeRadius
      exact min_le_left _ _
    · unfold pastConeRadius
      exact (min_le_right _ _).trans (min_le_left _ _)
    · unfold pastConeRadius
      exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · unfold pastConeRadius
      exact (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
    · unfold pastConeRadius
      exact (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    · unfold pastConeRadius
      exact (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans
          (min_le_right _ _))))

/-- Decomposition of the image of a wedge in the target direction and its
quarter-turn. The explicit denominators are nonzero hypotheses so the
componentwise field simplification is controlled. Helper toward the
Q-M0-repr face correspondence; not a paper result. -/
theorem pastCone_scaled_decompose (v w : ℂ) (alpha beta t eps c : ℝ)
    (hdec : w = (alpha : ℂ) * v + (beta : ℂ) * (Complex.I * v))
    (hc : c ≠ 0) (hfac : 1 + alpha * eps ≠ 0) :
    (t : ℂ) * (v + (eps : ℂ) * w) =
      ((t * (1 + alpha * eps) / c : ℝ) : ℂ) *
        ((c : ℂ) * v +
          ((beta * eps / (1 + alpha * eps) : ℝ) : ℂ) *
            (Complex.I * ((c : ℂ) * v))) := by
  have hfac' : 1 + eps * alpha ≠ 0 := by
    rw [mul_comm eps alpha]
    exact hfac
  rw [hdec]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, zero_add, add_zero] <;>
    field_simp [hc, hfac, hfac'] <;> ring

/-- Uniform transfer of a sufficiently small left wedge under the past
piecewise-linear direction map. The radius gives six positive caps: the
unit cap, aperture cap, denominator cap, strip cap, scale cap, and transverse
cap. Helper toward the Q-M0-repr face correspondence; not a paper result. -/
theorem pastCone_uniform_forward (aPos aNeg bPos bNeg c r Delta : ℝ)
    (u : ℂ) (haPos : 0 < aPos) (haNeg : 0 < aNeg)
    (hc : 0 < c) (hr : 0 < r) (hDelta : 0 < Delta) (hu : u ≠ 0) :
    (0 < pastConeRadius aPos aNeg bPos bNeg c r Delta u ∧
      pastConeRadius aPos aNeg bPos bNeg c r Delta u ≤ 1 ∧
      pastConeRadius aPos aNeg bPos bNeg c r Delta u ≤ pastConeEta u ∧
      pastConeRadius aPos aNeg bPos bNeg c r Delta u ≤
        1 / (2 * (|pastConeAlpha (pastConeV aPos aNeg bPos bNeg u)
          (pastConeW aPos aNeg bPos bNeg u)| + 1)) ∧
      pastConeRadius aPos aNeg bPos bNeg c r Delta u ≤
        r / (|u.re| + |u.im| + 1) ∧
      pastConeRadius aPos aNeg bPos bNeg c r Delta u ≤ c * Delta / 2 ∧
      pastConeRadius aPos aNeg bPos bNeg c r Delta u ≤
        Delta / (2 * (pastConeBeta (pastConeV aPos aNeg bPos bNeg u)
          (pastConeW aPos aNeg bPos bNeg u) + 1))) ∧
    (∀ t eps : ℝ, 0 < t → t < pastConeRadius aPos aNeg bPos bNeg c r Delta u →
      0 < eps → eps < pastConeRadius aPos aNeg bPos bNeg c r Delta u →
      |((t : ℂ) * (u + (eps : ℂ) * Complex.I * u)).re| < r ∧
      1 / 2 < 1 + pastConeAlpha
        (pastConeV aPos aNeg bPos bNeg u) (pastConeW aPos aNeg bPos bNeg u) * eps ∧
      1 + pastConeAlpha
        (pastConeV aPos aNeg bPos bNeg u) (pastConeW aPos aNeg bPos bNeg u) * eps < 3 / 2 ∧
      let q : ℂ := (c : ℂ) * pastConeV aPos aNeg bPos bNeg u
      let s : ℝ := t * (1 + pastConeAlpha
        (pastConeV aPos aNeg bPos bNeg u) (pastConeW aPos aNeg bPos bNeg u) * eps) / c
      let eps' : ℝ := pastConeBeta
        (pastConeV aPos aNeg bPos bNeg u) (pastConeW aPos aNeg bPos bNeg u) * eps /
          (1 + pastConeAlpha
            (pastConeV aPos aNeg bPos bNeg u) (pastConeW aPos aNeg bPos bNeg u) * eps)
      0 < s ∧ s < Delta ∧ 0 < eps' ∧ eps' < Delta ∧
      pastDirection aPos aNeg bPos bNeg
          ((t : ℂ) * (u + (eps : ℂ) * Complex.I * u)) =
        (s : ℂ) * (q + (eps' : ℂ) * (Complex.I * q))) := by
  have hcaps := pastConeRadius_pos_caps aPos aNeg bPos bNeg c r Delta u
    haPos haNeg hc hr hDelta hu
  rcases hcaps with ⟨hrho, hcap1, hcapEta, hcapAlpha, hcapR, hcapC, hcapBeta⟩
  refine ⟨⟨hrho, hcap1, hcapEta, hcapAlpha, hcapR, hcapC, hcapBeta⟩, ?_⟩
  intro t eps ht htR heps hepsR
  dsimp only
  let v := pastConeV aPos aNeg bPos bNeg u
  let w := pastConeW aPos aNeg bPos bNeg u
  let alpha := pastConeAlpha v w
  let beta := pastConeBeta v w
  have hv : v ≠ 0 := pastDirection_ne_zero haPos haNeg hu
  have hbeta : 0 < beta := by simpa [beta, v, w] using
    (pastConeBeta_pos haPos haNeg hu)
  have hBetaPlus : 0 < beta + 1 := by linarith
  have hEta : eps < pastConeEta u := hepsR.trans_le hcapEta
  have hepsOne : eps ≤ 1 := (hepsR.trans_le hcap1).le
  have hAlphaCap : eps < 1 / (2 * (|alpha| + 1)) := by
    simpa [alpha, v, w] using hepsR.trans_le hcapAlpha
  have hAlphaProduct : eps * (2 * (|alpha| + 1)) < 1 :=
    (lt_div_iff₀ (by positivity)).mp hAlphaCap
  have hAbsAlphaEps : |alpha| * eps < 1 / 2 := by
    nlinarith [hAlphaProduct, heps]
  have hFactorLower : 1 / 2 < 1 + alpha * eps := by
    have hlow : -|alpha| * eps ≤ alpha * eps :=
      mul_le_mul_of_nonneg_right (neg_abs_le alpha) heps.le
    nlinarith [hAbsAlphaEps, hlow]
  have hFactorUpper : 1 + alpha * eps < 3 / 2 := by
    have hupp : alpha * eps ≤ |alpha| * eps :=
      mul_le_mul_of_nonneg_right (le_abs_self alpha) heps.le
    nlinarith [hAbsAlphaEps, hupp]
  have hFactorPos : 0 < 1 + alpha * eps := by linarith
  have hAlphaDen : 0 < |u.re| + |u.im| + 1 := by positivity
  have htStripProduct : t * (|u.re| + |u.im| + 1) < r :=
    (lt_div_iff₀ hAlphaDen).mp (htR.trans_le hcapR)
  have hpert : ((eps : ℂ) * Complex.I * u).re = -eps * u.im := by
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have hinner : (u + (eps : ℂ) * Complex.I * u).re =
      u.re - eps * u.im := by
    rw [Complex.add_re, hpert]
    ring
  have hreal : ((t : ℂ) * (u + (eps : ℂ) * Complex.I * u)).re =
      t * (u.re - eps * u.im) := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hinner]
    simp
  have hAbsInside : |u.re - eps * u.im| ≤ |u.re| + |u.im| := by
    calc
      |u.re - eps * u.im| ≤ |u.re| + |eps * u.im| := by
        simpa using abs_sub_le u.re (0 : ℝ) (eps * u.im)
      _ = |u.re| + eps * |u.im| := by rw [abs_mul, abs_of_pos heps]
      _ ≤ |u.re| + |u.im| := by nlinarith [abs_nonneg u.im]
  have hstrip : |((t : ℂ) * (u + (eps : ℂ) * Complex.I * u)).re| < r := by
    rw [hreal, abs_mul, abs_of_pos ht]
    calc
      t * |u.re - eps * u.im| ≤ t * (|u.re| + |u.im| + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith [hAbsInside]) ht.le
      _ < r := htStripProduct
  have hBetaCap : eps < Delta / (2 * (beta + 1)) := by
    simpa [beta, v, w] using hepsR.trans_le hcapBeta
  have hBetaSmallProduct : eps * (2 * (beta + 1)) < Delta :=
    (lt_div_iff₀ (by positivity)).mp hBetaCap
  have hBetaEpsSmall : beta * eps < Delta / 2 := by
    nlinarith [hBetaSmallProduct, heps, hbeta]
  have hSCap : t < c * Delta / 2 := htR.trans_le hcapC
  have hTFactor : t * (1 + alpha * eps) < c * Delta := by
    calc
      t * (1 + alpha * eps) < (c * Delta / 2) * (1 + alpha * eps) :=
        mul_lt_mul_of_pos_right hSCap hFactorPos
      _ < (c * Delta / 2) * (3 / 2) :=
        mul_lt_mul_of_pos_left hFactorUpper (by positivity)
      _ < c * Delta := by nlinarith [mul_pos hc hDelta]
  have hsPos : 0 < t * (1 + alpha * eps) / c :=
    div_pos (mul_pos ht hFactorPos) hc
  have hsLt : t * (1 + alpha * eps) / c < Delta := by
    apply (div_lt_iff₀ hc).2
    nlinarith [hTFactor]
  have hepsPrimePos : 0 < beta * eps / (1 + alpha * eps) :=
    div_pos (mul_pos hbeta heps) hFactorPos
  have hBetaTimesFactor : beta * eps < (2 * beta * eps) *
      (1 + alpha * eps) := by
    have hh := mul_lt_mul_of_pos_left hFactorLower (mul_pos hbeta heps)
    nlinarith [hh]
  have hepsPrimeLtTwo : beta * eps / (1 + alpha * eps) < 2 * beta * eps :=
    (div_lt_iff₀ hFactorPos).2 hBetaTimesFactor
  have hepsPrimeLt : beta * eps / (1 + alpha * eps) < Delta := by
    calc
      beta * eps / (1 + alpha * eps) < 2 * beta * eps := hepsPrimeLtTwo
      _ < Delta := by linarith [hBetaEpsSmall]
  have hdec : w = (alpha : ℂ) * v + (beta : ℂ) * (Complex.I * v) :=
    pastCone_decompose v w hv
  have hfacne : 1 + alpha * eps ≠ 0 := ne_of_gt hFactorPos
  have hscaled := pastCone_scaled_decompose v w alpha beta t eps c hdec
    (ne_of_gt hc) hfacne
  have hmap := pastCone_map_wedge aPos aNeg bPos bNeg t eps ht heps
    hepsOne u hu hEta
  refine ⟨hstrip, hFactorLower, hFactorUpper, hsPos, hsLt,
    hepsPrimePos, hepsPrimeLt, ?_⟩
  simpa [v, w, alpha, beta] using hmap.trans hscaled

/-- The explicit inverse pieces recover the input direction on the target strip
`|h.re| < r * min(aPos,aNeg)`, including `h.re = 0`. Helper toward the
Q-M0-repr face correspondence; not a paper result. -/
theorem pastDirection_inverse_on_strip
    (aPos aNeg bPos bNeg r : ℝ) (haPos : 0 < aPos) (haNeg : 0 < aNeg)
    (hr : 0 < r) (h : ℂ)
    (_hstrip : |h.re| < r * min aPos aNeg) :
    pastDirection (1 / aNeg) (1 / aPos) (-bNeg / aNeg) (-bPos / aPos)
      (pastDirection aPos aNeg bPos bNeg h) = h := by
  classical
  by_cases hp : 0 < h.re
  · have hcond : ¬ aPos * h.re < 0 := not_lt.mpr (le_of_lt (mul_pos haPos hp))
    apply Complex.ext <;>
      simp [pastDirection, hp, hcond, Complex.mul_re, Complex.mul_im] <;>
      field_simp [ne_of_gt haPos, ne_of_gt haNeg] <;> ring
  · by_cases hm : h.re < 0
    · have hn : ¬ 0 < h.re := not_lt.mpr hm.le
      have hcond : aNeg * h.re < 0 := mul_neg_of_pos_of_neg haNeg hm
      apply Complex.ext <;>
        simp [pastDirection, hn, hcond, Complex.mul_re, Complex.mul_im] <;>
        field_simp [ne_of_gt haPos, ne_of_gt haNeg] <;> ring
    · have hz : h.re = 0 := by linarith
      apply Complex.ext <;>
        simp [pastDirection, hz, Complex.mul_re, Complex.mul_im] <;>
        field_simp [ne_of_gt haPos, ne_of_gt haNeg] <;> ring

/-- The inverse slopes cancel the two past pieces for every coordinate vector.
The strip radius in the local transfer is needed for geometric application,
but not for this coordinate identity. Helper toward the Q-M0-repr face
correspondence; not a paper result. -/
theorem pastDirection_inverse (aPos aNeg bPos bNeg : ℝ)
    (haPos : 0 < aPos) (haNeg : 0 < aNeg) (h : ℂ) :
    pastDirection (1 / aNeg) (1 / aPos) (-bNeg / aNeg) (-bPos / aPos)
      (pastDirection aPos aNeg bPos bNeg h) = h := by
  classical
  by_cases hp : 0 < h.re
  · have hcond : ¬ aPos * h.re < 0 := not_lt.mpr (le_of_lt (mul_pos haPos hp))
    apply Complex.ext <;>
      simp [pastDirection, hp, hcond, Complex.mul_re, Complex.mul_im] <;>
      field_simp [ne_of_gt haPos, ne_of_gt haNeg] <;> ring
  · by_cases hm : h.re < 0
    · have hn : ¬ 0 < h.re := not_lt.mpr hm.le
      have hcond : aNeg * h.re < 0 := mul_neg_of_pos_of_neg haNeg hm
      apply Complex.ext <;>
        simp [pastDirection, hn, hcond, Complex.mul_re, Complex.mul_im] <;>
        field_simp [ne_of_gt haPos, ne_of_gt haNeg] <;> ring
    · have hz : h.re = 0 := by linarith
      apply Complex.ext <;>
        simp [pastDirection, hz, Complex.mul_re, Complex.mul_im] <;>
      field_simp [ne_of_gt haPos, ne_of_gt haNeg] <;> ring

/-- Transparent package of the six radius caps and the forward uniform wedge
conclusions, used to state the reverse construction without duplicating its
coordinate clauses. Helper toward the Q-M0-repr face correspondence; not a
paper result. -/
def pastConeUniformPackage (aPos aNeg bPos bNeg c r Delta : ℝ) (u : ℂ) : Prop :=
  (0 < pastConeRadius aPos aNeg bPos bNeg c r Delta u ∧
    pastConeRadius aPos aNeg bPos bNeg c r Delta u ≤ 1 ∧
    pastConeRadius aPos aNeg bPos bNeg c r Delta u ≤ pastConeEta u ∧
    pastConeRadius aPos aNeg bPos bNeg c r Delta u ≤
      1 / (2 * (|pastConeAlpha (pastConeV aPos aNeg bPos bNeg u)
        (pastConeW aPos aNeg bPos bNeg u)| + 1)) ∧
    pastConeRadius aPos aNeg bPos bNeg c r Delta u ≤
      r / (|u.re| + |u.im| + 1) ∧
    pastConeRadius aPos aNeg bPos bNeg c r Delta u ≤ c * Delta / 2 ∧
    pastConeRadius aPos aNeg bPos bNeg c r Delta u ≤
      Delta / (2 * (pastConeBeta (pastConeV aPos aNeg bPos bNeg u)
        (pastConeW aPos aNeg bPos bNeg u) + 1))) ∧
  (∀ t eps : ℝ, 0 < t → t < pastConeRadius aPos aNeg bPos bNeg c r Delta u →
    0 < eps → eps < pastConeRadius aPos aNeg bPos bNeg c r Delta u →
    |((t : ℂ) * (u + (eps : ℂ) * Complex.I * u)).re| < r ∧
    1 / 2 < 1 + pastConeAlpha
      (pastConeV aPos aNeg bPos bNeg u) (pastConeW aPos aNeg bPos bNeg u) * eps ∧
    1 + pastConeAlpha
      (pastConeV aPos aNeg bPos bNeg u) (pastConeW aPos aNeg bPos bNeg u) * eps < 3 / 2 ∧
    let q : ℂ := (c : ℂ) * pastConeV aPos aNeg bPos bNeg u
    let s : ℝ := t * (1 + pastConeAlpha
      (pastConeV aPos aNeg bPos bNeg u) (pastConeW aPos aNeg bPos bNeg u) * eps) / c
    let eps' : ℝ := pastConeBeta
      (pastConeV aPos aNeg bPos bNeg u) (pastConeW aPos aNeg bPos bNeg u) * eps /
        (1 + pastConeAlpha
          (pastConeV aPos aNeg bPos bNeg u) (pastConeW aPos aNeg bPos bNeg u) * eps)
    0 < s ∧ s < Delta ∧ 0 < eps' ∧ eps' < Delta ∧
    pastDirection aPos aNeg bPos bNeg
        ((t : ℂ) * (u + (eps : ℂ) * Complex.I * u)) =
      (s : ℂ) * (q + (eps' : ℂ) * (Complex.I * q)))

/-- Reverse uniform cone transfer using the explicit inverse pieces. Its
forward package has input direction `c * D(u)`, scale `1/c`, and strip radius
`r * min(aPos,aNeg)`; the accompanying identity identifies its output
direction with `u`. Helper toward the Q-M0-repr face correspondence; not a paper
result. -/
theorem pastCone_uniform_reverse (aPos aNeg bPos bNeg c r Delta : ℝ)
    (u : ℂ) (haPos : 0 < aPos) (haNeg : 0 < aNeg)
    (hc : 0 < c) (hr : 0 < r) (hDelta : 0 < Delta) (hu : u ≠ 0) :
    let q : ℂ := (c : ℂ) * pastConeV aPos aNeg bPos bNeg u
    let r' : ℝ := r * min aPos aNeg
    ((1 / c : ℝ) : ℂ) *
        pastConeV (1 / aNeg) (1 / aPos) (-bNeg / aNeg) (-bPos / aPos) q = u ∧
      pastConeUniformPackage (1 / aNeg) (1 / aPos)
        (-bNeg / aNeg) (-bPos / aPos) (1 / c) r' Delta q := by
  dsimp only
  let q : ℂ := (c : ℂ) * pastConeV aPos aNeg bPos bNeg u
  have hq : q = (c : ℂ) * pastConeV aPos aNeg bPos bNeg u := rfl
  have hV : pastConeV aPos aNeg bPos bNeg u ≠ 0 :=
    pastDirection_ne_zero haPos haNeg hu
  have hqne : q ≠ 0 := by
    intro hzero
    have hprod : (c : ℂ) * pastConeV aPos aNeg bPos bNeg u = 0 := by
      simpa [q] using hzero
    exact hV ((mul_eq_zero.mp hprod).resolve_left (by exact_mod_cast hc.ne'))
  have hInvV : pastConeV (1 / aNeg) (1 / aPos)
      (-bNeg / aNeg) (-bPos / aPos) q = (c : ℂ) * u := by
    change pastDirection (1 / aNeg) (1 / aPos) (-bNeg / aNeg) (-bPos / aPos)
      ((c : ℂ) * pastDirection aPos aNeg bPos bNeg u) = _
    rw [pastDirection_smul_pos (1 / aNeg) (1 / aPos)
      (-bNeg / aNeg) (-bPos / aPos) c hc
      (pastDirection aPos aNeg bPos bNeg u)]
    rw [pastDirection_inverse aPos aNeg bPos bNeg haPos haNeg u]
  have hscale : ((1 / c : ℝ) : ℂ) * (c : ℂ) = 1 := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.one_re, Complex.one_im] <;>
      field_simp [ne_of_gt hc] <;> ring
  have htarget : ((1 / c : ℝ) : ℂ) *
      pastConeV (1 / aNeg) (1 / aPos) (-bNeg / aNeg) (-bPos / aPos) q = u := by
    rw [hInvV]
    calc
      ((1 / c : ℝ) : ℂ) * ((c : ℂ) * u) =
          (((1 / c : ℝ) : ℂ) * (c : ℂ)) * u := by rw [mul_assoc]
      _ = u := by rw [hscale]; simp
  have hr' : 0 < r * min aPos aNeg := mul_pos hr (lt_min haPos haNeg)
  have hc' : 0 < 1 / c := one_div_pos.mpr hc
  have hforward := pastCone_uniform_forward (1 / aNeg) (1 / aPos)
    (-bNeg / aNeg) (-bPos / aPos) (1 / c) (r * min aPos aNeg) Delta q
    (by positivity) (by positivity) hc' hr' hDelta hqne
  refine ⟨htarget, ?_⟩
  simpa only [pastConeUniformPackage, htarget, q] using hforward

end
end DirectedDistances.PlanarMap
