module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Function.L1Space.Integrable




public section
namespace DirectedDistances.Probability

open MeasureTheory
open scoped ENNReal




@[expose] noncomputable def geomTwoThirds : Measure ℕ :=
  Measure.sum fun j => ENNReal.ofReal ((2 / 3 : ℝ) * (1 / 3 : ℝ) ^ j) • Measure.dirac j

private theorem geomTwoThirds_weight_hasSum :
    HasSum (fun j : ℕ => (2 / 3 : ℝ) * (1 / 3 : ℝ) ^ j) 1 := by
  convert (hasSum_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 3 : ℝ))
    (by norm_num : (1 / 3 : ℝ) < 1)).mul_left (2 / 3) using 1
  norm_num

/-- The generic Geom(2/3) measure is a probability measure (not a paper result). -/
instance geomTwoThirds_isProbabilityMeasure : IsProbabilityMeasure geomTwoThirds := by
  unfold geomTwoThirds
  apply HasSum.isProbabilityMeasure_sum_dirac
  · intro j
    positivity
  · exact geomTwoThirds_weight_hasSum

/-- Integrals against the generic Geom(2/3) law are the corresponding atom-weighted
    sums; not a paper result. -/
theorem integral_geomTwoThirds (f : ℕ → ℝ) :
    ∫ j, f j ∂geomTwoThirds =
      ∑' j, (2 / 3 : ℝ) * (1 / 3 : ℝ) ^ j * f j := by
  unfold geomTwoThirds
  rw [integral_sum_dirac (by intro j; simp)]
  refine tsum_congr fun j => ?_
  rw [ENNReal.toReal_ofReal]
  · simp only [smul_eq_mul]
  · positivity

/-- The centered generic Geom(2/3) has mean zero; not a paper result. -/
theorem integral_geomTwoThirds_centered :
    ∫ j, ((j : ℝ) - 1 / 2) ∂geomTwoThirds = 0 := by
  rw [integral_geomTwoThirds]
  let r : ℝ := 1 / 3
  let c : ℝ := 2 / 3
  have hr : ‖r‖ < 1 := by norm_num [r]
  have hsJ : Summable (fun j : ℕ => (j : ℝ) * r ^ j) := by
    simpa [r, pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hsG : Summable (fun j : ℕ => r ^ j) := (hasSum_geometric_of_norm_lt_one hr).summable
  have hform :
      (fun j : ℕ => (2 / 3 : ℝ) * (1 / 3 : ℝ) ^ j * ((j : ℝ) - 1 / 2)) =
        (fun j : ℕ => c * ((j : ℝ) * r ^ j)) -
          (fun j : ℕ => (c / 2) * r ^ j) := by
    funext j
    dsimp [r, c]
    ring
  rw [hform]
  change tsum (fun j : ℕ => c * ((j : ℝ) * r ^ j) - (c / 2) * r ^ j) = 0
  rw [(hsJ.mul_left c).tsum_sub (hsG.mul_left (c / 2))]
  rw [tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one hr, tsum_mul_left,
    tsum_geometric_of_norm_lt_one hr]
  norm_num [r, c]

/-- The centered generic Geom(2/3) has second moment `3/4`; not a paper result. -/
theorem integral_geomTwoThirds_centered_sq :
    ∫ j, ((j : ℝ) - 1 / 2) ^ 2 ∂geomTwoThirds = 3 / 4 := by
  rw [integral_geomTwoThirds]
  let r : ℝ := 1 / 3
  let c : ℝ := 2 / 3
  have hr : ‖r‖ < 1 := by norm_num [r]
  have hs0 : Summable (fun j : ℕ => r ^ j) := (hasSum_geometric_of_norm_lt_one hr).summable
  have hs1 : Summable (fun j : ℕ => (j : ℝ) * r ^ j) := by
    simpa [r, pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hs2 : Summable (fun j : ℕ => (j : ℝ) ^ 2 * r ^ j) := by
    simpa [r] using summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have hform :
      (fun j : ℕ => (2 / 3 : ℝ) * (1 / 3 : ℝ) ^ j * ((j : ℝ) - 1 / 2) ^ 2) =
        (fun j : ℕ => c * ((j : ℝ) ^ 2 * r ^ j)) -
          (fun j : ℕ => c * ((j : ℝ) * r ^ j)) +
          (fun j : ℕ => (c / 4) * r ^ j) := by
    funext j
    dsimp [r, c]
    ring
  rw [hform]
  change tsum (fun j : ℕ =>
    (c * ((j : ℝ) ^ 2 * r ^ j) - c * ((j : ℝ) * r ^ j)) + (c / 4) * r ^ j) = 3 / 4
  rw [((hs2.mul_left c).sub (hs1.mul_left c)).tsum_add (hs0.mul_left (c / 4))]
  rw [(hs2.mul_left c).tsum_sub (hs1.mul_left c)]
  rw [tsum_mul_left, tsum_sq_mul_geometric_of_norm_lt_one hr, tsum_mul_left,
    tsum_coe_mul_geometric_of_norm_lt_one hr, tsum_mul_left,
    tsum_geometric_of_norm_lt_one hr]
  norm_num [r, c]

private theorem geomTwoThirds_centered_four_summable :
    Summable (fun j : ℕ =>
      (2 / 3 : ℝ) * (1 / 3 : ℝ) ^ j * ((j : ℝ) - 1 / 2) ^ 4) := by
  let r : ℝ := 1 / 3
  let c : ℝ := 2 / 3
  have hr : ‖r‖ < 1 := by norm_num [r]
  have hs0 : Summable (fun j : ℕ => r ^ j) := (hasSum_geometric_of_norm_lt_one hr).summable
  have hs1 : Summable (fun j : ℕ => (j : ℝ) * r ^ j) := by
    simpa [r, pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hs2 : Summable (fun j : ℕ => (j : ℝ) ^ 2 * r ^ j) := by
    simpa [r] using summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have hs3 : Summable (fun j : ℕ => (j : ℝ) ^ 3 * r ^ j) := by
    simpa [r] using summable_pow_mul_geometric_of_norm_lt_one 3 hr
  have hs4 : Summable (fun j : ℕ => (j : ℝ) ^ 4 * r ^ j) := by
    simpa [r] using summable_pow_mul_geometric_of_norm_lt_one 4 hr
  have hform :
      (fun j : ℕ => (2 / 3 : ℝ) * (1 / 3 : ℝ) ^ j * ((j : ℝ) - 1 / 2) ^ 4) =
        fun j : ℕ =>
          c * ((j : ℝ) ^ 4 * r ^ j) - (2 * c) * ((j : ℝ) ^ 3 * r ^ j) +
            (3 * c / 2) * ((j : ℝ) ^ 2 * r ^ j) - (c / 2) * ((j : ℝ) * r ^ j) +
              (c / 16) * r ^ j := by
    funext j
    dsimp [r, c]
    ring
  rw [hform]
  exact ((((hs4.mul_left c).sub (hs3.mul_left (2 * c))).add
      (hs2.mul_left (3 * c / 2))).sub (hs1.mul_left (c / 2))).add
      (hs0.mul_left (c / 16))

/-- The centered generic Geom(2/3) has a finite fourth moment; not a paper result. -/
theorem memLp_geomTwoThirds_centered_four :
    MemLp (fun j : ℕ => (j : ℝ) - 1 / 2) 4 geomTwoThirds := by
  have hweight : Summable (fun j : ℕ =>
      (ENNReal.ofReal ((2 / 3 : ℝ) * (1 / 3 : ℝ) ^ j)).toReal *
        ‖((j : ℝ) - 1 / 2) ^ 4‖) := by
    apply geomTwoThirds_centered_four_summable.congr
    intro j
    rw [ENNReal.toReal_ofReal]
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · positivity
  have hint : Integrable (fun j : ℕ => ((j : ℝ) - 1 / 2) ^ 4) geomTwoThirds := by
    unfold geomTwoThirds
    exact integrable_sum_dirac (fun j => by simp) hweight
  have hfmeas : AEStronglyMeasurable (fun j : ℕ => (j : ℝ) - 1 / 2) geomTwoThirds :=
    (measurable_of_countable _).aestronglyMeasurable
  have hnorm : Integrable
      (fun j : ℕ => ‖(j : ℝ) - 1 / 2‖ ^ (4 : ℝ)) geomTwoThirds := by
    convert hint using 1
    funext j
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      ← norm_pow, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  exact (integrable_norm_rpow_iff hfmeas (by norm_num) (by norm_num)).mp hnorm

/-- The centered generic Geom(2/3) has strictly positive fourth moment; not a paper result. -/
theorem integral_geomTwoThirds_centered_four_pos :
    0 < ∫ j, ((j : ℝ) - 1 / 2) ^ 4 ∂geomTwoThirds := by
  rw [integral_geomTwoThirds]
  have hzero : 0 < (2 / 3 : ℝ) * (1 / 3 : ℝ) ^ 0 * ((0 : ℝ) - 1 / 2) ^ 4 := by
    norm_num
  have hle : (2 / 3 : ℝ) * (1 / 3 : ℝ) ^ 0 * ((0 : ℝ) - 1 / 2) ^ 4 ≤
      ∑' j : ℕ, (2 / 3 : ℝ) * (1 / 3 : ℝ) ^ j * ((j : ℝ) - 1 / 2) ^ 4 := by
    simpa using geomTwoThirds_centered_four_summable.le_tsum 0 (fun j _ => by positivity)
  exact lt_of_lt_of_le hzero hle

end DirectedDistances.Probability
