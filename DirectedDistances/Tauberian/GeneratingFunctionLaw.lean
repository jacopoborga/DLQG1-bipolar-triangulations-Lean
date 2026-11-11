/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.ProbabilityGeneratingFunction
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Analysis.Complex.Trigonometric








public section
namespace DirectedDistances.Tauberian

open MeasureTheory
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℕ}

omit [IsProbabilityMeasure μ] in
/-- The literal point probabilities are nonnegative. -/
theorem probability_fiber_nonneg (k : ℕ) : 0 ≤ (μ (X ⁻¹' {k})).toReal :=
  ENNReal.toReal_nonneg

/-- A natural-valued random variable has total discrete probability mass one. -/
theorem hasSum_probability_fiber (hX : Measurable X) :
    HasSum (fun k : ℕ => (μ (X ⁻¹' {k})).toReal) 1 := by
  have ht : (∑' k : ℕ, μ (X ⁻¹' {k})) = 1 := by
    rw [← measure_iUnion (pairwise_disjoint_fiber X)
      (fun k => hX (measurableSet_singleton k))]
    have hu : (⋃ k : ℕ, X ⁻¹' {k}) = Set.univ := by
      ext ω
      simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
        exists_eq', Set.mem_univ]
    rw [hu, measure_univ]
  have hreal : (∑' k : ℕ, (μ (X ⁻¹' {k})).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun k => measure_ne_top μ _), ht, ENNReal.toReal_one]
  rw [← hreal]
  exact ENNReal.hasSum_toReal (by rw [ht]; exact ENNReal.one_ne_top)

/-- Every generating-function integrand on the closed disk is integrable,
by its uniform bound of one under a probability measure. -/
theorem integrable_pow_randomVariable (hX : Measurable X) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Integrable (fun ω => z ^ X ω) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    (((measurable_of_countable (fun n : ℕ => z ^ n)).comp hX).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun ω => by
    change ‖z ^ X ω‖ ≤ 1
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg z) hz

/-- The expectation defining the generating function is the genuine discrete
probability generating series on the whole closed unit disk. -/
theorem integral_pow_eq_tsum_probability_fiber (hX : Measurable X)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (∫ ω, z ^ X ω ∂μ) = ∑' k : ℕ, ((μ (X ⁻¹' {k})).toReal : ℂ) * z ^ k := by
  have hmeas : StronglyMeasurable (fun k : ℕ => z ^ k) :=
    (measurable_of_countable _).stronglyMeasurable
  have hi : Integrable (fun k : ℕ => z ^ k) (Measure.map X μ) :=
    (integrable_map_measure hmeas.aestronglyMeasurable hX.aemeasurable).2
      (integrable_pow_randomVariable hX hz)
  rw [← integral_map_of_stronglyMeasurable hX hmeas, integral_countable hi]
  apply tsum_congr
  intro k
  rw [Measure.real, Measure.map_apply hX (measurableSet_singleton k), Complex.real_smul]

omit [IsProbabilityMeasure μ] in
/-- The boundary generating-function expectation is the characteristic
expectation, with the natural variable explicitly cast to the real carrier. -/
theorem integral_pow_exp_eq_characteristic (t : ℝ) :
    (∫ ω, Complex.exp ((t : ℂ) * Complex.I) ^ X ω ∂μ) =
      ∫ ω, Complex.exp (((t * (X ω : ℝ) : ℝ) : ℂ) * Complex.I) ∂μ := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => by
    change Complex.exp ((t : ℂ) * Complex.I) ^ X ω =
      Complex.exp (((t * (X ω : ℝ) : ℝ) : ℂ) * Complex.I)
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring

/-- The characteristic expectation has its normalized probability series. -/
theorem integral_characteristic_eq_tsum_probability_fiber
    (hX : Measurable X) (t : ℝ) :
    (∫ ω, Complex.exp (((t * (X ω : ℝ) : ℝ) : ℂ) * Complex.I) ∂μ) =
      ∑' k : ℕ, ((μ (X ⁻¹' {k})).toReal : ℂ) *
        Complex.exp ((t : ℂ) * Complex.I) ^ k := by
  rw [← integral_pow_exp_eq_characteristic t]
  exact integral_pow_eq_tsum_probability_fiber hX
    (le_of_eq (Complex.norm_exp_ofReal_mul_I t))

/-- Characteristic integrability follows from the unit-modulus exponential
bound, so its expectation also has no default-value interpretation. -/
theorem integrable_characteristic_randomVariable (hX : Measurable X) (t : ℝ) :
    Integrable (fun ω => Complex.exp (((t * (X ω : ℝ) : ℝ) : ℂ) * Complex.I)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    (((measurable_of_countable (fun n : ℕ =>
      Complex.exp (((t * (n : ℝ) : ℝ) : ℂ) * Complex.I))).comp hX).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun ω => by
    change ‖Complex.exp (((t * (X ω : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤ 1
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I (t * (X ω : ℝ)))

/-- Every generating expectation is the actual sum of its probability series. -/
theorem hasSum_probability_fiber_pow_integral (hX : Measurable X)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun k : ℕ => ((μ (X ⁻¹' {k})).toReal : ℂ) * z ^ k)
      (∫ ω, z ^ X ω ∂μ) := by
  rw [integral_pow_eq_tsum_probability_fiber hX hz]
  exact hasSum_weighted_pow (fun k => probability_fiber_nonneg k)
    (hasSum_probability_fiber hX).summable hz

/-- Revised Appendix A: the expectation itself is the uniform limit of its
probability partial sums and is continuous on the closed disk and holomorphic
on the open disk, with value one at one. -/
theorem generating_expectation_properties (hX : Measurable X) :
    TendstoUniformlyOn
      (fun (N : ℕ) (z : ℂ) => ∑ k ∈ Finset.range N,
        ((μ (X ⁻¹' {k})).toReal : ℂ) * z ^ k)
      (fun z : ℂ => ∫ ω, z ^ X ω ∂μ) Filter.atTop (Metric.closedBall 0 1) ∧
    ContinuousOn (fun z : ℂ => ∫ ω, z ^ X ω ∂μ) (Metric.closedBall 0 1) ∧
    DifferentiableOn ℂ (fun z : ℂ => ∫ ω, z ^ X ω ∂μ) (Metric.ball 0 1) ∧
    (∫ ω, (1 : ℂ) ^ X ω ∂μ) = 1 := by
  have hf := fun k => probability_fiber_nonneg (μ := μ) (X := X) k
  have hs := hasSum_probability_fiber (μ := μ) hX
  have hclosed : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      (∫ ω, z ^ X ω ∂μ) = ∑' k : ℕ, ((μ (X ⁻¹' {k})).toReal : ℂ) * z ^ k := by
    intro z hz
    exact integral_pow_eq_tsum_probability_fiber hX
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
  refine ⟨(tendstoUniformlyOn_sum_weighted_pow hf hs.summable).congr_right
    (fun z hz => (hclosed z hz).symm),
    (continuousOn_tsum_weighted_pow hf hs.summable).congr hclosed,
    (differentiableOn_tsum_weighted_pow hf hs.summable).congr ?_, ?_⟩
  · intro z hz
    exact hclosed z (Metric.ball_subset_closedBall hz)
  · simp only [one_pow, integral_const, probReal_univ, one_smul]

end DirectedDistances.Tauberian
