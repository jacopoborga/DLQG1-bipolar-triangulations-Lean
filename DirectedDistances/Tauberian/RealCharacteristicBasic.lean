/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.GeneratingFunctionLaw






public section
namespace DirectedDistances.Tauberian
open MeasureTheory

/-- Every measurable real variable has an integrable characteristic integrand. -/
theorem integrable_real_characteristic {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (t : ℝ) :
    Integrable (fun ω => Complex.exp ((((t * X ω : ℝ) : ℂ)) * Complex.I)) μ := by
  have hc : Continuous (fun x : ℝ => Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul continuous_const)
  apply (integrable_const (1 : ℝ)).mono' ((hc.measurable.comp hX).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun ω =>
    le_of_eq (Complex.norm_exp_ofReal_mul_I (t * X ω))

/-- The actual characteristic expectation at zero is one. -/
theorem real_characteristic_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : Ω → ℝ) :
    (∫ ω, Complex.exp (((((0 : ℝ) * X ω : ℝ) : ℂ)) * Complex.I) ∂μ) = 1 := by
  simp

end DirectedDistances.Tauberian
