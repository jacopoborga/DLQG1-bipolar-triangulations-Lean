/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.RealCharacteristicBasic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Complex.Log










public section
namespace DirectedDistances.Tauberian
open MeasureTheory



theorem cexp_mul_I_cpow_ofReal {t : ℝ} (ht₁ : -Real.pi < t) (ht₂ : t < Real.pi) (x : ℝ) :
    (Complex.exp ((t : ℂ) * Complex.I)) ^ (x : ℂ) =
      Complex.exp ((((t * x : ℝ) : ℂ)) * Complex.I) := by
  have him : ((t : ℂ) * Complex.I).im = t := by simp
  have hlog : Complex.log (Complex.exp ((t : ℂ) * Complex.I)) = (t : ℂ) * Complex.I :=
    Complex.log_exp (by rw [him]; exact ht₁) (by rw [him]; exact ht₂.le)
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), hlog]
  congr 1
  push_cast
  ring





theorem integrable_and_integral_cexp_mul_I_cpow {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {t : ℝ} (ht₁ : -Real.pi < t) (ht₂ : t < Real.pi) :
    Integrable (fun ω => (Complex.exp ((t : ℂ) * Complex.I)) ^ (X ω : ℂ)) μ ∧
      (∫ ω, (Complex.exp ((t : ℂ) * Complex.I)) ^ (X ω : ℂ) ∂μ) =
        ∫ ω, Complex.exp ((((t * X ω : ℝ) : ℂ)) * Complex.I) ∂μ := by
  have h : (fun ω => (Complex.exp ((t : ℂ) * Complex.I)) ^ (X ω : ℂ)) =
      fun ω => Complex.exp ((((t * X ω : ℝ) : ℂ)) * Complex.I) :=
    funext fun ω => cexp_mul_I_cpow_ofReal ht₁ ht₂ (X ω)
  constructor
  · rw [h]
    exact integrable_real_characteristic hX t
  · rw [h]



theorem eventually_integral_cexp_mul_I_cpow_eq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) :
    Filter.Eventually (fun t : ℝ =>
      (∫ ω, (Complex.exp ((t : ℂ) * Complex.I)) ^ (X ω : ℂ) ∂μ) =
        ∫ ω, Complex.exp ((((t * X ω : ℝ) : ℂ)) * Complex.I) ∂μ)
      (nhds (0 : ℝ)) := by
  have hnear : Set.Ioo (-Real.pi) Real.pi ∈ nhds (0 : ℝ) :=
    isOpen_Ioo.mem_nhds ⟨by linarith [Real.pi_pos], Real.pi_pos⟩
  filter_upwards [hnear] with t ht
  exact (integrable_and_integral_cexp_mul_I_cpow (μ := μ) hX ht.1 ht.2).2

end DirectedDistances.Tauberian
