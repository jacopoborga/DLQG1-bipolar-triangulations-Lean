/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! # Actual first moments of natural-valued random variables

The real-variable floor reduction consumes a proved moment series for the
actual natural-valued fiber law. This file produces integrability and the
actual expectation from that series, without assuming either conclusion. -/

public section
namespace DirectedDistances.Tauberian
open MeasureTheory

private theorem integrable_natCast_of_summable_singletons {ν : Measure ℕ} [IsFiniteMeasure ν]
    (hm : Summable (fun n : ℕ => (n : ℝ) * ν.real {n})) :
    Integrable (fun n : ℕ => (n : ℝ)) ν := by
  have hw : Summable (fun n : ℕ => (ν {n}).toReal * ‖(n : ℝ)‖) := by
    apply hm.congr
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
    exact mul_comm _ _
  rw [← Measure.sum_smul_dirac ν]
  exact integrable_sum_dirac (fun n => measure_ne_top ν _) hw

/-- A summable actual natural-valued fiber first moment produces genuine
integrability and identifies the actual expectation with that same series. -/
theorem integrable_integral_natCast_of_summable_fiber {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℕ} (hY : Measurable Y)
    (hm : Summable (fun n : ℕ => (n : ℝ) * μ.real (Y ⁻¹' {n}))) :
    Integrable (fun ω => (Y ω : ℝ)) μ ∧
      (∫ ω, (Y ω : ℝ) ∂μ) = ∑' n : ℕ, (n : ℝ) * μ.real (Y ⁻¹' {n}) := by
  have hmmap : Summable (fun n : ℕ => (n : ℝ) * (μ.map Y).real {n}) := by
    apply hm.congr
    intro n
    rw [map_measureReal_apply hY (measurableSet_singleton n)]
  have himap := integrable_natCast_of_summable_singletons hmmap
  have hmeas : StronglyMeasurable (fun n : ℕ => (n : ℝ)) :=
    (measurable_of_countable _).stronglyMeasurable
  have hi : Integrable (fun ω => (Y ω : ℝ)) μ :=
    (integrable_map_measure hmeas.aestronglyMeasurable hY.aemeasurable).mp himap
  refine ⟨hi, ?_⟩
  rw [← integral_map_of_stronglyMeasurable hY hmeas, integral_countable himap]
  apply tsum_congr
  intro n
  rw [map_measureReal_apply hY (measurableSet_singleton n)]
  simp only [smul_eq_mul]
  exact mul_comm _ _

end DirectedDistances.Tauberian
