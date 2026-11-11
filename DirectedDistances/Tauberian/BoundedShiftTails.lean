/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.TailPowerTransfer

/-! # Actual tail transfer across an almost-sure unit lag

The floor reduction for original-v1 real nonnegative random variables. These
conditional helpers transfer an already proved natural-variable tail law to
the actual real variable by event inclusions, without assuming its conclusion. -/

public section
namespace DirectedDistances.Tauberian
open Filter MeasureTheory
open scoped Topology

private theorem shifted_power_limit {F : ℝ → ℝ} {ρ C : ℝ}
    (hF : Tendsto (fun R : ℝ => F R / R ^ ρ) atTop (𝓝 C)) :
    Tendsto (fun R : ℝ => F (R - 1) / R ^ ρ) atTop (𝓝 C) := by
  have hindex : Tendsto (fun R : ℝ => R - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b + 1)] with R hR
    linarith only [hR]
  have hratio : Tendsto (fun R : ℝ => (R - 1) / R) atTop (𝓝 1) := by
    have ht : Tendsto (fun R : ℝ => 1 - R⁻¹) atTop (𝓝 1) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_inv_atTop_zero
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    field_simp
  have hp := hratio.rpow_const (p := ρ) (Or.inl one_ne_zero)
  simp only [Real.one_rpow] at hp
  have hh := (hF.comp hindex).mul hp
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
  have hr : 0 < R := lt_trans zero_lt_one hR
  have hrs : 0 < R - 1 := sub_pos.mpr hR
  change F (R - 1) / (R - 1) ^ ρ * ((R - 1) / R) ^ ρ = F (R - 1) / R ^ ρ
  rw [Real.div_rpow hrs.le hr.le]
  field_simp [(Real.rpow_pos_of_pos hrs ρ).ne', (Real.rpow_pos_of_pos hr ρ).ne']

private theorem power_limit_of_littleO {F : ℝ → ℝ} {ρ C : ℝ}
    (hF : (fun R : ℝ => F R - C * R ^ ρ) =o[atTop] (fun R : ℝ => R ^ ρ)) :
    Tendsto (fun R : ℝ => F R / R ^ ρ) atTop (𝓝 C) := by
  have hh := hF.tendsto_div_nhds_zero.add_const C
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  field_simp [(Real.rpow_pos_of_pos hR ρ).ne']
  ring

private theorem real_tail_squeeze_of_ae_unit_lag {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} {Y : Ω → ℕ}
    (hlag : ∀ᵐ ω ∂μ, (Y ω : ℝ) ≤ X ω ∧ X ω < (Y ω : ℝ) + 1) (R : ℝ) :
    μ.real {ω | R < (Y ω : ℝ)} ≤ μ.real {ω | R < X ω} ∧
      μ.real {ω | R < X ω} ≤ μ.real {ω | R - 1 < (Y ω : ℝ)} := by
  constructor
  · apply ENNReal.toReal_mono (measure_ne_top μ _)
    apply measure_mono_ae
    filter_upwards [hlag] with ω hω
    exact fun h => h.trans_le hω.1
  · apply ENNReal.toReal_mono (measure_ne_top μ _)
    apply measure_mono_ae
    filter_upwards [hlag] with ω hω
    intro h
    change R < X ω at h
    linarith only [h, hω.2]

/-- A genuine real tail power limit transfers across an almost-sure unit lag.
The strict event bounds are derived from the lag; no real-variable tail limit
is assumed. The real exponent is arbitrary. -/
theorem tendsto_real_tail_power_of_ae_unit_lag {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {Y : Ω → ℕ}
    (_hX : Measurable X) (_hY : Measurable Y)
    (hlag : ∀ᵐ ω ∂μ, (Y ω : ℝ) ≤ X ω ∧ X ω < (Y ω : ℝ) + 1)
    {ρ C : ℝ}
    (hYtail : Tendsto (fun R : ℝ => μ.real {ω | R < (Y ω : ℝ)} / R ^ ρ)
      atTop (𝓝 C)) :
    Tendsto (fun R : ℝ => μ.real {ω | R < X ω} / R ^ ρ) atTop (𝓝 C) := by
  have hupper := shifted_power_limit hYtail
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hYtail hupper
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact (div_le_div_iff_of_pos_right (Real.rpow_pos_of_pos hR ρ)).2
      (real_tail_squeeze_of_ae_unit_lag hlag R).1
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact (div_le_div_iff_of_pos_right (Real.rpow_pos_of_pos hR ρ)).2
      (real_tail_squeeze_of_ae_unit_lag hlag R).2

/-- The literal real-variable little-o tail remainder follows from the proved
integer-variable remainder across the actual almost-sure unit lag. -/
theorem real_tail_isLittleO_of_ae_unit_lag {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {Y : Ω → ℕ}
    (hX : Measurable X) (hY : Measurable Y)
    (hlag : ∀ᵐ ω ∂μ, (Y ω : ℝ) ≤ X ω ∧ X ω < (Y ω : ℝ) + 1)
    {ρ C : ℝ}
    (hYtail : (fun R : ℝ => μ.real {ω | R < (Y ω : ℝ)} - C * R ^ ρ)
      =o[atTop] (fun R : ℝ => R ^ ρ)) :
    (fun R : ℝ => μ.real {ω | R < X ω} - C * R ^ ρ)
      =o[atTop] (fun R : ℝ => R ^ ρ) :=
  isLittleO_sub_mul_rpow_of_tendsto
    (tendsto_real_tail_power_of_ae_unit_lag hX hY hlag (power_limit_of_littleO hYtail))

end DirectedDistances.Tauberian
