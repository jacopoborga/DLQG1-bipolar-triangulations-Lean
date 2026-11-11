/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.ScaledPowerError
import Mathlib.MeasureTheory.Integral.IntegralEqImproper








public section
namespace DirectedDistances.Tauberian

open Set MeasureTheory Filter
open scoped Topology Interval

/-- The derivative remainder in integration by parts is absolutely integrable. -/
theorem integrableOn_power_deriv_sin {ν : ℝ} (hν : 0 < ν) :
    IntegrableOn (fun x : ℝ => (-ν * x ^ (-ν - 1)) * Real.sin x) (Ioi 1) := by
  apply ((integrableOn_rpow_neg_sub_one hν).const_mul (-ν)).mul_bdd
    Real.continuous_sin.aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one x)

/-- The oscillating endpoint term vanishes for every positive exponent. -/
theorem tendsto_power_mul_sin_zero {ν : ℝ} (hν : 0 < ν) :
    Tendsto (fun x : ℝ => x ^ (-ν) * Real.sin x) atTop (𝓝 0) := by
  simpa only [mul_comm] using bdd_le_mul_tendsto_zero' 1
    (Eventually.of_forall Real.abs_sin_le_one) (tendsto_rpow_neg_atTop hν)

/-- Integration by parts on a finite interval away from the singular endpoint. -/
theorem integral_power_cos_one {ν R : ℝ} (hR : 1 ≤ R) :
    (∫ x : ℝ in 1..R, x ^ (-ν) * Real.cos x) =
      R ^ (-ν) * Real.sin R - Real.sin 1 -
        ∫ x : ℝ in 1..R, (-ν * x ^ (-ν - 1)) * Real.sin x := by
  have hx : ∀ x ∈ uIcc (1 : ℝ) R, 0 < x := by
    intro x hx
    rw [uIcc_of_le hR] at hx
    exact zero_lt_one.trans_le hx.1
  have hp : ContinuousOn (fun x : ℝ => x ^ (-ν - 1)) (uIcc 1 R) :=
    continuousOn_id.rpow_const (fun x hx' => Or.inl (hx x hx').ne')
  simpa only [Real.one_rpow, one_mul] using
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun x hx' => Real.hasDerivAt_rpow_const (Or.inl (hx x hx').ne'))
      (fun x _ => Real.hasDerivAt_sin x)
      (hp.const_mul (-ν)).intervalIntegrable
      (Real.continuous_cos.intervalIntegrable _ _)

/-- The tail has a genuine arbitrary-cutoff improper limit. -/
theorem tendsto_integral_power_cos_one {ν : ℝ} (hν : 0 < ν) :
    Tendsto (fun R : ℝ => ∫ x : ℝ in 1..R, x ^ (-ν) * Real.cos x) atTop
      (𝓝 (-Real.sin 1 -
        ∫ x : ℝ in Ioi 1, (-ν * x ^ (-ν - 1)) * Real.sin x)) := by
  have hi := intervalIntegral_tendsto_integral_Ioi 1
    (integrableOn_power_deriv_sin hν) tendsto_id
  have ht := ((tendsto_power_mul_sin_zero hν).sub_const (Real.sin 1)).sub hi
  simp only [zero_sub] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  exact (integral_power_cos_one hR).symm

/-- The power-cosine integrand is integrable over every bounded interval when
`ν < 1`, including intervals meeting zero. -/
theorem intervalIntegrable_power_cos {ν a b : ℝ} (hν : ν < 1) :
    IntervalIntegrable (fun x : ℝ => x ^ (-ν) * Real.cos x) volume a b :=
  (intervalIntegrable_rpow_neg hν).mul_continuousOn Real.continuous_cos.continuousOn

/-- Existence from zero follows by adding the locally integrable initial part.
This theorem gives an actual witness, rather than a default set integral. -/
theorem exists_improper_power_cos {ν : ℝ} (hν₀ : 0 < ν) (hν₁ : ν < 1) :
    ∃ L : ℝ, Tendsto
      (fun R : ℝ => ∫ x : ℝ in (0 : ℝ)..R, x ^ (-ν) * Real.cos x) atTop (𝓝 L) := by
  refine ⟨(∫ x : ℝ in (0 : ℝ)..1, x ^ (-ν) * Real.cos x) +
    (-Real.sin 1 - ∫ x : ℝ in Ioi 1, (-ν * x ^ (-ν - 1)) * Real.sin x), ?_⟩
  have ht := (tendsto_integral_power_cos_one hν₀).const_add
    (∫ x : ℝ in (0 : ℝ)..1, x ^ (-ν) * Real.cos x)
  apply ht.congr'
  exact Eventually.of_forall (fun R => intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_power_cos hν₁) (intervalIntegrable_power_cos hν₁))

/-- A finite-cutoff identity separates the two improper terms through an
absolutely integrable difference. -/
theorem integral_staircase_power_cos_decomposition {ν t R : ℝ}
    (hν₀ : 0 < ν) (hν₁ : ν < 1) (ht : 0 < t) (hR : 0 ≤ R) :
    (∫ u : ℝ in (0 : ℝ)..R, (((⌊u / t⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) * Real.cos u) =
      t ^ ν * (∫ u : ℝ in (0 : ℝ)..R, u ^ (-ν) * Real.cos u) +
        ∫ u : ℝ in (0 : ℝ)..R,
          ((((⌊u / t⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - (u / t) ^ (-ν)) * Real.cos u := by
  have he : IntervalIntegrable (fun u : ℝ =>
      ((((⌊u / t⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - (u / t) ^ (-ν)) * Real.cos u)
      volume 0 R := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).2
    exact (integrableOn_scaled_power_staircase_error_cos hν₀ hν₁ ht).mono_set
      (fun x hx => hx.1)
  have hp := (intervalIntegrable_power_cos (a := 0) (b := R) hν₁).const_mul (t ^ ν)
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add hp he]
  apply intervalIntegral.integral_congr_Ioo_of_le hR
  intro u hu
  dsimp only
  rw [Real.div_rpow hu.1.le ht.le, Real.rpow_neg ht.le, div_inv_eq_mul]
  ring

/-- The first approximation in revised A.6, with genuine arbitrary-cutoff
improper integrals and a coefficient uniform in every positive scale.
The Gamma evaluation and hence the full numbered lemma remain separate. -/
theorem exists_improper_staircase_power_cos_approximation {ν : ℝ}
    (hν₀ : 0 < ν) (hν₁ : ν < 1) :
    ∃ J : ℝ,
      Tendsto (fun R : ℝ => ∫ u : ℝ in (0 : ℝ)..R, u ^ (-ν) * Real.cos u)
        atTop (𝓝 J) ∧
      ∀ t : ℝ, 0 < t → ∃ I : ℝ,
        Tendsto (fun R : ℝ => ∫ u : ℝ in (0 : ℝ)..R,
          (((⌊u / t⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) * Real.cos u) atTop (𝓝 I) ∧
        ‖I - t ^ ν * J‖ ≤ t * (1 / (1 - ν) + 1) := by
  obtain ⟨J, hJ⟩ := exists_improper_power_cos hν₀ hν₁
  refine ⟨J, hJ, ?_⟩
  intro t ht
  let E : ℝ := ∫ u : ℝ in Ioi 0,
    ((((⌊u / t⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - (u / t) ^ (-ν)) * Real.cos u
  refine ⟨t ^ ν * J + E, ?_, ?_⟩
  · have he := intervalIntegral_tendsto_integral_Ioi 0
      (integrableOn_scaled_power_staircase_error_cos hν₀ hν₁ ht) tendsto_id
    have hh := (hJ.const_mul (t ^ ν)).add he
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact (integral_staircase_power_cos_decomposition hν₀ hν₁ ht hR).symm
  · rw [add_sub_cancel_left]
    exact norm_integral_scaled_power_staircase_error_cos_le hν₀ hν₁ ht

/-- Actual improper limits satisfy both remainder estimates in revised A.6.
Only the evaluation of `J` by the Gamma expression is not supplied here. -/
theorem exists_improper_staircase_power_cos_asymptotics {ν : ℝ}
    (hν₀ : 0 < ν) (hν₁ : ν < 1) :
    ∃ (J : ℝ) (I : ℝ → ℝ),
      Tendsto (fun R : ℝ => ∫ u : ℝ in (0 : ℝ)..R, u ^ (-ν) * Real.cos u)
        atTop (𝓝 J) ∧
      (∀ t : ℝ, 0 < t → Tendsto (fun R : ℝ => ∫ u : ℝ in (0 : ℝ)..R,
        (((⌊u / t⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) * Real.cos u) atTop (𝓝 (I t))) ∧
      (∀ t : ℝ, 0 < t → ‖I t - t ^ ν * J‖ ≤ t * (1 / (1 - ν) + 1)) ∧
      (fun t : ℝ => I t - t ^ ν * J) =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t) ∧
      (fun t : ℝ => I t - t ^ ν * J) =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ ν) := by
  obtain ⟨J, hJ⟩ := exists_improper_power_cos hν₀ hν₁
  let E := fun t : ℝ => ∫ u : ℝ in Ioi 0,
    ((((⌊u / t⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) - (u / t) ^ (-ν)) * Real.cos u
  refine ⟨J, (fun t => t ^ ν * J + E t), hJ, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have he := intervalIntegral_tendsto_integral_Ioi 0
      (integrableOn_scaled_power_staircase_error_cos hν₀ hν₁ ht) tendsto_id
    apply ((hJ.const_mul (t ^ ν)).add he).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact (integral_staircase_power_cos_decomposition hν₀ hν₁ ht hR).symm
  · intro t ht
    simpa only [add_sub_cancel_left] using
      norm_integral_scaled_power_staircase_error_cos_le hν₀ hν₁ ht
  · simpa only [add_sub_cancel_left] using
      scaled_power_staircase_error_cos_isBigO hν₀ hν₁
  · simpa only [add_sub_cancel_left] using
      scaled_power_staircase_error_cos_isLittleO hν₀ hν₁

end DirectedDistances.Tauberian
