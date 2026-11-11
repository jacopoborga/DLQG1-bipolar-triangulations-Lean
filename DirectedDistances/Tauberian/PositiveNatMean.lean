/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.NatMomentLaw
public import Mathlib.Analysis.Complex.Trigonometric

/-! # Strict positivity of the actual natural-valued mean

A producer for the original real-variable A.3 floor reduction. The actual
higher-order characteristic expansion rules out a zero mean; positivity is
a conclusion, not an extra hypothesis of the original real-valued result. -/

public section
namespace DirectedDistances.Tauberian
open MeasureTheory Filter
open scoped Topology

private theorem nat_eq_zero_ae_of_integral_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Y : Ω → ℕ} (hI : Integrable (fun ω => (Y ω : ℝ)) μ)
    (hzero : (∫ ω, (Y ω : ℝ) ∂μ) = 0) : ∀ᵐ ω ∂μ, Y ω = 0 := by
  have h := (integral_eq_zero_iff_of_nonneg (fun ω => Nat.cast_nonneg (Y ω)) hI).mp hzero
  filter_upwards [h] with ω hω
  change (Y ω : ℝ) = 0 at hω
  exact_mod_cast hω

private theorem characteristic_eq_one_of_zero_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℕ}
    (hzero : ∀ᵐ ω ∂μ, Y ω = 0) (t : ℝ) :
    (∫ ω, Complex.exp (((t * (Y ω : ℝ) : ℝ) : ℂ) * Complex.I) ∂μ) = 1 := by
  calc
    _ = ∫ _ω, (1 : ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hzero] with ω hω
      rw [hω]
      simp only [Nat.cast_zero, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
    _ = 1 := by simp only [integral_const, probReal_univ, one_smul]

private theorem model_coefficient_eq_zero {c : ℂ} {β : ℝ}
    (hb : (fun t : ℝ => (if 0 < t then c else starRingEnd ℂ c) *
      ((|t| ^ β : ℝ) : ℂ)) =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => |t| ^ β)) : c = 0 := by
  have ht := hb.tendsto_inv_smul_nhds_zero.mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  have hc : Tendsto (fun _t : ℝ => c) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply ht.congr'
    filter_upwards [eventually_mem_nhdsWithin] with t ht0
    have hp : (((t ^ β : ℝ)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ht0 β).ne'
    rw [abs_of_pos ht0, ite_eq_left (show 0 < t from ht0), Complex.real_smul, Complex.ofReal_inv]
    field_simp
  exact tendsto_nhds_unique tendsto_const_nhds hc

/-- The actual higher-order characteristic expansion with a nonreal power
coefficient forces the actual integrable natural-variable mean to be strictly
positive. The linear coefficient is the literal expectation, not a chosen
parameter. This is an ordinary producer for the real A.3 floor reduction. -/
theorem integral_natCast_pos_of_higher_order_boundary {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℕ} (_hY : Measurable Y)
    (hI : Integrable (fun ω => (Y ω : ℝ)) μ)
    {ν : ℝ} (_hν₀ : 0 < ν) (_hν₁ : ν < 1) {c₂ : ℂ} (hc₂ : c₂.im ≠ 0)
    (hb : (fun t : ℝ =>
      (∫ ω, Complex.exp (((t * (Y ω : ℝ) : ℝ) : ℂ) * Complex.I) ∂μ) - 1 -
        ((∫ ω, (Y ω : ℝ) ∂μ : ℝ) : ℂ) * Complex.I * (t : ℂ) -
        (if 0 < t then c₂ else starRingEnd ℂ c₂) * ((|t| ^ (1 + ν) : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => |t| ^ (1 + ν))) :
    0 < ∫ ω, (Y ω : ℝ) ∂μ := by
  have hnonneg : 0 ≤ ∫ ω, (Y ω : ℝ) ∂μ :=
    integral_nonneg (fun ω => Nat.cast_nonneg (Y ω))
  by_contra hnot
  have hm0 : (∫ ω, (Y ω : ℝ) ∂μ) = 0 := le_antisymm (not_lt.mp hnot) hnonneg
  have hy0 := nat_eq_zero_ae_of_integral_eq_zero hI hm0
  have hmodel : (fun t : ℝ => (if 0 < t then c₂ else starRingEnd ℂ c₂) *
      ((|t| ^ (1 + ν) : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => |t| ^ (1 + ν)) := by
    simpa only [characteristic_eq_one_of_zero_ae hy0, hm0, Complex.ofReal_zero,
      zero_mul, sub_self, zero_sub, neg_neg] using hb.neg_left
  have hc0 := model_coefficient_eq_zero hmodel
  exact hc₂ (by rw [hc0, Complex.zero_im])

end DirectedDistances.Tauberian
