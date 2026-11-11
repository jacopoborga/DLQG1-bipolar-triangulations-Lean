/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.AppendixA.TauberianAboveOne
import DirectedDistances.Tauberian.RealRoundingQuadratic
import DirectedDistances.Tauberian.NatMomentLaw
import DirectedDistances.Tauberian.PositiveNatMean
import DirectedDistances.Tauberian.BoundedShiftTails

/-! # Original Appendix A.3 for nonnegative real random variables

under the real-valued standing assumptions at lines 3–9. The actual higher-order
characteristic expansion produces the rounded first moment before the
conditional quadratic rounding estimate is used. The complete integer theorem
then transfers back to the actual real tail with the unchanged coefficient.
The source's general-real PGF holomorphy is neither assumed nor claimed. -/

public section
namespace DirectedDistances.PaperProofs.AppendixA
open MeasureTheory Filter
open scoped Topology
universe u

private theorem nat_mean_of_characteristic_derivative {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℕ} (hY : Measurable Y) {m : ℝ}
    (hd : HasDerivAt (fun t : ℝ =>
      ∫ ω, Complex.exp ((((t * (Y ω : ℝ)) : ℝ) : ℂ) * Complex.I) ∂μ)
      ((m : ℂ) * Complex.I) 0) :
    Integrable (fun ω => (Y ω : ℝ)) μ ∧ (∫ ω, (Y ω : ℝ) ∂μ) = m := by
  let f : ℕ → ℝ := fun k => μ.real (Y ⁻¹' {k})
  have hf : ∀ k, 0 ≤ f k := fun k => ENNReal.toReal_nonneg
  have hs : HasSum f 1 := DirectedDistances.Tauberian.hasSum_probability_fiber hY
  have hφ (t : ℝ) :
      (∫ ω, Complex.exp ((((t * (Y ω : ℝ)) : ℝ) : ℂ) * Complex.I) ∂μ) =
        ∑' k : ℕ, (f k : ℂ) * Complex.exp ((((t * (k : ℝ)) : ℝ) : ℂ) * Complex.I) := by
    rw [DirectedDistances.Tauberian.integral_characteristic_eq_tsum_probability_fiber hY t]
    apply tsum_congr
    intro k
    change (f k : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ^ k = _
    rw [← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hd' : HasDerivAt (fun t : ℝ =>
      ∑' k : ℕ, (f k : ℂ) * Complex.exp ((((t * (k : ℝ)) : ℝ) : ℂ) * Complex.I))
      ((m : ℂ) * Complex.I) 0 := by simpa only [hφ] using hd
  obtain ⟨hm, hmean⟩ := DirectedDistances.Tauberian.first_moment_of_characteristic_derivative
    f hf hs hd'
  obtain ⟨hi, heq⟩ := DirectedDistances.Tauberian.integrable_integral_natCast_of_summable_fiber hY hm
  exact ⟨hi, heq.trans hmean⟩

private theorem rounded_mean_of_higher_order_boundary {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (hX₀ : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    {c₁ ν : ℝ} (hν₀ : 0 < ν) {c₂ : ℂ}
    (hb : (fun t : ℝ =>
      (∫ ω, Complex.exp ((((t * X ω) : ℝ) : ℂ) * Complex.I) ∂μ) - 1 -
      (c₁ : ℂ) * Complex.I * (t : ℂ) -
      (if 0 < t then c₂ else starRingEnd ℂ c₂) * (((|t| : ℝ) ^ (1 + ν) : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ (1 + ν))) :
    Integrable (fun ω => (Nat.floor |X ω| : ℝ)) μ ∧
      (∫ ω, (Nat.floor |X ω| : ℝ) ∂μ) =
        c₁ - (∫ ω, X ω - (Nat.floor |X ω| : ℝ) ∂μ) := by
  let Y : Ω → ℕ := fun ω => Nat.floor |X ω|
  let m : ℝ := c₁ - (∫ ω, X ω - (Y ω : ℝ) ∂μ)
  have hdX := DirectedDistances.Tauberian.hasDerivAt_of_higher_order_boundary
    (DirectedDistances.Tauberian.real_characteristic_zero X) hν₀ hb
  have hdD := DirectedDistances.Tauberian.hasDerivAt_CFroundingdifference hX hX₀
  have hdY : HasDerivAt (fun t : ℝ =>
      ∫ ω, Complex.exp ((((t * (Y ω : ℝ)) : ℝ) : ℂ) * Complex.I) ∂μ)
      ((m : ℂ) * Complex.I) 0 := by
    convert hdX.sub hdD using 1
    · funext t
      dsimp only [Y, Pi.sub_apply]
      ring
    · dsimp only [m, Y]
      push_cast
      ring
  exact nat_mean_of_characteristic_derivative
    (DirectedDistances.Tauberian.measurable_floor_abs hX) hdY

/-- Original-v1 Lemma A.3 for actual nonnegative real variables, with its
imaginary sign, positive shared coefficient and strict real-tail asymptotic. -/
theorem real_tauberian_above_one :
∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (_hX : Measurable X) (_hX₀ : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (c₁ : ℝ) (_hc₁ : 0 < c₁) (c₂ : ℂ) (_hc₂ : c₂.im ≠ 0)
    (ν : ℝ) (_hν₀ : 0 < ν) (_hν₁ : ν < 1),
    (fun t : ℝ => (∫ ω, Complex.exp ((((t * X ω) : ℝ) : ℂ) * Complex.I) ∂μ) - 1 -
      (c₁ : ℂ) * Complex.I * (t : ℂ) -
      (if 0 < t then c₂ else starRingEnd ℂ c₂) * (((|t| : ℝ) ^ (1 + ν) : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ (1 + ν)) →
    let a : ℝ := -(ν / Real.Gamma (1 - ν)) / Real.cos (Real.pi * ν / 2) * c₂.im
    c₂.im < 0 ∧ 0 < a ∧
      (fun R : ℝ => μ.real {ω | R < X ω} - a * R ^ (-ν - 1))
        =o[atTop] (fun R : ℝ => R ^ (-ν - 1)) := by
  intro Ω _ μ _ X hX hX₀ c₁ _hc₁ c₂ hc₂ ν hν₀ hν₁ hb
  let Y : Ω → ℕ := fun ω => Nat.floor |X ω|
  have hY : Measurable Y := DirectedDistances.Tauberian.measurable_floor_abs hX
  obtain ⟨hYI, hEY⟩ := rounded_mean_of_higher_order_boundary hX hX₀ hν₀ hb
  have hcentered := DirectedDistances.Tauberian.CFrounding_centered_isLittleO_abs_rpow_one_add
    hX hX₀ hYI hν₀ hν₁
  have hbY : (fun t : ℝ =>
      (∫ ω, Complex.exp ((((t * (Y ω : ℝ)) : ℝ) : ℂ) * Complex.I) ∂μ) - 1 -
      (((∫ ω, (Y ω : ℝ) ∂μ) : ℝ) : ℂ) * Complex.I * (t : ℂ) -
      (if 0 < t then c₂ else starRingEnd ℂ c₂) * (((|t| : ℝ) ^ (1 + ν) : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ (1 + ν)) := by
    convert hb.sub hcentered using 1
    funext t
    dsimp only [Y]
    rw [hEY]
    push_cast
    ring
  have hEYpos := DirectedDistances.Tauberian.integral_natCast_pos_of_higher_order_boundary
    hY hYI hν₀ hν₁ hc₂ hbY
  have hpow (t : ℝ) := DirectedDistances.Tauberian.integral_pow_exp_eq_characteristic
    (μ := μ) (X := Y) t
  have hbYpow : (fun t : ℝ =>
      (∫ ω, Complex.exp ((t : ℂ) * Complex.I) ^ Y ω ∂μ) - 1 -
      (((∫ ω, (Y ω : ℝ) ∂μ) : ℝ) : ℂ) * Complex.I * (t : ℂ) -
      (if 0 < t then c₂ else starRingEnd ℂ c₂) * (((|t| : ℝ) ^ (1 + ν) : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ (1 + ν)) := by
    simpa only [hpow] using hbY
  obtain ⟨hsign, ha, hYtail⟩ := tauberian_above_one Ω μ Y hY
    (∫ ω, (Y ω : ℝ) ∂μ) hEYpos c₂ hc₂ ν hν₀ hν₁ hbYpow
  have hlag : ∀ᵐ ω ∂μ, (Y ω : ℝ) ≤ X ω ∧ X ω < (Y ω : ℝ) + 1 := by
    filter_upwards [DirectedDistances.Tauberian.ae_floor_abs_lag hX₀] with ω hω
    change (Nat.floor |X ω| : ℝ) ≤ X ω ∧ X ω < (Nat.floor |X ω| : ℝ) + 1
    constructor <;> linarith only [hω.1, hω.2]
  exact ⟨hsign, ha,
    DirectedDistances.Tauberian.real_tail_isLittleO_of_ae_unit_lag hX hY hlag hYtail⟩

end DirectedDistances.PaperProofs.AppendixA
