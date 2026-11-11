/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.AppendixA.Tauberian
public import DirectedDistances.Tauberian.RealRoundingCharacteristic
public import DirectedDistances.Tauberian.BoundedShiftTails

/-! # Original Appendix A.2 for nonnegative real random variables

with the real-valued standing assumptions at lines 3–9. The actual characteristic
expansion passes to the rounded magnitude, then the checked integer theorem
and actual bounded-lag tail transfer return the same explicit tail constant.
No general-real probability generating function holomorphy is assumed. The
source principal-complex-power boundary interpretation is local near zero. -/

public section
namespace DirectedDistances.PaperProofs.AppendixA
open MeasureTheory Filter
open scoped Topology
universe u

/-- Original-v1 Lemma A.2's sign, positive explicit coefficient and actual
strict real-tail asymptotic, without an integer or moment premise. -/
theorem real_tauberian_below_one :
∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (_hX : Measurable X) (_hX₀ : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (ν : ℝ) (_hν₀ : 0 < ν) (_hν₁ : ν < 1) (c : ℂ) (_hc : c.re ≠ 0),
    (fun t : ℝ =>
      (∫ ω, Complex.exp ((((t * X ω) : ℝ) : ℂ) * Complex.I) ∂μ) - 1 -
      (if 0 < t then c else starRingEnd ℂ c) * (((|t| : ℝ) ^ ν : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν) →
    let a : ℝ := -(c.re / Real.Gamma (1 - ν)) / Real.cos (Real.pi * ν / 2)
    c.re < 0 ∧ 0 < a ∧
      (fun R : ℝ => μ.real {ω | R < X ω} - a * R ^ (-ν))
        =o[atTop] (fun R : ℝ => R ^ (-ν)) := by
  intro Ω _ μ _ X hX hX₀ ν hν₀ hν₁ c hc hb
  let Y : Ω → ℕ := fun ω => Nat.floor |X ω|
  have hY : Measurable Y := DirectedDistances.Tauberian.measurable_floor_abs hX
  have hround := DirectedDistances.Tauberian.CFroundingdifference_isLittleO_abs_rpow
    hX hX₀ hν₀ hν₁
  have hbY : (fun t : ℝ =>
      (∫ ω, Complex.exp ((((t * (Y ω : ℝ)) : ℝ) : ℂ) * Complex.I) ∂μ) - 1 -
      (if 0 < t then c else starRingEnd ℂ c) * (((|t| : ℝ) ^ ν : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν) := by
    convert hb.sub hround using 1
    funext t
    dsimp only [Y]
    ring
  have hpow (t : ℝ) := DirectedDistances.Tauberian.integral_pow_exp_eq_characteristic
    (μ := μ) (X := Y) t
  have hbYpow : (fun t : ℝ =>
      (∫ ω, Complex.exp ((t : ℂ) * Complex.I) ^ Y ω ∂μ) - 1 -
      (if 0 < t then c else starRingEnd ℂ c) * (((|t| : ℝ) ^ ν : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν) := by
    simpa only [hpow] using hbY
  obtain ⟨hsign, ha, hYtail⟩ := tauberian Ω μ Y hY ν hν₀ hν₁ c hc hbYpow
  have hlag : ∀ᵐ ω ∂μ, (Y ω : ℝ) ≤ X ω ∧ X ω < (Y ω : ℝ) + 1 := by
    filter_upwards [DirectedDistances.Tauberian.ae_floor_abs_lag hX₀] with ω hω
    change (Nat.floor |X ω| : ℝ) ≤ X ω ∧ X ω < (Nat.floor |X ω| : ℝ) + 1
    constructor <;> linarith only [hω.1, hω.2]
  exact ⟨hsign, ha,
    DirectedDistances.Tauberian.real_tail_isLittleO_of_ae_unit_lag hX hY hlag hYtail⟩

end DirectedDistances.PaperProofs.AppendixA
