/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.AppendixA.Tauberian
public import DirectedDistances.PaperProofs.AppendixA.TauberianAboveOne
public import DirectedDistances.Tauberian.ImaginaryCoefficient

/-! Supporting lemmas for paper labels `prop:Tauberian` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.PaperProofs.Section6
open MeasureTheory Filter
open scoped Topology
universe u
/-- Proposition 6.1 (`prop:Tauberian`): both characteristic-function
regimes, all coefficient signs, and their actual strict real-tail laws. -/
theorem tauberian_characteristic :
∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℕ) (_hX : Measurable X),
  (∀ (c : ℂ) (_hc : c.re ≠ 0) (ν : ℝ) (_hν₀ : 0 < ν) (_hν₁ : ν < 1),
    (fun t : ℝ =>
      (∫ ω, Complex.exp ((((t * (X ω : ℝ)) : ℝ) : ℂ) * Complex.I) ∂μ) - 1 -
      (if 0 < t then c else starRingEnd ℂ c) * (((|t| : ℝ) ^ ν : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν) →
    let a : ℝ := -(c.re / Real.Gamma (1 - ν)) / Real.cos (Real.pi * ν / 2)
    c.re < 0 ∧ 0 < c.im ∧ 0 < a ∧
      (fun R : ℝ => μ.real {ω | R < (X ω : ℝ)} - a * R ^ (-ν))
        =o[atTop] (fun R : ℝ => R ^ (-ν))) ∧
  (∀ (c₁ : ℝ) (_hc₁ : 0 < c₁) (c₂ : ℂ) (_hc₂ : c₂.im ≠ 0)
      (ν : ℝ) (_hν₀ : 0 < ν) (_hν₁ : ν < 1),
    (fun t : ℝ =>
      (∫ ω, Complex.exp ((((t * (X ω : ℝ)) : ℝ) : ℂ) * Complex.I) ∂μ) - 1 -
      (c₁ : ℂ) * Complex.I * (t : ℂ) -
      (if 0 < t then c₂ else starRingEnd ℂ c₂) * (((|t| : ℝ) ^ (1 + ν) : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ (1 + ν)) →
    let a : ℝ := -((ν * c₂.im) / Real.Gamma (1 - ν)) / Real.cos (Real.pi * ν / 2)
    c₂.im < 0 ∧ 0 < a ∧
      (fun R : ℝ => μ.real {ω | R < (X ω : ℝ)} - a * R ^ (-ν - 1))
        =o[atTop] (fun R : ℝ => R ^ (-ν - 1))) := by
  intro Ω _ μ _ X hX
  have hpow (t : ℝ) := DirectedDistances.Tauberian.integral_pow_exp_eq_characteristic
    (μ := μ) (X := X) t
  constructor
  · intro c hc ν hν₀ hν₁ hb
    have hbpow : (fun t : ℝ =>
        (∫ ω, Complex.exp ((t : ℂ) * Complex.I) ^ X ω ∂μ) - 1 -
        (if 0 < t then c else starRingEnd ℂ c) * (((|t| : ℝ) ^ ν : ℝ) : ℂ))
        =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν) := by
      simpa only [hpow] using hb
    obtain ⟨hre, ha, htail⟩ := DirectedDistances.PaperProofs.AppendixA.tauberian
      Ω μ X hX ν hν₀ hν₁ c hc hbpow
    let f : ℕ → ℝ := fun k => (μ (X ⁻¹' {k})).toReal
    have hf : ∀ k, 0 ≤ f k := fun k => ENNReal.toReal_nonneg
    have hs : HasSum f 1 := DirectedDistances.Tauberian.hasSum_probability_fiber hX
    have hφ (t : ℝ) : (∫ ω, Complex.exp ((t : ℂ) * Complex.I) ^ X ω ∂μ) =
        ∑' k : ℕ, (f k : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ^ k :=
      DirectedDistances.Tauberian.integral_pow_eq_tsum_probability_fiber hX
        (le_of_eq (Complex.norm_exp_ofReal_mul_I t))
    have hbseries : (fun t : ℝ =>
        (∑' k : ℕ, (f k : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ^ k) - 1 -
        (if 0 < t then c else starRingEnd ℂ c) * (((|t| : ℝ) ^ ν : ℝ) : ℂ))
        =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν) := by
      simpa only [hφ] using hbpow
    have him := DirectedDistances.Tauberian.im_pos_of_boundary_pgf_expansion
      hf hs hν₀ hν₁ hc hbseries
    exact ⟨hre, him, ha, htail⟩
  · intro c₁ hc₁ c₂ hc₂ ν hν₀ hν₁ hb
    have hbpow : (fun t : ℝ =>
        (∫ ω, Complex.exp ((t : ℂ) * Complex.I) ^ X ω ∂μ) - 1 -
        (c₁ : ℂ) * Complex.I * (t : ℂ) -
        (if 0 < t then c₂ else starRingEnd ℂ c₂) * (((|t| : ℝ) ^ (1 + ν) : ℝ) : ℂ))
        =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ (1 + ν)) := by
      simpa only [hpow] using hb
    have h := DirectedDistances.PaperProofs.AppendixA.tauberian_above_one
      Ω μ X hX c₁ hc₁ c₂ hc₂ ν hν₀ hν₁ hbpow
    have hconst : -(ν / Real.Gamma (1 - ν)) / Real.cos (Real.pi * ν / 2) * c₂.im =
        -((ν * c₂.im) / Real.Gamma (1 - ν)) / Real.cos (Real.pi * ν / 2) := by ring
    simpa only [hconst] using h
end DirectedDistances.PaperProofs.Section6
