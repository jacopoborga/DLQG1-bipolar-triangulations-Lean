/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.HigherOrderBoundary
public import DirectedDistances.Tauberian.NormalizedBoundary
public import DirectedDistances.Tauberian.IntegratedTailTransfer
public import DirectedDistances.Tauberian.TailPowerTransfer

/-! Supporting lemmas for paper labels `lem-tauberian`, `lem-tauberian'` (see CORRESPONDENCE.md). -/









public section
namespace DirectedDistances.PaperProofs.AppendixA
open MeasureTheory Filter
open scoped Topology
universe u
/-- Revised Lemma A.3 (`lem-tauberian'`), including the imaginary sign,
positivity of its explicit coefficient, and the actual real-cutoff tail. -/
theorem tauberian_above_one :
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℕ) (_hX : Measurable X)
    (c₁ : ℝ) (_hc₁ : 0 < c₁) (c₂ : ℂ) (_hc₂ : c₂.im ≠ 0)
    (ν : ℝ) (_hν₀ : 0 < ν) (_hν₁ : ν < 1),
    (fun t : ℝ => (∫ ω, Complex.exp ((t : ℂ) * Complex.I) ^ X ω ∂μ) - 1 -
      (c₁ : ℂ) * Complex.I * (t : ℂ) -
      (if 0 < t then c₂ else starRingEnd ℂ c₂) * (((|t| : ℝ) ^ (1 + ν) : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ (1 + ν)) →
    let a : ℝ := -(ν / Real.Gamma (1 - ν)) / Real.cos (Real.pi * ν / 2) * c₂.im
    c₂.im < 0 ∧ 0 < a ∧
      (fun R : ℝ => μ.real {ω | R < (X ω : ℝ)} - a * R ^ (-ν - 1))
        =o[atTop] (fun R : ℝ => R ^ (-ν - 1)) := by
  intro Ω _ μ _ X hX c₁ hc₁ c₂ hc₂ ν hν₀ hν₁ hb
  let f : ℕ → ℝ := fun k => (μ (X ⁻¹' {k})).toReal
  have hf : ∀ k, 0 ≤ f k := fun k => ENNReal.toReal_nonneg
  have hs : HasSum f 1 := DirectedDistances.Tauberian.hasSum_probability_fiber hX
  have hφ (t : ℝ) : (∫ ω, Complex.exp ((t : ℂ) * Complex.I) ^ X ω ∂μ) =
      ∑' k : ℕ, (f k : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ^ k :=
    DirectedDistances.Tauberian.integral_pow_eq_tsum_probability_fiber hX
      (le_of_eq (Complex.norm_exp_ofReal_mul_I t))
  have hb' : (fun t : ℝ =>
      (∑' k, (f k : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ^ k) - 1 -
      (c₁ : ℂ) * Complex.I * (t : ℂ) -
      (if 0 < t then c₂ else starRingEnd ℂ c₂) * (((|t| : ℝ) ^ (1 + ν) : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ (1 + ν)) := by
    simpa only [hφ] using hb
  obtain ⟨hm, hmean⟩ := DirectedDistances.Tauberian.first_moment_of_higher_order_boundary
    hf hs hν₀ hb'
  let g : ℕ → ℝ := fun k => (∑' j : ℕ, f (j + (k + 1))) / c₁
  obtain ⟨hg₀, hgs⟩ := DirectedDistances.Tauberian.normalized_tail_coefficients hf hm
    (by rw [hmean]; exact hc₁)
  rw [hmean] at hg₀ hgs
  have hgb := DirectedDistances.Tauberian.normalized_tail_boundary_expansion
    hf hs hm hc₁ hmean hν₀ hν₁ hb'
  rw [hmean] at hgb
  have hc₃ := DirectedDistances.Tauberian.normalized_boundary_coefficient_re_ne_zero hc₁.ne' hc₂
  have hsign := DirectedDistances.Tauberian.re_neg_of_boundary_pgf_expansion
    hg₀ hgs hν₀ hν₁ hc₃ hgb
  rw [DirectedDistances.Tauberian.normalized_boundary_coefficient_re hc₁.ne'] at hsign
  have hc₂neg : c₂.im < 0 := by
    simpa only [zero_mul] using (div_lt_iff₀ hc₁).1 hsign
  have hgT := DirectedDistances.Tauberian.tendsto_tail_power_of_boundary_expansion
    hg₀ hgs hν₀ hν₁ hc₃ hgb
  have htail := DirectedDistances.Tauberian.tendsto_tail_power_of_normalized_integrated_tail
    hf hs hm hmean hc₁ hν₀ hgT
  have hconst : ν * c₁ *
      (-((c₂ / ((c₁ : ℂ) * Complex.I)).re / Real.Gamma (1 - ν)) /
        Real.cos (Real.pi * ν / 2)) =
      -(ν / Real.Gamma (1 - ν)) / Real.cos (Real.pi * ν / 2) * c₂.im := by
    rw [DirectedDistances.Tauberian.normalized_boundary_coefficient_re hc₁.ne']
    field_simp [hc₁.ne']
  rw [hconst] at htail
  obtain ⟨hη, -⟩ := DirectedDistances.Tauberian.tail_laplace_of_boundary_expansion
    hg₀ hgs hν₀ hν₁ hc₃ hgb
  have hΓ : 0 < Real.Gamma (1 - ν) := Real.Gamma_pos_of_pos (sub_pos.mpr hν₁)
  have hC : 0 < -((c₂ / ((c₁ : ℂ) * Complex.I)).re / Real.Gamma (1 - ν)) /
      Real.cos (Real.pi * ν / 2) := by
    convert div_pos hη hΓ using 1
    ring
  have ha := mul_pos (mul_pos hν₀ hc₁) hC
  rw [hconst] at ha
  exact ⟨hc₂neg, ha,
    DirectedDistances.Tauberian.probability_real_tail_isLittleO_of_fiber_tail hX htail⟩
end DirectedDistances.PaperProofs.AppendixA
