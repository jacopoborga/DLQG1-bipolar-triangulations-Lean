/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.TauberianPower
public import DirectedDistances.Tauberian.TailPowerTransfer

/-! Supporting lemmas for paper labels `lem-tauberian` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.PaperProofs.AppendixA
open MeasureTheory Filter
open scoped Topology
universe u

/-- Lemma A.2 (`lem-tauberian`) with its sign and explicit tail constant. -/
theorem tauberian :
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℕ) (_hX : Measurable X)
    (ν : ℝ) (_hν₀ : 0 < ν) (_hν₁ : ν < 1) (c : ℂ) (_hc : c.re ≠ 0),
    (fun t : ℝ => (∫ ω, Complex.exp ((t : ℂ) * Complex.I) ^ X ω ∂μ) - 1 -
      (if 0 < t then c else starRingEnd ℂ c) * (((|t| : ℝ) ^ ν : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν) →
    let a : ℝ := -(c.re / Real.Gamma (1 - ν)) / Real.cos (Real.pi * ν / 2)
    c.re < 0 ∧ 0 < a ∧
      (fun R : ℝ => μ.real {ω | R < (X ω : ℝ)} - a * R ^ (-ν))
        =o[atTop] (fun R : ℝ => R ^ (-ν)) := by
  intro Ω _ μ _ X hX ν hν₀ hν₁ c hc hb
  let f : ℕ → ℝ := fun k => (μ (X ⁻¹' {k})).toReal
  have hf : ∀ k, 0 ≤ f k := fun k => ENNReal.toReal_nonneg
  have hs : HasSum f 1 := DirectedDistances.Tauberian.hasSum_probability_fiber hX
  have hφ (t : ℝ) : (∫ ω, Complex.exp ((t : ℂ) * Complex.I) ^ X ω ∂μ) =
      ∑' k : ℕ, (f k : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ^ k :=
    DirectedDistances.Tauberian.integral_pow_eq_tsum_probability_fiber hX
      (le_of_eq (Complex.norm_exp_ofReal_mul_I t))
  have hb' : (fun t : ℝ =>
      (∑' k, (f k : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ^ k) - 1 -
        (if 0 < t then c else starRingEnd ℂ c) * (((|t| : ℝ) ^ ν : ℝ) : ℂ))
        =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν) := by
    simpa only [hφ] using hb
  have hsign := DirectedDistances.Tauberian.re_neg_of_boundary_pgf_expansion
    hf hs hν₀ hν₁ hc hb'
  have htail := DirectedDistances.Tauberian.tendsto_tail_power_of_boundary_expansion
    hf hs hν₀ hν₁ hc hb'
  obtain ⟨hη, -⟩ := DirectedDistances.Tauberian.tail_laplace_of_boundary_expansion
    hf hs hν₀ hν₁ hc hb'
  have hΓ : 0 < Real.Gamma (1 - ν) := Real.Gamma_pos_of_pos (sub_pos.mpr hν₁)
  have ha : 0 < -(c.re / Real.Gamma (1 - ν)) / Real.cos (Real.pi * ν / 2) := by
    convert div_pos hη hΓ using 1
    ring
  exact ⟨hsign, ha,
    DirectedDistances.Tauberian.probability_real_tail_isLittleO_of_fiber_tail hX htail⟩

end DirectedDistances.PaperProofs.AppendixA
