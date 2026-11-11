 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section6.Tauberian

/-!
# Proposition 6.1 (`prop:Tauberian`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/








public section
namespace DirectedDistances.Paper.Section6
open MeasureTheory Filter
open scoped Topology
universe u


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
        =o[atTop] (fun R : ℝ => R ^ (-ν - 1))) :=
 
by exact DirectedDistances.PaperProofs.Section6.tauberian_characteristic
 
 

end DirectedDistances.Paper.Section6
 
