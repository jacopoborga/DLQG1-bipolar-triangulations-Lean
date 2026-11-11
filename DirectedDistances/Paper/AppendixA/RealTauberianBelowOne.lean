 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.AppendixA.RealTauberianBelowOne
public import DirectedDistances.Tauberian.RealPowerCharacteristic

/-!
# Lemma A.2 (`lem-tauberian`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/









public section
namespace DirectedDistances.Paper.AppendixA
open MeasureTheory Filter
open scoped Topology
universe u



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
        =o[atTop] (fun R : ℝ => R ^ (-ν)) :=
 
by exact DirectedDistances.PaperProofs.AppendixA.real_tauberian_below_one
 
 

end DirectedDistances.Paper.AppendixA
 
