 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.AppendixA.TauberianAboveOne

/-!
# Lemma A.3 (`lem-tauberian'`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/









public section
namespace DirectedDistances.Paper.AppendixA
open MeasureTheory Filter
open scoped Topology
universe u


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
        =o[atTop] (fun R : ℝ => R ^ (-ν - 1)) :=
 
by exact DirectedDistances.PaperProofs.AppendixA.tauberian_above_one
 
 

end DirectedDistances.Paper.AppendixA
 
