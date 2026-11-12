/-
Copyright (c) 2026 Jacopo Borga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Paper.AppendixA.Tauberian

/-!
# Lemma A.2: characteristic expansion and a power-law tail

For a measurable nonnegative integer-valued random variable on a probability
space, assume its characteristic function has the displayed two-sided
order-ν expansion, where 0 < ν < 1 and the real part of c is nonzero.
Then Re(c) is negative and the upper tail is asymptotic to a R^(-ν), with
the exact positive constant a displayed below. The negative-t coefficient
is the complex conjugate of c. The tail uses the strict event R < X.

This is the full Nat-valued Lemma A.2 (`lem-tauberian`) in the manuscript
identified by CORRESPONDENCE.json, not the separate real-valued generalization.
All definitions in this statement are standard Mathlib notions: the Bochner
integral, complex exponential/conjugation, little-o, real powers and Gamma.
No project-specific carrier, abstract law or assumed identification is used.
The Solution is obtained from the existing proof without extra assumptions.
This pilot compares only the single declaration named in its configuration;
it neither checks all 90 catalogue entries nor constitutes Palomar registration.
-/

public section
open MeasureTheory Filter
open scoped Topology
universe u
namespace DLQG1.Palomar

theorem tauberian_below_one :
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
  exact DirectedDistances.Paper.AppendixA.tauberian

end DLQG1.Palomar
