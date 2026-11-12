/-
Copyright (c) 2026 Jacopo Borga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# The six numbered lemmas in Appendix A

These are the full accepted statements of Lemmas A.1--A.6 in the manuscript
identified in CORRESPONDENCE.json, under its disclosed formulation conventions.
All mathematical notions below are standard Mathlib definitions; no unspecified
project map, law, transport hypothesis or definition hole appears here.

* A.1 transfers a two-sided boundary asymptotic of a continuous closed-disk,
  open-disk holomorphic function to a radial asymptotic, with its exact constant.
* A.2: for a measurable Nat-valued random variable, a characteristic expansion
  of order ν in (0,1) gives a negative real coefficient and a positive power-tail
  constant. The conjugation, strict tail event and Gamma/cosine constant are exact.
* A.3 retains the positive linear coefficient, nonzero imaginary next coefficient,
  its negative sign, and the power-tail exponent −ν−1 and explicit constant.
* A.4 proves positivity for the sine transform of nonnegative weights with the
  stated regularly varying tail, for all sufficiently small positive times.
* A.5 identifies its convergent sine series, Abel sums and improper integral.
* A.6 identifies the improper Gamma integral and its discrete Riemann integrals,
  retaining the shared witnesses and both O(t) and o(t^ν) estimates.

Every quantifier, endpoint case, integrability/convergence clause and constant
is copied from the corresponding existing source-facing theorem. Solutions use
those proofs directly. The real-valued A.2/A.3 generalizations are not selected.
This configuration checks only these six entries; the full 90-item catalogue
remains in CORRESPONDENCE.md. No intake or registration is represented here.
-/

public section
open MeasureTheory Filter Metric Asymptotics
open scoped Topology Interval ENNReal
universe u
namespace DLQG1.Palomar.AppendixA

theorem holomorphic_asymptotic :
    ∀ (ψ : ℂ → ℂ)
    (_hcont : ContinuousOn ψ (closedBall (0 : ℂ) 1))
    (_hholo : DifferentiableOn ℂ ψ (ball (0 : ℂ) 1))
    (ν : ℝ) (_hν₀ : 0 < ν) (_hν₁ : ν < 1)
    (c : ℂ) (_hc : c.re ≠ 0),
    (fun t : ℝ => ψ (Complex.exp ((t : ℂ) * Complex.I)) - 1 -
      (if 0 < t then c else starRingEnd ℂ c) * (((|t| : ℝ) ^ ν : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν) →
    let b : ℝ := c.re / Real.cos (Real.pi * ν / 2)
    b ≠ 0 ∧
      (fun r : ℝ => ψ (((1 - r : ℝ) : ℂ)) - 1 -
        (b : ℂ) * (((r ^ ν : ℝ)) : ℂ))
          =o[𝓝[>] (0 : ℝ)] (fun r : ℝ => r ^ ν) := by
  sorry

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
  sorry

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
  sorry

theorem positive_sine :
    ∀ (f : ℕ → ℝ) (hf_nonneg : ∀ k, 0 ≤ f k) (c' ν : ℝ)
    (_hc : 0 < c') (_hν₀ : 0 < ν) (_hν₁ : ν < 1)
    (hTail : Tendsto (fun k : ℕ => (∑' j, ENNReal.ofReal (f (j + k))) /
      ENNReal.ofReal ((k : ℝ) ^ (-ν))) atTop (𝓝 (ENNReal.ofReal c'))),
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
      HasSum (fun k : ℕ => f k * Real.sin (t * (k : ℝ)))
        (∑' k, f k * Real.sin (t * (k : ℝ))) ∧
      0 < ∑' k, f k * Real.sin (t * (k : ℝ)) := by
  sorry

theorem abel :
    ∀ (f : ℕ → ℝ) (hf_nonneg : ∀ k, 0 ≤ f k) (c' ν : ℝ)
    (_hc : 0 < c') (_hν₀ : 0 < ν) (_hν₁ : ν < 1)
    (hTail : Tendsto (fun k : ℕ => (∑' j, ENNReal.ofReal (f (j + k))) /
      ENNReal.ofReal ((k : ℝ) ^ (-ν))) atTop (𝓝 (ENNReal.ofReal c')))
    (t : ℝ) (ht : 0 < t),
    HasSum (fun k : ℕ => f k * Real.sin (t * (k : ℝ)))
        (∑' k, f k * Real.sin (t * (k : ℝ))) ∧
      Tendsto
        (fun N : ℕ => ∑ k ∈ Finset.range N,
          (∑' j, ENNReal.ofReal (f (j + (k + 1)))).toReal *
            (Real.sin (((k + 1 : ℕ) : ℝ) * t) - Real.sin ((k : ℝ) * t)))
        atTop (𝓝 (∑' k, f k * Real.sin (t * (k : ℝ)))) ∧
      Tendsto
        (fun R : ℝ => ∫ u in 0..R,
          (∑' j, ENNReal.ofReal (f (j + (⌊u / t⌋₊ + 1)))).toReal * Real.cos u)
        atTop (𝓝 (∑' k, f k * Real.sin (t * (k : ℝ)))) := by
  sorry

theorem riemann : ∀ (ν : ℝ) (_hν₀ : 0 < ν) (_hν₁ : ν < 1),
    ∃ (J : ℝ) (I : ℝ → ℝ),
      (∀ R : ℝ, 0 ≤ R → IntervalIntegrable
        (fun u : ℝ => u ^ (-ν) * Real.cos u) MeasureTheory.volume 0 R) ∧
      (∀ t : ℝ, 0 < t → ∀ R : ℝ, 0 ≤ R → IntervalIntegrable
        (fun u : ℝ => (((⌊u / t⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) * Real.cos u)
          MeasureTheory.volume 0 R) ∧
      Tendsto (fun R : ℝ => ∫ u : ℝ in (0 : ℝ)..R, u ^ (-ν) * Real.cos u)
        atTop (𝓝 J) ∧
      J = Real.Gamma (1 - ν) * Real.sin (Real.pi * ν / 2) ∧
      (∀ t : ℝ, 0 < t → Tendsto (fun R : ℝ => ∫ u : ℝ in (0 : ℝ)..R,
        (((⌊u / t⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) * Real.cos u) atTop (𝓝 (I t))) ∧
      (fun t : ℝ => I t - t ^ ν * J) =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t) ∧
      (fun t : ℝ => I t -
        (Real.Gamma (1 - ν) * Real.sin (Real.pi * ν / 2)) * t ^ ν)
          =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ ν) := by
  sorry

end DLQG1.Palomar.AppendixA
