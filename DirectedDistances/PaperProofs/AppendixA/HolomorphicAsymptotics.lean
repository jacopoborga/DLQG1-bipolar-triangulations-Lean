/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.PoissonBoundary

/-! # Appendix A.1: boundary and radial holomorphic asymptotics

Revised manuscript `lem-holo-asymp`,
The total ambient function is constrained only on the closed unit disk.
The two-sided boundary error scale is `|t|^ν`; the radial limit approaches
from positive r, so every sufficiently close evaluation remains in the disk. -/

public section
namespace DirectedDistances.PaperProofs.AppendixA

open Filter Metric
open scoped Topology

/-- Lemma A.1 (`lem-holo-asymp`), with its exact nonzero radial coefficient. -/
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
          =o[𝓝[>] (0 : ℝ)] (fun r : ℝ => r ^ ν) :=
by
  intro ψ hcont hholo ν hν₀ hν₁ c hc hb
  exact DirectedDistances.Tauberian.radial_asymptotic_of_boundary
    hcont hholo hν₀ hν₁ hc hb


end DirectedDistances.PaperProofs.AppendixA
