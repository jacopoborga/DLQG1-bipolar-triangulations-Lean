 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.AppendixA.HolomorphicAsymptotics

/-!
# Lemma A.1 (`lem-holo-asymp`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/








public section
namespace DirectedDistances.Paper.AppendixA

open Filter Metric
open scoped Topology

 
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
 
by exact DirectedDistances.PaperProofs.AppendixA.holomorphic_asymptotic
 
 

end DirectedDistances.Paper.AppendixA
 
