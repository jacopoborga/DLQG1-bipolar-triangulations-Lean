 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.AppendixA.Riemann

/-!
# Lemma A.6 (`lem:riemann`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/









public section
namespace DirectedDistances.Paper.AppendixA

open Filter Asymptotics
open scoped Topology Interval

 
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
          =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ ν) :=
 
by exact DirectedDistances.PaperProofs.AppendixA.riemann
 
 

end DirectedDistances.Paper.AppendixA
 
