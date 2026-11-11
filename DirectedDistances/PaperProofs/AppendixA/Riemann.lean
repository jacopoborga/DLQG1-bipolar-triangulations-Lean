/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.MellinCos
import DirectedDistances.Tauberian.ImproperAbel

/-! # Appendix A.6: power staircase asymptotics

Revised manuscript `lem:riemann`,
The two improper integrals have certified interval integrability at every
nonnegative cutoff and arbitrary-real-cutoff limits.
One common power integral value and one staircase transform work for every
positive scale. The two remainder scales are stated separately. -/

public section
namespace DirectedDistances.PaperProofs.AppendixA

open Filter Asymptotics
open scoped Topology Interval

/-- Lemma A.6 (`lem:riemann`), including both asymptotic equalities. -/
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
by
  intro ν hν₀ hν₁
  obtain ⟨J, I, hJ, hval, hI, _hb, hbig, hlittle⟩ :=
    DirectedDistances.Tauberian.exists_staircase_power_cos_gamma_asymptotics hν₀ hν₁
  refine ⟨J, I, ?_, ?_, hJ, hval, hI, hbig, hlittle⟩
  · intro R _hR
    exact DirectedDistances.Tauberian.intervalIntegrable_power_cos hν₁
  · intro t ht R hR
    exact DirectedDistances.Tauberian.intervalIntegrable_staircase_cos
      (fun n : ℕ => (n : ℝ) ^ (-ν)) ht hR


end DirectedDistances.PaperProofs.AppendixA
