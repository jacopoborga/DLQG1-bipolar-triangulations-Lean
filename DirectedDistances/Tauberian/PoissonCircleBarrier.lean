/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.PoissonBarrier
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith

/-! # From local angle control to a global circle barrier

Dependencies of Appendix A.1 (`lem-holo-asymp`). The closed angle interval
retains both occurrences of -1 at its endpoints. The correction weight
`1-cos(t)` is positive except at the distinguished point t=0. Every point of
the unit circle is recovered through its principal argument. -/

public section
namespace DirectedDistances.Tauberian

open Set Filter Metric Complex
open scoped Topology

/-- A local angle bound extends to the entire unit circle, with a linear
harmonic correction. No continuity of the majorizing weight is needed. -/
theorem exists_global_circle_barrier_from_angle (e : ℂ → ℂ) (q : ℂ → ℝ)
    (he : ContinuousOn e (sphere (0 : ℂ) 1))
    (hq : ∀ z ∈ sphere (0 : ℂ) 1, 0 ≤ q z) {ε : ℝ} (hε : 0 ≤ ε)
    (hlocal : ∀ᶠ t : ℝ in 𝓝 0,
      ‖e (Complex.exp ((t : ℂ) * I))‖ ≤ ε * q (Complex.exp ((t : ℂ) * I))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ sphere (0 : ℂ) 1,
      ‖e z‖ ≤ ε * q z + C * (1 - z.re) := by
  have hc (t : ℝ) : Complex.exp ((t : ℂ) * I) ∈ sphere (0 : ℂ) 1 := by
    simp only [mem_sphere, dist_zero_right, norm_exp_ofReal_mul_I]
  have he' : ContinuousOn (fun t : ℝ => e (Complex.exp ((t : ℂ) * I)))
      (Icc (-Real.pi) Real.pi) :=
    he.comp (Complex.continuous_ofReal.mul_const I).cexp.continuousOn (fun t _ => hc t)
  have hp : ∀ t ∈ Icc (-Real.pi) Real.pi, t ≠ (0 : ℝ) → 0 < 1 - Real.cos t := by
    intro t ht ht0
    apply sub_pos.2
    by_contra hnot
    have ht₁ : -(2 * Real.pi) < t := by linarith only [ht.1, Real.pi_pos]
    have ht₂ : t < 2 * Real.pi := by linarith only [ht.2, Real.pi_pos]
    exact ht0 ((Real.cos_eq_one_iff_of_lt_of_lt ht₁ ht₂).1
      (le_antisymm (Real.cos_le_one t) (not_lt.1 hnot)))
  obtain ⟨C, hC, hbar⟩ := exists_global_compact_barrier isCompact_Icc (a := (0 : ℝ))
    (fun t : ℝ => e (Complex.exp ((t : ℂ) * I)))
    (fun t : ℝ => 1 - Real.cos t) (fun t : ℝ => q (Complex.exp ((t : ℂ) * I)))
    he' (continuous_const.sub Real.continuous_cos).continuousOn
    (fun t _ => sub_nonneg.2 (Real.cos_le_one t)) hp (fun t _ => hq _ (hc t))
    hε (hlocal.filter_mono nhdsWithin_le_nhds)
  refine ⟨C, hC, ?_⟩
  intro z hz
  have hn : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hz
  have hz' : Complex.exp (((arg z : ℝ) : ℂ) * I) = z := by
    simpa only [hn, ofReal_one, one_mul] using norm_mul_exp_arg_mul_I z
  have hcos : Real.cos (arg z) = z.re := by
    simpa only [hn, one_mul] using norm_mul_cos_arg z
  have hb := hbar (arg z) ⟨(neg_pi_lt_arg z).le, arg_le_pi z⟩
  simpa only [hz', hcos] using hb

end DirectedDistances.Tauberian
