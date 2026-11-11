/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.RegularVariationAbel
public import DirectedDistances.Tauberian.TailAsymptotic
import DirectedDistances.Tauberian.ImproperAbel

/-! # Appendix A.4: positivity of the sine transform

Revised manuscript `lem:bound-im-part`,
The actual nonnegative tail has the power asymptotic stated by the manuscript.
Convergence of the sine series and strict positivity hold on one common
interval `(0,t₀]`, including its upper endpoint. -/

public section
namespace DirectedDistances.PaperProofs.AppendixA

open Filter
open scoped Topology ENNReal

/-- Lemma A.4 (`lem:bound-im-part`) on the full source tail domain. -/
theorem positive_sine :
    ∀ (f : ℕ → ℝ) (hf_nonneg : ∀ k, 0 ≤ f k) (c' ν : ℝ)
    (_hc : 0 < c') (_hν₀ : 0 < ν) (_hν₁ : ν < 1)
    (hTail : Tendsto (fun k : ℕ => (∑' j, ENNReal.ofReal (f (j + k))) /
      ENNReal.ofReal ((k : ℝ) ^ (-ν))) atTop (𝓝 (ENNReal.ofReal c'))),
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
      HasSum (fun k : ℕ => f k * Real.sin (t * (k : ℝ)))
        (∑' k, f k * Real.sin (t * (k : ℝ))) ∧
      0 < ∑' k, f k * Real.sin (t * (k : ℝ)) :=
by
  intro f hn c' ν hc hν₀ hν₁ hTail
  obtain ⟨hf, hratio, hnS, hanti, _hzero⟩ :=
    DirectedDistances.Tauberian.real_tail_properties_of_ennreal_power_ratio
      f hn c' ν hc hν₀ hν₁ hTail
  have hF : ∀ t : ℝ, 0 < t → Tendsto (fun R : ℝ => ∫ u : ℝ in 0..R,
      (∑' j, f (j + (⌊u / t⌋₊ + 1))) * Real.cos u) atTop
        (𝓝 (∑' k, f k * Real.sin (t * (k : ℝ)))) := by
    intro t ht
    simpa only [mul_comm t] using
      DirectedDistances.Tauberian.tendsto_integral_tail_cos f hf hn ht
  have hscaled := DirectedDistances.Tauberian.tendsto_scaled_improper_staircase_cos
    (fun n : ℕ => ∑' j, f (j + n))
    (fun t : ℝ => ∑' k, f k * Real.sin (t * (k : ℝ)))
    hanti hnS hν₀ hν₁ hratio hF
  have hlead : 0 < c' * (Real.Gamma (1 - ν) * Real.sin (Real.pi * ν / 2)) :=
    mul_pos hc (DirectedDistances.Tauberian.gamma_sin_coefficient_pos hν₀ hν₁)
  have hevent := hscaled.eventually (Ioi_mem_nhds hlead)
  obtain ⟨δ, hδ, hδprop⟩ := Metric.mem_nhdsWithin_iff.1 hevent
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro t ht htle
  have hdist : dist t (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    exact htle.trans_lt (half_lt_self hδ)
  have hprod := hδprop ⟨Metric.mem_ball.2 hdist, ht⟩
  have hpos : 0 < ∑' k, f k * Real.sin (t * (k : ℝ)) :=
    (mul_pos_iff_of_pos_left (Real.rpow_pos_of_pos ht (-ν))).1 hprod
  refine ⟨?_, hpos⟩
  simpa only [mul_comm t] using
    (DirectedDistances.Tauberian.summable_mul_sin f hf hn t).hasSum


end DirectedDistances.PaperProofs.AppendixA
