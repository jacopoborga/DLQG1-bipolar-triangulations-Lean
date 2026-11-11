/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.AbelFromTail







public section
namespace DirectedDistances.Tauberian

open Filter
open scoped Topology Interval ENNReal

/-- A finite limit of actual tail ratios supplies all three convergence claims,
with one common sine-transform value and no assumed summability or integrability. -/
theorem abel_limits_of_tail_div_tendsto (f : ℕ → ℝ) (hn : ∀ k, 0 ≤ f k)
    (w : ℕ → ℝ) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hlim : Tendsto (fun k : ℕ => (∑' j, ENNReal.ofReal (f (j + k))) /
      ENNReal.ofReal (w k)) atTop (𝓝 c)) {t : ℝ} (ht : 0 < t) :
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
  have hf := summable_of_ennreal_tail_div_tendsto f hn w hc hlim
  have hk : (∑' j, ENNReal.ofReal (f (j + 0))) ≠ ⊤ := by
    simpa only [Nat.add_zero] using hf.tsum_ofReal_ne_top
  constructor
  · simpa only [mul_comm t] using (summable_mul_sin f hf hn t).hasSum
  constructor
  · simpa only [mul_comm t] using
      tendsto_sum_ennreal_tail_sin_sub_of_finite_tail f hn 0 hk t
  · simpa only [mul_comm t] using
      tendsto_integral_ennreal_tail_cos_of_finite_tail f hn 0 hk ht

end DirectedDistances.Tauberian
