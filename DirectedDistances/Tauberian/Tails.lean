/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.AbelSine
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Finite nonnegative tails and genuine summability

Infrastructure for the inherited tail setup of `lem:abel`
infinite values; no real `tsum` default is used to infer that a tail is finite.
These lemmas do not prove a Tauberian asymptotic or an improper-integral identity. -/

public section
namespace DirectedDistances.Tauberian

open Filter
open scoped Topology

/-- One finite extended nonnegative tail forces summability of the whole real
sequence: the omitted initial segment has finitely many terms. -/
theorem summable_of_finite_ennreal_tail (f : ℕ → ℝ) (hn : ∀ k, 0 ≤ f k)
    (k : ℕ) (hk : (∑' j, ENNReal.ofReal (f (j + k))) ≠ ⊤) : Summable f := by
  have ht : Summable (fun j => f (j + k)) := by
    simpa only [ENNReal.toReal_ofReal (hn _)] using ENNReal.summable_toReal hk
  exact (summable_nat_add_iff k).1 ht

/-- If the actual extended nonnegative tails tend to zero, at least one tail is
finite, and the original real sequence is summable. -/
theorem summable_of_ennreal_tail_tendsto_zero (f : ℕ → ℝ) (hn : ∀ k, 0 ≤ f k)
    (ht : Tendsto (fun k : ℕ => ∑' j, ENNReal.ofReal (f (j + k))) atTop (𝓝 0)) :
    Summable f := by
  obtain ⟨k, hk⟩ := (ht.eventually_lt_const ENNReal.zero_lt_top).exists
  exact summable_of_finite_ennreal_tail f hn k hk.ne

/-- After summability is established, the real tail and extended nonnegative tail
agree exactly. This is a value identity, not a change of tail convention. -/
theorem ofReal_tsum_tail (f : ℕ → ℝ) (hf : Summable f) (hn : ∀ k, 0 ≤ f k) (k : ℕ) :
    ENNReal.ofReal (∑' j, f (j + k)) = ∑' j, ENNReal.ofReal (f (j + k)) :=
  ENNReal.ofReal_tsum_of_nonneg (fun j => hn (j + k)) ((summable_nat_add_iff k).2 hf)

/-- The ordered Abel series identity follows from one finite nonnegative tail.
This discharges the summability input without using a real-sum default. -/
theorem tendsto_sum_tail_sin_sub_of_finite_tail (f : ℕ → ℝ) (hn : ∀ k, 0 ≤ f k)
    (k₀ : ℕ) (hk : (∑' j, ENNReal.ofReal (f (j + k₀))) ≠ ⊤) (t : ℝ) :
    Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range N, (∑' j, f (j + (k + 1))) *
        (Real.sin (((k + 1 : ℕ) : ℝ) * t) - Real.sin ((k : ℝ) * t)))
      atTop (𝓝 (∑' k, f k * Real.sin ((k : ℝ) * t))) :=
  tendsto_sum_tail_sin_sub f (summable_of_finite_ennreal_tail f hn k₀ hk) hn t

end DirectedDistances.Tauberian
