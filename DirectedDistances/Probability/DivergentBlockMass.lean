/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Order.Interval.Finset.Nat
meta import Lean.Elab.Tactic.Omega

/-! # Divergence from persistent mass in half blocks

Generic analytic infrastructure for the last summation implication of
Lemma 4.12 (`lem-walk-bdy-sum`), unchanged
functional-limit and path-support inputs remain separate obligations.
This module does not prove the paper's probability estimate or lemma. -/

public section

namespace DirectedDistances.Probability

open Filter
open scoped ENNReal Topology

/-- A uniformly positive eventual lower bound for mass in inclusive blocks
`[m, 2m]` forces the full nonnegative sum to be infinite. -/
theorem tsum_eq_top_of_eventually_le_sum_Icc_double
    (f : ℕ → ℝ≥0∞) (c : ℝ≥0∞) (hc : 0 < c)
    (hblock : ∀ᶠ m in atTop, c ≤ ∑ n ∈ Finset.Icc m (2 * m), f n) :
    ∑' n, f n = ∞ := by
  by_contra hfinite
  have htail := ENNReal.tendsto_sum_nat_add f hfinite
  have hbound (m : ℕ) :
      ∑ n ∈ Finset.Icc m (2 * m), f n ≤ ∑' k, f (k + m) := by
    have hreindex :
        ∑ n ∈ Finset.Icc m (2 * m), f n =
          ∑ k ∈ Finset.Icc 0 m, f (k + m) := by
      apply Finset.sum_bij (fun n _ => n - m)
      · intro n hn
        simp only [Finset.mem_Icc] at hn ⊢
        omega
      · intro n hn n' hn' heq
        simp only [Finset.mem_Icc] at hn hn'
        omega
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        refine ⟨k + m, ?_, ?_⟩
        · simp only [Finset.mem_Icc]
          omega
        · omega
      · intro n hn
        have hm := (Finset.mem_Icc.mp hn).1
        rw [Nat.sub_add_cancel hm]
    rw [hreindex]
    exact sum_le_tsum (Finset.Icc 0 m)
  have hc0 : c ≤ 0 := ge_of_tendsto htail (hblock.mono fun m hm => hm.trans (hbound m))
  exact (not_le_of_gt hc) hc0

/-- The inclusive integer half blocks `[⌈N/2⌉, N]` appearing in the final
summation step of Lemma 4.12 suffice for divergence. This implication requires
the actual block lower bounds as inputs and supplies no probability estimate. -/
theorem tsum_eq_top_of_eventually_le_sum_half_block
    (f : ℕ → ℝ≥0∞) (c : ℝ≥0∞) (hc : 0 < c)
    (hblock : ∀ᶠ N in atTop,
      c ≤ ∑ n ∈ Finset.Icc ((N + 1) / 2) N, f n) :
    ∑' n, f n = ∞ := by
  apply tsum_eq_top_of_eventually_le_sum_Icc_double f c hc
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hblock
  apply eventually_atTop.mpr
  refine ⟨N₀, fun m hm => ?_⟩
  have h := hN₀ (2 * m) (by omega)
  have hhalf : (2 * m + 1) / 2 = m := by omega
  simpa only [hhalf] using h

end DirectedDistances.Probability
