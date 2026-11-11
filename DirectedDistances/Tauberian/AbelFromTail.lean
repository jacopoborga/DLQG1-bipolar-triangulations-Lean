/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.Tails
public import DirectedDistances.Tauberian.ImproperAbel
public import Mathlib.Basic.ENNReal.Inv

/-! # Abel identities from actual nonnegative tails

Infrastructure for the inherited tail hypotheses in `lem:abel`
Finiteness is proved before converting them to real values. This file supplies
both ordered-series and improper-integral consumers of the finite-tail bridge;
it does not seal a source theorem or choose an unreviewed asymptotic encoding. -/

public section
namespace DirectedDistances.Tauberian

open Filter
open scoped Topology Interval ENNReal

/-- For nonnegative sequences, finiteness of any one extended tail is exactly
summability of the full real sequence. -/
theorem finite_ennreal_tail_iff_summable (f : ℕ → ℝ) (hn : ∀ k, 0 ≤ f k) (k : ℕ) :
    (∑' j, ENNReal.ofReal (f (j + k))) ≠ ⊤ ↔ Summable f := by
  constructor
  · exact summable_of_finite_ennreal_tail f hn k
  · intro hf
    exact ((summable_nat_add_iff k).2 hf).tsum_ofReal_ne_top

/-- Once summability is proved, converting the actual extended tail to a real
number gives the genuine real sum. -/
theorem toReal_tsum_tail (f : ℕ → ℝ) (hf : Summable f) (hn : ∀ k, 0 ≤ f k) (k : ℕ) :
    (∑' j, ENNReal.ofReal (f (j + k))).toReal = ∑' j, f (j + k) := by
  rw [← ofReal_tsum_tail f hf hn k,
    ENNReal.toReal_ofReal (tsum_nonneg (fun j => hn (j + k)))]

/-- A finite limit of ratios with finite extended denominators forces a finite
tail, hence summability. This generic bridge does not impose or encode a
particular power asymptotic. Real denominator weights are always finite. -/
theorem summable_of_ennreal_tail_div_tendsto (f : ℕ → ℝ) (hn : ∀ k, 0 ≤ f k)
    (w : ℕ → ℝ) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (ht : Tendsto (fun k : ℕ => (∑' j, ENNReal.ofReal (f (j + k))) /
      ENNReal.ofReal (w k)) atTop (𝓝 c)) : Summable f := by
  obtain ⟨k, hk⟩ := (ht.eventually_lt_const (lt_top_iff_ne_top.2 hc)).exists
  apply summable_of_finite_ennreal_tail f hn k
  intro htop
  rw [htop, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at hk
  exact (lt_irrefl ⊤) hk

/-- Ordered Abel sums written using actual extended tails, with finiteness
derived from one tail. No absolute summability of these transformed terms is assumed. -/
theorem tendsto_sum_ennreal_tail_sin_sub_of_finite_tail (f : ℕ → ℝ)
    (hn : ∀ k, 0 ≤ f k) (k₀ : ℕ)
    (hk : (∑' j, ENNReal.ofReal (f (j + k₀))) ≠ ⊤) (t : ℝ) :
    Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range N,
        (∑' j, ENNReal.ofReal (f (j + (k + 1)))).toReal *
          (Real.sin (((k + 1 : ℕ) : ℝ) * t) - Real.sin ((k : ℝ) * t)))
      atTop (𝓝 (∑' k, f k * Real.sin ((k : ℝ) * t))) := by
  have hf := summable_of_finite_ennreal_tail f hn k₀ hk
  simp_rw [toReal_tsum_tail f hf hn]
  exact tendsto_sum_tail_sin_sub f hf hn t

/-- The improper Abel integral using actual extended tails. The finite-tail input
supplies every summability and finite-value obligation before the analytic theorem
is applied. Positive mesh size is essential for this integral statement. -/
theorem tendsto_integral_ennreal_tail_cos_of_finite_tail (f : ℕ → ℝ)
    (hn : ∀ k, 0 ≤ f k) (k₀ : ℕ)
    (hk : (∑' j, ENNReal.ofReal (f (j + k₀))) ≠ ⊤) {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun R : ℝ => ∫ u in 0..R,
        (∑' j, ENNReal.ofReal (f (j + (⌊u / t⌋₊ + 1)))).toReal * Real.cos u)
      atTop (𝓝 (∑' k, f k * Real.sin ((k : ℝ) * t))) := by
  have hf := summable_of_finite_ennreal_tail f hn k₀ hk
  simp_rw [toReal_tsum_tail f hf hn]
  exact tendsto_integral_tail_cos f hf hn ht

end DirectedDistances.Tauberian
