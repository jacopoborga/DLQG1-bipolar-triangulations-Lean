/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.AbelFromTail
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Supporting lemmas for paper labels `lem:bound-im-part` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.Tauberian

open Filter
open scoped Topology ENNReal

/-- Actual tails of a nonnegative real sequence are nonnegative. -/
theorem real_tail_nonneg (f : ℕ → ℝ) (hn : ∀ k, 0 ≤ f k) (n : ℕ) :
    0 ≤ ∑' j, f (j + n) :=
  tsum_nonneg (fun j => hn (j + n))

/-- Once summability is established, the actual nonnegative tails decrease. -/
theorem real_tail_antitone (f : ℕ → ℝ) (hf : Summable f) (hn : ∀ k, 0 ≤ f k) :
    Antitone (fun n : ℕ => ∑' j, f (j + n)) := by
  apply antitone_nat_of_succ_le
  intro n
  have hh := eq_tsum_tail_sub f hf n
  linarith only [hh, hn n]

/-- Genuine summable real tails tend to zero, with no default-zero argument. -/
theorem tendsto_real_tail_zero (f : ℕ → ℝ) (hf : Summable f) :
    Tendsto (fun n : ℕ => ∑' j, f (j + n)) atTop (𝓝 0) := by
  have heq (n : ℕ) : (∑' j, f (j + n)) =
      (∑' j, f j) - ∑ k ∈ Finset.range n, f k :=
    (eq_sub_iff_add_eq').2 (hf.sum_add_tsum_nat_add n)
  simp_rw [heq]
  simpa only [sub_self] using (tendsto_const_nhds (x := ∑' j, f j)).sub
    hf.hasSum.tendsto_sum_nat

/-- The actual extended-tail asymptotic forces summability and passes to the
genuine real-tail quotient. The output also supplies all order and vanishing
facts needed to use the real tails in the A.4 analytic argument. -/
theorem real_tail_properties_of_ennreal_power_ratio (f : ℕ → ℝ)
    (hn : ∀ k, 0 ≤ f k) (c' ν : ℝ) (hc : 0 < c')
    (_hν₀ : 0 < ν) (_hν₁ : ν < 1)
    (hTail : Tendsto (fun k : ℕ => (∑' j, ENNReal.ofReal (f (j + k))) /
      ENNReal.ofReal ((k : ℝ) ^ (-ν))) atTop (𝓝 (ENNReal.ofReal c'))) :
    Summable f ∧
      Tendsto (fun n : ℕ => (∑' j, f (j + n)) / (n : ℝ) ^ (-ν)) atTop (𝓝 c') ∧
      (∀ n : ℕ, 0 ≤ ∑' j, f (j + n)) ∧
      Antitone (fun n : ℕ => ∑' j, f (j + n)) ∧
      Tendsto (fun n : ℕ => ∑' j, f (j + n)) atTop (𝓝 0) := by
  have hf := summable_of_ennreal_tail_div_tendsto f hn
    (fun k : ℕ => (k : ℝ) ^ (-ν)) ENNReal.ofReal_ne_top hTail
  refine ⟨hf, ?_, real_tail_nonneg f hn, real_tail_antitone f hf hn,
    tendsto_real_tail_zero f hf⟩
  have ht := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hTail
  rw [ENNReal.toReal_ofReal hc.le] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun n => by
    dsimp only [Function.comp_def]
    rw [ENNReal.toReal_div, toReal_tsum_tail f hf hn,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (Nat.cast_nonneg n) _)])

/-- The source's leading oscillatory coefficient is strictly positive on its
entire exponent domain. -/
theorem gamma_sin_coefficient_pos {ν : ℝ} (hν₀ : 0 < ν) (hν₁ : ν < 1) :
    0 < Real.Gamma (1 - ν) * Real.sin (Real.pi * ν / 2) := by
  apply mul_pos (Real.Gamma_pos_of_pos (sub_pos.2 hν₁))
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact div_pos (mul_pos Real.pi_pos hν₀) (by norm_num)
  · have hh := mul_lt_mul_of_pos_left hν₁ Real.pi_pos
    linarith only [hh, Real.pi_pos]

end DirectedDistances.Tauberian
