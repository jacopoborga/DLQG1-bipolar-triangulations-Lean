/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.DivergentBlockMass
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Order.Interval.Finset.Nat
meta import Lean.Elab.Tactic.Omega

/-! # Weighted half-block lower bound

Generic finite-sum step preceding the final summation of Lemma 4.12
The joint form `μ (B n ∩ F n)` replaces the printed conditional probability
in (4.13), so no positive-mass conditioning is formed. The inputs (4.13) and
(4.14) are hypotheses here; this module proves neither them nor the lemma. -/

public section

namespace DirectedDistances.Probability

open MeasureTheory Filter
open scoped ENNReal

/-- Elementary finite-sum form: a per-index weighted comparison with weight
`(101 √n)⁻¹` and a half-block lower bound `p √N` for `f` give the uniform lower
bound `p / 101` for `g` on every half block with `N ≥ 100`. -/
theorem halfBlock_weighted_sum_lower_bound
    (f g : ℕ → ℝ) (p : ℝ)
    (hf : ∀ n, 0 ≤ f n)
    (hfg : ∀ n : ℕ, 1 ≤ n → (1 / 101) * (Real.sqrt n)⁻¹ * f n ≤ g n)
    (hblock : ∀ N : ℕ, 100 ≤ N →
      p * Real.sqrt N ≤ ∑ n ∈ Finset.Icc ((N + 1) / 2) N, f n) :
    ∀ N : ℕ, 100 ≤ N →
      p / 101 ≤ ∑ n ∈ Finset.Icc ((N + 1) / 2) N, g n := by
  intro N hN
  have hNpos : (0 : ℝ) < Real.sqrt N :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have hterm : ∀ n ∈ Finset.Icc ((N + 1) / 2) N,
      (1 / 101) * (Real.sqrt N)⁻¹ * f n ≤ g n := by
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    have h1 : 1 ≤ n := by omega
    have hnpos : (0 : ℝ) < Real.sqrt n :=
      Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
    have hle : Real.sqrt n ≤ Real.sqrt N :=
      Real.sqrt_le_sqrt (by exact_mod_cast hn'.2)
    have hinv : (Real.sqrt N)⁻¹ ≤ (Real.sqrt n)⁻¹ := inv_anti₀ hnpos hle
    calc (1 / 101) * (Real.sqrt N)⁻¹ * f n
        ≤ (1 / 101) * (Real.sqrt n)⁻¹ * f n :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hinv (by norm_num)) (hf n)
      _ ≤ g n := hfg n h1
  have hsum : (1 / 101) * (Real.sqrt N)⁻¹ * ∑ n ∈ Finset.Icc ((N + 1) / 2) N, f n ≤
      ∑ n ∈ Finset.Icc ((N + 1) / 2) N, g n := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hscale : (1 / 101) * (Real.sqrt N)⁻¹ * (p * Real.sqrt N) ≤
      (1 / 101) * (Real.sqrt N)⁻¹ * ∑ n ∈ Finset.Icc ((N + 1) / 2) N, f n :=
    mul_le_mul_of_nonneg_left (hblock N hN) (by positivity)
  have heq : (1 / 101) * (Real.sqrt N)⁻¹ * (p * Real.sqrt N) = p / 101 := by
    calc (1 / 101) * (Real.sqrt N)⁻¹ * (p * Real.sqrt N)
        = p / 101 * ((Real.sqrt N)⁻¹ * Real.sqrt N) := by ring
      _ = p / 101 := by rw [inv_mul_cancel₀ hNpos.ne', mul_one]
  exact heq.symm.le.trans (hscale.trans hsum)

/-- Finite-measure specialization: joint restricted mass `μ (B n ∩ F n)`,
containment `F n ⊆ A n`, and a half-block mass bound with one `p` give the
lower bound `p / 101` for `∑ μ (A n ∩ B n)` on every half block, `N ≥ 100`. -/
theorem halfBlock_sum_inter_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (A B F : ℕ → Set Ω) (p : ℝ)
    (hFA : ∀ n, 1 ≤ n → F n ⊆ A n)
    (hjoint : ∀ n : ℕ, 1 ≤ n →
      (1 / 101) * (Real.sqrt n)⁻¹ * μ.real (F n) ≤ μ.real (B n ∩ F n))
    (hblock : ∀ N : ℕ, 100 ≤ N →
      p * Real.sqrt N ≤ ∑ n ∈ Finset.Icc ((N + 1) / 2) N, μ.real (F n)) :
    ∀ N : ℕ, 100 ≤ N →
      p / 101 ≤ ∑ n ∈ Finset.Icc ((N + 1) / 2) N, μ.real (A n ∩ B n) := by
  refine halfBlock_weighted_sum_lower_bound (fun n => μ.real (F n))
    (fun n => μ.real (A n ∩ B n)) p (fun _ => measureReal_nonneg) ?_ hblock
  intro n hn
  show (1 / 101) * (Real.sqrt n)⁻¹ * μ.real (F n) ≤ μ.real (A n ∩ B n)
  refine (hjoint n hn).trans (measureReal_mono ?_)
  intro ω hω
  exact ⟨hFA n hn hω.2, hω.1⟩

/-- The shared-constant form: one positive `c`, chosen before `N`, works for
every `N ≥ 100`. -/
theorem exists_pos_halfBlock_sum_inter_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (A B F : ℕ → Set Ω) (p : ℝ) (hp : 0 < p)
    (hFA : ∀ n, 1 ≤ n → F n ⊆ A n)
    (hjoint : ∀ n : ℕ, 1 ≤ n →
      (1 / 101) * (Real.sqrt n)⁻¹ * μ.real (F n) ≤ μ.real (B n ∩ F n))
    (hblock : ∀ N : ℕ, 100 ≤ N →
      p * Real.sqrt N ≤ ∑ n ∈ Finset.Icc ((N + 1) / 2) N, μ.real (F n)) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 100 ≤ N →
      c ≤ ∑ n ∈ Finset.Icc ((N + 1) / 2) N, μ.real (A n ∩ B n) :=
  ⟨p / 101, by positivity,
    halfBlock_sum_inter_lower_bound μ A B F p hFA hjoint hblock⟩

/-- Real half-block lower bounds with one shared positive constant force divergence. -/
theorem tsum_measure_eq_top_of_halfBlock_measureReal
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (G : ℕ → Set Ω) (c : ℝ) (hc : 0 < c)
    (hblock : ∀ N : ℕ, 100 ≤ N → c ≤ ∑ n ∈ Finset.Icc ((N + 1) / 2) N, μ.real (G n)) :
    ∑' n, μ (G n) = ∞ := by
  refine tsum_eq_top_of_eventually_le_sum_half_block (fun n => μ (G n))
    (ENNReal.ofReal c) (ENNReal.ofReal_pos.mpr hc) ?_
  filter_upwards [eventually_ge_atTop 100] with N hN
  calc ENNReal.ofReal c
      ≤ ENNReal.ofReal (∑ n ∈ Finset.Icc ((N + 1) / 2) N, μ.real (G n)) :=
        ENNReal.ofReal_le_ofReal (hblock N hN)
    _ = ∑ n ∈ Finset.Icc ((N + 1) / 2) N, ENNReal.ofReal (μ.real (G n)) :=
        ENNReal.ofReal_sum_of_nonneg (fun _ _ => measureReal_nonneg)
    _ = ∑ n ∈ Finset.Icc ((N + 1) / 2) N, μ (G n) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        exact ENNReal.ofReal_toReal (measure_ne_top μ _)

/-- Divergence of the joint masses from the weighted comparison and the block bound. -/
theorem tsum_measure_inter_eq_top_of_weighted_halfBlock
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (A B F : ℕ → Set Ω) (p : ℝ) (hp : 0 < p)
    (hFA : ∀ n, 1 ≤ n → F n ⊆ A n)
    (hjoint : ∀ n : ℕ, 1 ≤ n →
      (1 / 101) * (Real.sqrt n)⁻¹ * μ.real (F n) ≤ μ.real (B n ∩ F n))
    (hblock : ∀ N : ℕ, 100 ≤ N →
      p * Real.sqrt N ≤ ∑ n ∈ Finset.Icc ((N + 1) / 2) N, μ.real (F n)) :
    ∑' n, μ (A n ∩ B n) = ∞ :=
  tsum_measure_eq_top_of_halfBlock_measureReal μ (fun n => A n ∩ B n) (p / 101)
    (by positivity) (halfBlock_sum_inter_lower_bound μ A B F p hFA hjoint hblock)

/-- The same divergence indexed from `n = 1`, as printed (`∑_{n=1}^∞`). -/
theorem tsum_measure_inter_succ_eq_top_of_weighted_halfBlock
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (A B F : ℕ → Set Ω) (p : ℝ) (hp : 0 < p)
    (hFA : ∀ n, 1 ≤ n → F n ⊆ A n)
    (hjoint : ∀ n : ℕ, 1 ≤ n →
      (1 / 101) * (Real.sqrt n)⁻¹ * μ.real (F n) ≤ μ.real (B n ∩ F n))
    (hblock : ∀ N : ℕ, 100 ≤ N →
      p * Real.sqrt N ≤ ∑ n ∈ Finset.Icc ((N + 1) / 2) N, μ.real (F n)) :
    ∑' n, μ (A (n + 1) ∩ B (n + 1)) = ∞ :=
  ENNReal.tsum_add_one_eq_top
    (f := fun n => μ (A n ∩ B n))
    (tsum_measure_inter_eq_top_of_weighted_halfBlock μ A B F p hp hFA hjoint hblock)
    (measure_ne_top μ _)

end DirectedDistances.Probability
