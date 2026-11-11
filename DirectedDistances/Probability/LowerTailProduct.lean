/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! # Product bound for the maximum of independent variables with a lower tail

single-increment lower tail bound over `⌊A^{-2/3+ε} n^{1/2}⌋` indices). Nothing here
mentions Busemann functions.

Remark on the uniform hypothesis: since `P.real _ ≤ 1`, the lower tail bound
`c₁ A^{2/3} n^{-1/2} ≤ P[ξ_k ≥ A⁻¹ n^{3/4}]` can only hold when `A^{2/3} ≤ n^{1/2}/c₁`.
Hence it cannot hold for *all* `A > 1` at a fixed `n`. The statements below therefore take
the tail bound at the specific pair `(n, A)` at which the conclusion is drawn, so the
conclusion holds on exactly the range where the tail bound holds (with constants
independent of `n` and `A`). -/

public section
namespace DirectedDistances.Probability
open MeasureTheory ProbabilityTheory Finset




theorem lowerTail_exists_ge_prob {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ} (hmeas : ∀ k, Measurable (ξ k))
    (hind : iIndepFun ξ P) (x p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : ∀ k, p ≤ P.real {ω | x ≤ ξ k ω}) (m : ℕ) :
    1 - (1 - p) ^ m ≤ P.real {ω | ∃ k ∈ Finset.range m, x ≤ ξ k ω} := by
  have hset : {ω | ∃ k ∈ Finset.range m, x ≤ ξ k ω} =
      (⋂ k ∈ Finset.range m, ξ k ⁻¹' Set.Iio x)ᶜ := by
    ext ω; simp
  have hms : MeasurableSet (⋂ k ∈ Finset.range m, ξ k ⁻¹' Set.Iio x) :=
    Finset.measurableSet_biInter _ fun k _ => hmeas k measurableSet_Iio
  have hprod : P (⋂ k ∈ Finset.range m, ξ k ⁻¹' Set.Iio x) =
      ∏ k ∈ Finset.range m, P (ξ k ⁻¹' Set.Iio x) :=
    hind.meas_biInter fun k _ => ⟨Set.Iio x, measurableSet_Iio, rfl⟩
  have hprodR : P.real (⋂ k ∈ Finset.range m, ξ k ⁻¹' Set.Iio x) =
      ∏ k ∈ Finset.range m, P.real (ξ k ⁻¹' Set.Iio x) := by
    simp only [measureReal_def]
    rw [hprod, ENNReal.toReal_prod]
  have hk : ∀ k ∈ Finset.range m, P.real (ξ k ⁻¹' Set.Iio x) ≤ 1 - p := by
    intro k _
    have h1 : ξ k ⁻¹' Set.Iio x = {ω | x ≤ ξ k ω}ᶜ := by ext ω; simp
    have hm : MeasurableSet {ω | x ≤ ξ k ω} := hmeas k measurableSet_Ici
    rw [h1, probReal_compl_eq_one_sub hm]
    linarith [hp k]
  have hle : P.real (⋂ k ∈ Finset.range m, ξ k ⁻¹' Set.Iio x) ≤ (1 - p) ^ m := by
    rw [hprodR]
    calc _ ≤ ∏ _k ∈ Finset.range m, (1 - p) :=
          Finset.prod_le_prod₀ (fun k _ => measureReal_nonneg) hk
      _ = (1 - p) ^ m := by simp
  rw [hset, probReal_compl_eq_one_sub hms]
  linarith

/-- `1 - (1-p)^m ≥ 1 - exp(-(p m))`, so the product bound has exponential form. -/
theorem lowerTail_exists_ge_prob_exp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ} (hmeas : ∀ k, Measurable (ξ k))
    (hind : iIndepFun ξ P) (x p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : ∀ k, p ≤ P.real {ω | x ≤ ξ k ω}) (m : ℕ) :
    1 - Real.exp (-(p * m)) ≤ P.real {ω | ∃ k ∈ Finset.range m, x ≤ ξ k ω} := by
  refine le_trans ?_ (lowerTail_exists_ge_prob hmeas hind x p hp0 hp1 hp m)
  have h1 : (1 - p) ^ m ≤ Real.exp (-(p * m)) := by
    calc (1 - p) ^ m ≤ (Real.exp (-p)) ^ m :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-p)]) m
      _ = Real.exp (-(p * m)) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
  linarith







theorem lowerTail_exists_ge_prob_param {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ} (hmeas : ∀ k, Measurable (ξ k))
    (hind : iIndepFun ξ P) {c₁ : ℝ} (hc₁ : 0 < c₁) (ε : ℝ) :
    ∃ c₂ c₃ : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ ∀ n : ℕ, 1 ≤ n → ∀ A : ℝ, 1 < A →
      (∀ k, c₁ * A ^ (2 / 3 : ℝ) * (n : ℝ) ^ (-1 / 2 : ℝ) ≤
        P.real {ω | A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ) ≤ ξ k ω}) →
      1 - c₂ * Real.exp (-(c₃ * A ^ ε)) ≤
        P.real {ω | ∃ k ∈ Finset.range ⌊A ^ (-2 / 3 + ε : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)⌋₊,
          A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ) ≤ ξ k ω} := by
  refine ⟨Real.exp 1, c₁, Real.exp_pos 1, hc₁, ?_⟩
  intro n hn A hA hp
  have hApos : 0 < A := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set p : ℝ := c₁ * A ^ (2 / 3 : ℝ) * (n : ℝ) ^ (-1 / 2 : ℝ) with hpdef
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := le_trans (hp 0) measureReal_le_one
  set a : ℝ := A ^ (-2 / 3 + ε : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) with hadef
  have hpa : p * a = c₁ * A ^ ε := by
    have e1 : A ^ (2 / 3 : ℝ) * A ^ (-2 / 3 + ε : ℝ) = A ^ ε := by
      rw [← Real.rpow_add hApos]; congr 1; ring
    have e2 : (n : ℝ) ^ (-1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add hnpos]; norm_num
    calc p * a = c₁ * (A ^ (2 / 3 : ℝ) * A ^ (-2 / 3 + ε : ℝ)) *
          ((n : ℝ) ^ (-1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)) := by
          rw [hpdef, hadef]; ring
      _ = c₁ * A ^ ε := by rw [e1, e2]; ring
  have hfl : a - 1 ≤ (⌊a⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one a]
  have hpm : c₁ * A ^ ε - 1 ≤ p * (⌊a⌋₊ : ℝ) := by
    nlinarith
  have key := lowerTail_exists_ge_prob_exp hmeas hind (A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ)) p hp0 hp1
    hp ⌊a⌋₊
  refine le_trans ?_ key
  have : Real.exp (-(p * (⌊a⌋₊ : ℝ))) ≤ Real.exp 1 * Real.exp (-(c₁ * A ^ ε)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
  linarith
