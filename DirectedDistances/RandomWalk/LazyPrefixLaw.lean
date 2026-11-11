/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Distributions.Uniform







public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Independent uniform three-valued increments have the actual uniform
joint law on each finite prefix. No joint-law premise is assumed. -/
theorem map_lazy_prefix_eq_uniform {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : ℕ → Ω → Fin 3}
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (hlaw : ∀ i, μ.map (ξ i) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin 3))) (n : ℕ) :
    μ.map (fun ω => fun i : Fin n => ξ (i : ℕ) ω) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3)) := by
  have hfin : iIndepFun (fun i : Fin n => ξ (i : ℕ)) μ :=
    iIndepFun.precomp Fin.val_injective hind
  have hmap := iIndepFun.map_fun_eq_pi_map
    (fun i : Fin n => (hξ (i : ℕ)).aemeasurable) hfin
  apply Measure.ext_of_singleton
  intro w
  rw [hmap, Measure.pi_singleton]
  simp only [hlaw, Measure.uniformOfFinset_apply_singleton, Finset.mem_univ,
    ite_true, Finset.card_univ, Fintype.card_fin, Finset.prod_const,
    Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]

/-- Every actual finite word has probability `3^(-n)`, including probability
one for the unique empty word when `n=0`. -/
theorem measure_lazy_prefix_word {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : ℕ → Ω → Fin 3}
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (hlaw : ∀ i, μ.map (ξ i) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin 3)))
    (n : ℕ) (w : Fin n → Fin 3) :
    μ {ω | (fun i : Fin n => ξ (i : ℕ) ω) = w} = ((3 : ℝ≥0∞) ^ n)⁻¹ := by
  have hmeas : Measurable (fun ω => fun i : Fin n => ξ (i : ℕ) ω) :=
    Measurable.of_eval (fun i : Fin n => hξ (i : ℕ))
  rw [show {ω | (fun i : Fin n => ξ (i : ℕ) ω) = w} =
      (fun ω => fun i : Fin n => ξ (i : ℕ) ω) ⁻¹' {w} from rfl,
    ← Measure.map_apply hmeas (measurableSet_singleton w),
    map_lazy_prefix_eq_uniform hξ hind hlaw n,
    Measure.uniformOfFinset_apply_singleton]
  simp only [Finset.mem_univ, ite_true, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]

/-- The real word probability is the exact normalized counting weight. -/
theorem measureReal_lazy_prefix_word {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : ℕ → Ω → Fin 3}
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (hlaw : ∀ i, μ.map (ξ i) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin 3)))
    (n : ℕ) (w : Fin n → Fin 3) :
    μ.real {ω | (fun i : Fin n => ξ (i : ℕ) ω) = w} = (1 / 3 : ℝ) ^ n := by
  rw [Measure.real, measure_lazy_prefix_word hξ hind hlaw n w,
    ENNReal.toReal_inv, ENNReal.toReal_pow]
  simp only [ENNReal.toReal_ofNat, one_div, inv_pow]

end DirectedDistances.RandomWalk
