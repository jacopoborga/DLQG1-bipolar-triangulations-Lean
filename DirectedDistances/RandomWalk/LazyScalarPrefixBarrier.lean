/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.LazySurvivalProbability
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! # The actual scalar finite-prefix barrier mass

Finite probability producer for Lemma 4.10 (`lem-walk-pos-prob`). The literal
source endpoint density is applied to actual integrated uniform words. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory
open scoped ENNReal Topology

/-- Actual endpoint-weighted finite-prefix barrier mass equals the produced
killed-word expectation. No probability formula is a premise. -/
theorem scalarLazyPrefix_barrier_real (n s a : ℕ) :
    (((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
      (fun w => fun j : Fin (n + 1) => ((s + a : ℕ) : ℤ) + lazyWordValues w j)).withDensity
        (fun q => if ∀ j, 0 ≤ q j then
          ENNReal.ofReal (((q (Fin.last n) : ℝ) + 1) / ((s + a : ℕ) + 1 : ℝ)) else 0)).real
      {q | ∀ j, (a : ℤ) ≤ q j} =
      lazyWordKilledAverage n s
        (fun y => ((y : ℝ) + 1 + (a : ℝ)) / ((s + a : ℕ) + 1 : ℝ)) := by
  classical
  let μ := Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))
  let T : (Fin n → Fin 3) → Fin (n + 1) → ℤ :=
    fun w j => ((s + a : ℕ) : ℤ) + lazyWordValues w j
  let ρ : (Fin (n + 1) → ℤ) → ℝ≥0∞ := fun q =>
    if ∀ j, 0 ≤ q j then
      ENNReal.ofReal (((q (Fin.last n) : ℝ) + 1) / ((s + a : ℕ) + 1 : ℝ)) else 0
  let E : Set (Fin (n + 1) → ℤ) := {q | ∀ j, (a : ℤ) ≤ q j}
  let F : ℤ → ℝ := fun y => ((y : ℝ) + 1 + (a : ℝ)) / ((s + a : ℕ) + 1 : ℝ)
  have hE : MeasurableSet E := (Set.to_countable _).measurableSet
  have hpoint (w : Fin n → Fin 3) :
      E.indicator ρ (T w) = ENNReal.ofReal (lazyWordKilledPayoff s F w) := by
    have he : T w ∈ E ↔ LazyWordSurvives s w := by
      change (∀ j, (a : ℤ) ≤ ((s + a : ℕ) : ℤ) + lazyWordValues w j) ↔
        ∀ j, 0 ≤ (s : ℤ) + lazyWordValues w j
      simp only [Nat.cast_add]
      constructor <;> intro h j <;> have := h j <;> omega
    by_cases hw : LazyWordSurvives s w
    · have hmem := he.mpr hw
      rw [Set.indicator_of_mem hmem]
      have hpos : ∀ j, 0 ≤ T w j := by
        intro j
        have := hmem j
        omega
      change (if ∀ j, 0 ≤ T w j then _ else _) = _
      rw [ite_eq_left hpos]
      unfold lazyWordKilledPayoff
      rw [ite_eq_left hw]
      congr 1
      dsimp [T, F]
      simp only [Int.cast_add, Int.cast_natCast, Nat.cast_add]
      ring
    · rw [Set.indicator_of_notMem (mt he.mp hw)]
      unfold lazyWordKilledPayoff
      rw [ite_eq_right hw, ENNReal.ofReal_zero]
  have hn (w : Fin n → Fin 3) : 0 ≤ lazyWordKilledPayoff s F w := by
    unfold lazyWordKilledPayoff
    split_ifs with hw
    · dsimp [F]
      have hy := hw (Fin.last n)
      have hyr : (0 : ℝ) ≤ ((s : ℤ) + lazyWordValues w (Fin.last n) : ℤ) := by
        exact_mod_cast hy
      exact div_nonneg (by positivity) (by positivity)
    · exact le_rfl
  have hμ : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    dsimp [μ]
    rw [Measure.uniformOfFinset_apply]
    simp only [Set.mem_univ, Finset.filter_true, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    exact ENNReal.div_self (by positivity) (by norm_num)
  change ((μ.map T).withDensity ρ).real E = lazyWordKilledAverage n s F
  rw [Measure.real, withDensity_apply _ hE, ← lintegral_indicator hE,
    lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  simp_rw [hpoint]
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.of_finite)
    (Filter.Eventually.of_forall hn)]
  rw [ENNReal.toReal_ofReal (integral_nonneg hn)]
  exact integral_uniform_lazyWordKilledPayoff n s F

end DirectedDistances.RandomWalk
