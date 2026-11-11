/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.LazyTwoDimensionalPrefix
public import DirectedDistances.RandomWalk.ConditionedPrefixWords
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable








public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The actual full two-dimensional prefix retains the entire increment word.
Its first coordinate already determines every source step code. -/
theorem lazyTwoDimensionalPrefix_injective {n : ℕ} (x y : ℤ) :
    Function.Injective (@lazyTwoDimensionalPrefix n x y) := by
  intro w v h
  apply shifted_lazyWordValues_injective x
  funext j
  have hj := congrArg (fun q => (q j).1) h
  exact hj

/-- The true unconditioned two-dimensional prefix gives each actual word
exactly its uniform mass, including the unique empty word. -/
theorem lazyTwoDimensionalPrefix_atom {n : ℕ} (x y : ℤ) (w : Fin n → Fin 3) :
    ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
      (lazyTwoDimensionalPrefix x y)) {lazyTwoDimensionalPrefix x y w} =
        ((3 : ℝ≥0∞) ^ n)⁻¹ := by
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : lazyTwoDimensionalPrefix x y ⁻¹' {lazyTwoDimensionalPrefix x y w} = {w} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_singleton_iff,
      (lazyTwoDimensionalPrefix_injective x y).eq_iff]
  rw [he, Measure.uniformOfFinset_apply_singleton]
  simp only [Finset.mem_univ, ↓reduceIte, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]

/-- The literal finite source RN law gives the true atom mass of every full
two-dimensional word, with the whole nonnegative event and endpoint factor. -/
theorem conditionedTwoDimensionalPrefix_atom (n x : ℕ) (y : ℤ)
    (w : Fin n → Fin 3) :
    (((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
      (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
        (fun q => if ∀ j, 0 ≤ (q j).1 then
          ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0))
      {lazyTwoDimensionalPrefix (x : ℤ) y w} =
      (if ∀ j, 0 ≤ (lazyTwoDimensionalPrefix (x : ℤ) y w j).1 then
        ENNReal.ofReal
          ((((lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1 : ℝ) + 1) /
            ((x : ℝ) + 1)) else 0) * ((3 : ℝ≥0∞) ^ n)⁻¹ := by
  rw [withDensity_apply _ (measurableSet_singleton _), lintegral_singleton,
    lazyTwoDimensionalPrefix_atom]

/-- The source all-horizon RN characterization produces actual full-process
cylinder masses. It does not take a scalar or conditional future law as input. -/
theorem conditionedSource_prefix_atom
    (x : ℕ) (y : ℤ) (ν : Measure (ℕ → ℤ × ℤ))
    (hRN : ∀ n : ℕ,
      ν.map (fun q => fun j : Fin (n + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0))
    (n : ℕ) (w : Fin n → Fin 3) :
    ν {p | (fun j : Fin (n + 1) => p j.val) =
      lazyTwoDimensionalPrefix (x : ℤ) y w} =
      (if ∀ j, 0 ≤ (lazyTwoDimensionalPrefix (x : ℤ) y w j).1 then
        ENNReal.ofReal
          ((((lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1 : ℝ) + 1) /
            ((x : ℝ) + 1)) else 0) * ((3 : ℝ≥0∞) ^ n)⁻¹ := by
  have h := congrArg
    (fun μ : Measure (Fin (n + 1) → ℤ × ℤ) =>
      μ {lazyTwoDimensionalPrefix (x : ℤ) y w}) (hRN n)
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _),
    conditionedTwoDimensionalPrefix_atom] at h
  exact h

end DirectedDistances.RandomWalk
