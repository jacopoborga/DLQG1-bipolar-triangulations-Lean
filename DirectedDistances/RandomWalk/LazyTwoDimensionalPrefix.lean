/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.LazySurvivalProbability
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! Supporting lemmas for paper labels `lem-walk-pos-prob` (see CORRESPONDENCE.md). -/











public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- The three literal source increments, indexed in increasing first-coordinate
order. Every code belongs to Fin3, so these are exactly the source steps. -/
@[expose] def lazyTwoDimensionalStep (c : Fin 3) : ℤ × ℤ :=
  ((c : ℤ) - 1, if c = 0 then 0 else if c = 1 then 1 else -1)

@[simp] theorem lazyTwoDimensionalStep_zero : lazyTwoDimensionalStep 0 = (-1, 0) := by
  rfl
@[simp] theorem lazyTwoDimensionalStep_one : lazyTwoDimensionalStep 1 = (0, 1) := by
  rfl
@[simp] theorem lazyTwoDimensionalStep_two : lazyTwoDimensionalStep 2 = (1, -1) := by
  rfl

/-- Uniform source codes give exactly the uniform law on the three literal
source increments, not merely a distribution with the same first marginal. -/
theorem map_uniform_lazyTwoDimensionalStep :
    (Measure.uniformOfFinset (Finset.univ : Finset (Fin 3))).map lazyTwoDimensionalStep =
      Measure.uniformOfFinset ({(-1, 0), (0, 1), (1, -1)} : Finset (ℤ × ℤ)) := by
  have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  have hmeas : Measurable lazyTwoDimensionalStep := measurable_of_countable _
  have hmap (c : ℝ≥0∞) (z : Fin 3) :
      (c • Measure.dirac z).map lazyTwoDimensionalStep =
        c • Measure.dirac (lazyTwoDimensionalStep z) := by
    rw [Measure.map_smul c hmeas.aemeasurable, Measure.map_dirac]
  simp only [Measure.uniformOfFinset, hu]
  norm_num [Measure.map_add, hmeas, hmap, lazyTwoDimensionalStep]

/-- The genuine finite two-dimensional path integrating a source step word
from its specified integer start, retaining every coordinate. -/
@[expose] def lazyTwoDimensionalPrefix {n : ℕ} (x y : ℤ)
    (w : Fin n → Fin 3) (j : Fin (n + 1)) : ℤ × ℤ :=
  (x + ∑ i : Fin n with i.val < j.val, (lazyTwoDimensionalStep (w i)).1,
   y + ∑ i : Fin n with i.val < j.val, (lazyTwoDimensionalStep (w i)).2)

/-- Its actual first-coordinate path is the shifted original lazy word. -/
theorem lazyTwoDimensionalPrefix_fst {n : ℕ} (x y : ℤ)
    (w : Fin n → Fin 3) (j : Fin (n + 1)) :
    (lazyTwoDimensionalPrefix x y w j).1 = x + lazyWordValues w j := rfl

/-- The genuine two-dimensional prefix starts at the prescribed source point. -/
theorem lazyTwoDimensionalPrefix_zero {n : ℕ} (x y : ℤ) (w : Fin n → Fin 3) :
    lazyTwoDimensionalPrefix x y w 0 = (x, y) := by
  simp only [lazyTwoDimensionalPrefix, Fin.val_zero, not_lt_zero, Finset.filter_false,
    Finset.sum_empty, add_zero]

private theorem map_density_comp {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {ν : Measure α}
    {f : α → β} {g : β → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (ν.withDensity (fun x => g (f x))).map f = (ν.map f).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs),
    withDensity_apply _ hs, setLIntegral_map hs hg hf]

/-- A literal two-dimensional finite-prefix RN law projects to the exact
first-coordinate RN law. The right-hand side is the genuine uniform source
word law, with every intermediate nonnegative constraint retained. -/
theorem firstCoordinate_of_twoDimensional_prefix_RN (n x : ℕ) (y : ℤ)
    (ν : Measure (Fin (n + 1) → ℤ × ℤ))
    (hRN : ν =
      ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
        (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
        (fun q => if ∀ j, 0 ≤ (q j).1 then
          ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0)) :
    ν.map (fun q => fun j : Fin (n + 1) => (q j).1) =
      ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
        (fun w => fun j : Fin (n + 1) => (x : ℤ) + lazyWordValues w j)).withDensity
        (fun p => if ∀ j, 0 ≤ p j then
          ENNReal.ofReal (((p (Fin.last n) : ℝ) + 1) / ((x : ℝ) + 1)) else 0) := by
  let f : (Fin (n + 1) → ℤ × ℤ) → (Fin (n + 1) → ℤ) :=
    fun q j => (q j).1
  let d : (Fin (n + 1) → ℤ) → ℝ≥0∞ := fun p => if ∀ j, 0 ≤ p j then
    ENNReal.ofReal (((p (Fin.last n) : ℝ) + 1) / ((x : ℝ) + 1)) else 0
  have hf : Measurable f := measurable_of_countable _
  have hd : Measurable d := measurable_of_countable _
  let b : Measure (Fin (n + 1) → ℤ × ℤ) :=
    (Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
      (lazyTwoDimensionalPrefix (x : ℤ) y)
  have hb : ν = b.withDensity (fun q => d (f q)) := hRN
  change ν.map f = _
  rw [hb, map_density_comp hf hd]
  dsimp only [b]
  rw [Measure.map_map hf (measurable_of_countable _)]
  rfl

/-- Applying the source's genuine ALL-n two-dimensional RN characterization
produces the actual scalar prefix RN law for its first coordinate. The input
is precisely the defining source identity, not a scalar-law conclusion. -/
theorem firstCoordinate_of_twoDimensional_process_RN (x : ℕ) (y : ℤ)
    (ν : Measure (ℕ → ℤ × ℤ))
    (hRN : ∀ n : ℕ,
      ν.map (fun q => fun j : Fin (n + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0)) :
    ∀ n : ℕ,
      ν.map (fun q => fun j : Fin (n + 1) => (q j.val).1) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (fun w => fun j : Fin (n + 1) => (x : ℤ) + lazyWordValues w j)).withDensity
          (fun p => if ∀ j, 0 ≤ p j then
            ENNReal.ofReal (((p (Fin.last n) : ℝ) + 1) / ((x : ℝ) + 1)) else 0) := by
  intro n
  have h := firstCoordinate_of_twoDimensional_prefix_RN n x y
    (ν.map (fun q => fun j : Fin (n + 1) => q j.val)) (hRN n)
  rw [Measure.map_map (measurable_of_countable _) (by fun_prop)] at h
  exact h

end DirectedDistances.RandomWalk
