/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.LazyTwoDimensionalPrefix








public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A density-weighted actual word law remains supported on the literal
two-dimensional word image. This applies in particular to the source RN
density, without requiring a probability or positivity hypothesis. -/
theorem lazyTwoDimensionalPrefix_withDensity_ae_mem_range
    (n : ℕ) (x y : ℤ) (d : (Fin (n + 1) → ℤ × ℤ) → ℝ≥0∞) :
    ∀ᵐ q ∂(((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
      (lazyTwoDimensionalPrefix x y)).withDensity d),
      q ∈ Set.range (@lazyTwoDimensionalPrefix n x y) := by
  have hrange : MeasurableSet (Set.range (@lazyTwoDimensionalPrefix n x y)) :=
    (Set.to_countable _).measurableSet
  have hbase := ae_map_mem_range hrange
    (measurable_of_countable (@lazyTwoDimensionalPrefix n x y)).aemeasurable
    (μ := Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3)))
  exact (withDensity_absolutelyContinuous _ d).ae_le hbase

/-- The complete source RN characterization produces support of the actual
full-vector prefix at every prescribed horizon. All source coordinates and
intermediate nonnegative constraints remain in the defining RN data. -/
theorem conditionedSource_ae_prefix_mem_range
    (x : ℕ) (y : ℤ) (ν : Measure (ℕ → ℤ × ℤ))
    (hRN : ∀ n : ℕ,
      ν.map (fun q => fun j : Fin (n + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0))
    (n : ℕ) :
    ∀ᵐ p ∂ν, (fun j : Fin (n + 1) => p j.val) ∈
      Set.range (@lazyTwoDimensionalPrefix n (x : ℤ) y) := by
  have h := lazyTwoDimensionalPrefix_withDensity_ae_mem_range n (x : ℤ) y
    (fun q => if ∀ j, 0 ≤ (q j).1 then
      ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0)
  rw [← hRN n] at h
  have hprefix : Measurable (fun p : ℕ → ℤ × ℤ =>
      fun j : Fin (n + 1) => p j.val) := by
    exact .of_eval (fun j => measurable_pi_apply j.val)
  exact ae_of_ae_map hprefix.aemeasurable h

/-- The actual source path simultaneously has a literal step-word
representation of every finite vector prefix. Countable intersection, rather
than a pointwise family of unrelated full-measure events, gives the conclusion. -/
theorem conditionedSource_ae_all_prefixes_mem_range
    (x : ℕ) (y : ℤ) (ν : Measure (ℕ → ℤ × ℤ))
    (hRN : ∀ n : ℕ,
      ν.map (fun q => fun j : Fin (n + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0)) :
    ∀ᵐ p ∂ν, ∀ n : ℕ, (fun j : Fin (n + 1) => p j.val) ∈
      Set.range (@lazyTwoDimensionalPrefix n (x : ℤ) y) := by
  exact ae_all_iff.mpr (conditionedSource_ae_prefix_mem_range x y ν hRN)

end DirectedDistances.RandomWalk
