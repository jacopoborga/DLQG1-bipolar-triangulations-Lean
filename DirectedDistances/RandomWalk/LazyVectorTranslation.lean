/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.LazyTwoDimensionalPrefix

/-! Supporting lemmas for paper labels `lem-renewal` (see CORRESPONDENCE.md). -/










public section
namespace DirectedDistances.RandomWalk
open MeasureTheory

/-- Subtracting the actual starting vector from an integrated source word
gives the same word integrated from zero, in both coordinates at every time. -/
theorem lazyTwoDimensionalPrefix_sub_start {n : ℕ} (x y : ℤ)
    (w : Fin n → Fin 3) (j : Fin (n + 1)) :
    lazyTwoDimensionalPrefix x y w j - (x, y) =
      lazyTwoDimensionalPrefix 0 0 w j := by
  apply Prod.ext <;> simp [lazyTwoDimensionalPrefix]

/-- Staying above the first starting coordinate is exactly the nonnegative
barrier for the translated zero-start word, including both endpoints. -/
theorem lazyTwoDimensionalPrefix_above_start_iff {n : ℕ} (x y : ℤ)
    (w : Fin n → Fin 3) :
    (∀ j : Fin (n + 1), x ≤ (lazyTwoDimensionalPrefix x y w j).1) ↔
      ∀ j : Fin (n + 1), 0 ≤ (lazyTwoDimensionalPrefix 0 0 w j).1 := by
  constructor <;> intro h j <;> have hj := h j <;>
    simp only [lazyTwoDimensionalPrefix_fst] at * <;> omega

/-- The actual unconditioned finite-prefix law translated by its full start
vector is the zero-start finite-prefix law. This is a pushforward identity
for genuine uniform source words, not a conditioned-law assumption. -/
theorem map_uniform_lazyTwoDimensionalPrefix_sub_start (n : ℕ) (x y : ℤ) :
    (((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
      (lazyTwoDimensionalPrefix x y)).map
      (fun q => fun j : Fin (n + 1) => q j - (x, y))) =
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
        (lazyTwoDimensionalPrefix 0 0) := by
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  congr 1
  funext w j
  exact lazyTwoDimensionalPrefix_sub_start x y w j

end DirectedDistances.RandomWalk
