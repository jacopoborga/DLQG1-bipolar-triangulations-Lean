/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.LazyTwoDimensionalPrefix
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! Supporting lemmas for paper labels `lem-boltzmann-ldp-lower` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology

@[expose] noncomputable def lazyPrefixLaw (n : ℕ) :
    Measure (Fin (n + 1) → ℤ × ℤ) :=
  (Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
    (lazyTwoDimensionalPrefix 0 0)

@[expose] def shiftedWindowL {n : ℕ} (q : Fin (n + 1) → ℤ × ℤ) : ℝ :=
  ((q (Fin.last n)).1 : ℝ)

@[expose] noncomputable def shiftedWindowWeight (ℓ : ℕ) {n : ℕ}
    (q : Fin (n + 1) → ℤ × ℤ) : ℝ≥0∞ :=
  if ∀ j, -(ℓ : ℤ) ≤ (q j).1 then
    ENNReal.ofReal (((ℓ : ℝ) + shiftedWindowL q + 1) / ((ℓ : ℝ) + 1))
  else 0

theorem lazyPrefix_secondMoment_zero :
    ∫ q, (shiftedWindowL q) ^ 2 ∂lazyPrefixLaw 0 = 0 := by
  rw [lazyPrefixLaw, integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  simp [shiftedWindowL, lazyTwoDimensionalPrefix]

end DirectedDistances.RandomWalk
