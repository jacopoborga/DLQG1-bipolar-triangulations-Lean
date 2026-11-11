/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.RenewalRankSlice

/-! # Regeneration tested against the history on a renewal rank slice

Internal actual-law assembly for Lemma 4.9 (`lem-renewal`), unchanged
conditions are proved measurable internally. An arbitrary event in the
actual whole finite past tests the shifted future on their intersection
with the future lower barrier. No renewal time is defined here. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

/-- The actual source future law on a literal finite-rank slice, tested
against every event in its full finite history. Measurability of the rank
predicate is produced, while `hA` only specifies the arbitrary history test. -/
theorem conditionedSource_renewal_history_slice_restrict
    (ν : Measure (ℕ → ℤ × ℤ)) [IsProbabilityMeasure ν]
    (hRN : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0))
    (m n : ℕ) (A : Set (ℕ → ℤ × ℤ))
    (hA : MeasurableSet[MeasurableSpace.comap
      (fun p : ℕ → ℤ × ℤ => fun j : Fin (n + 1) => p j.val) inferInstance] A) :
    let P : Set (ℕ → ℤ × ℤ) :=
      {p | (∀ k, k < n → (p n).2 ≤ (p k).2 - 1) ∧
        (((Finset.Icc 1 n).filter fun j =>
          (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
            ∀ i, j ≤ i → i ≤ n → (p j).1 ≤ (p i).1).card = m)}
    let B : Set (ℕ → ℤ × ℤ) := {p | ∀ k, (p n).1 ≤ (p (n + k)).1}
    (ν.restrict (A ∩ (P ∩ B))).map (fun p => fun k => p (n + k) - p n) =
      ν (A ∩ (P ∩ B)) • ν := by
  have h := conditionedSource_past_restrict_regeneration ν hRN n _
    (hA.inter (measurableSet_renewal_prefix_condition_fin_comap m n))
  simpa only [Set.inter_assoc] using h

end DirectedDistances.RandomWalk
