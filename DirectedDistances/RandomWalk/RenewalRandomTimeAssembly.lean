/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.RenewalHistorySlice













public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

/-- The countable sum of the actual history-tested positive-time rank-slice
future laws. This supplies the law calculation for finite-time assembly,
without asserting existence or finiteness of any renewal time. -/
theorem conditionedSource_renewal_history_sum
    (ν : Measure (ℕ → ℤ × ℤ)) [IsProbabilityMeasure ν]
    (hRN : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0))
    (m : ℕ) (A : ℕ → Set (ℕ → ℤ × ℤ))
    (hA : ∀ n, MeasurableSet[MeasurableSpace.comap
      (fun p : ℕ → ℤ × ℤ => fun j : Fin (n + 2) => p j.val)
      inferInstance] (A n)) :
    let E : ℕ → Set (ℕ → ℤ × ℤ) := fun n =>
      A n ∩ ({p | (∀ k, k < n + 1 → (p (n + 1)).2 ≤ (p k).2 - 1) ∧
        (((Finset.Icc 1 (n + 1)).filter fun j =>
          (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
            ∀ i, j ≤ i → i ≤ n + 1 → (p j).1 ≤ (p i).1).card = m)} ∩
        {p | ∀ k, (p (n + 1)).1 ≤ (p (n + 1 + k)).1})
    Measure.sum (fun n => (ν.restrict (E n)).map
        (fun p => fun k => p (n + 1 + k) - p (n + 1))) =
      (∑' n, ν (E n)) • ν := by
  intro E
  have hpiece (n : ℕ) :
      (ν.restrict (E n)).map
          (fun p => fun k => p (n + 1 + k) - p (n + 1)) =
        ν (E n) • ν :=
    conditionedSource_renewal_history_slice_restrict ν hRN m (n + 1) (A n) (hA n)
  apply Measure.ext
  intro t ht
  rw [Measure.sum_apply _ ht]
  simp_rw [hpiece, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.tsum_mul_right

end DirectedDistances.RandomWalk
