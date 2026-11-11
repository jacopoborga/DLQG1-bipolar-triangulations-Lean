module

public import DirectedDistances.Probability.WeightedHalfBlockMass
public import DirectedDistances.RandomWalk.RecordBlockCount
public import DirectedDistances.RandomWalk.RegularRecordBarrier
public import DirectedDistances.RandomWalk.ConditionedVectorTrajectory

/-! # Divergence of the record-barrier masses from the block bound

Helper assembly for Lemma 4.12 (`lem-walk-bdy-sum`), -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Lemma 4.12 conclusion from the block bound as the only probabilistic input -/
theorem conditionedSource_tsum_recordBarrier_eq_top_of_blockProb
    (ν : Measure (ℕ → ℤ × ℤ)) [IsProbabilityMeasure ν]
    (hRN0 : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0))
    (q : ℝ) (hq : 0 < q)
    (hE : ∀ N : ℕ, 100 ≤ N → q ≤ ν.real {p : ℕ → ℤ × ℤ |
      (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
        Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
      (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
      ((p N).2 : ℝ) ≤ -2 * Real.sqrt N}) :
    ∑' n, ν ({p : ℕ → ℤ × ℤ | ∀ j < n + 1, (p (n + 1)).2 ≤ (p j).2 - 1} ∩
      {p : ℕ → ℤ × ℤ | ∀ j, (p (n + 1)).1 ≤ (p (n + 1 + j)).1}) = ∞ := by
  have hRN' : ∀ n : ℕ,
      ν.map (fun q => fun j : Fin (n + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix ((0 : ℕ) : ℤ) 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) /
              (((0 : ℕ) : ℝ) + 1)) else 0) := by
    simpa only [Nat.cast_zero] using hRN0
  have hstep := conditionedSource_ae_secondCoordinate_downStep 0 0 ν hRN'
  exact DirectedDistances.Probability.tsum_measure_inter_succ_eq_top_of_weighted_halfBlock ν
    (fun n => {p : ℕ → ℤ × ℤ | ∀ j < n, (p n).2 ≤ (p j).2 - 1})
    (fun n => {p : ℕ → ℤ × ℤ | ∀ j, (p n).1 ≤ (p (n + j)).1})
    (fun n => {p : ℕ → ℤ × ℤ | (∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
      Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n})
    q hq (fun n _ p hp => hp.1)
    (fun n hn => regularRecord_futureBarrier_joint_lower ν hRN0 n hn)
    (block_sum_lower_bound_of_block_prob ν hstep q hE)

/-- The same divergence for the success predicate. -/
theorem conditionedSource_tsum_success_eq_top_of_blockProb
    (ν : Measure (ℕ → ℤ × ℤ)) [IsProbabilityMeasure ν]
    (hRN0 : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0))
    (q : ℝ) (hq : 0 < q)
    (hE : ∀ N : ℕ, 100 ≤ N → q ≤ ν.real {p : ℕ → ℤ × ℤ |
      (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
        Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
      (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
      ((p N).2 : ℝ) ≤ -2 * Real.sqrt N}) :
    ∑' n, ν {p : ℕ → ℤ × ℤ | (∀ k, k < n + 1 → (p (n + 1)).2 ≤ (p k).2 - 1) ∧
      ∀ i, n + 1 ≤ i → (p (n + 1)).1 ≤ (p i).1} = ∞ := by
  have h := conditionedSource_tsum_recordBarrier_eq_top_of_blockProb ν hRN0 q hq hE
  rw [← h]
  refine tsum_congr fun n => congrArg ν ?_
  ext p
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  refine and_congr Iff.rfl ⟨fun h j => h (n + 1 + j) (by omega), fun h i hi => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  exact h j

/-- The `(0,0)` RN identity of the constructed law, in the form used by the -/
theorem conditionedVectorPathLaw_zero_RN (k : ℕ) :
    (conditionedVectorPathLaw 0 0).map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0) := by
  simpa only [Nat.cast_zero] using conditionedVectorPathLaw_map_prefix 0 0 k

/-- Specialization to the constructed law `conditionedVectorPathLaw 0 0`. -/
theorem conditionedVectorPathLaw_tsum_success_eq_top_of_blockProb
    (q : ℝ) (hq : 0 < q)
    (hE : ∀ N : ℕ, 100 ≤ N → q ≤ (conditionedVectorPathLaw 0 0).real {p : ℕ → ℤ × ℤ |
      (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
        Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
      (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
      ((p N).2 : ℝ) ≤ -2 * Real.sqrt N}) :
    ∑' n, conditionedVectorPathLaw 0 0 {p : ℕ → ℤ × ℤ |
      (∀ k, k < n + 1 → (p (n + 1)).2 ≤ (p k).2 - 1) ∧
      ∀ i, n + 1 ≤ i → (p (n + 1)).1 ≤ (p i).1} = ∞ :=
  conditionedSource_tsum_success_eq_top_of_blockProb _
    conditionedVectorPathLaw_zero_RN q hq hE

end DirectedDistances.RandomWalk
