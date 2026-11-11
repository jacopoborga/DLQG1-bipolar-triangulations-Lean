module

public import DirectedDistances.RandomWalk.SuccessSumAssembly
public import DirectedDistances.RandomWalk.RenewalCountGeometric
public import DirectedDistances.Probability.RenewalCountDichotomy
import DirectedDistances.RandomWalk.RenewalSuccessMeasurability

/-! # Infinitely many successes from the block bound

Helper for the probabilistic core of Proposition 4.3 (`prop-cut-vertex`),
geometric equivalence of Lemma 4.8 is not used here. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Almost surely infinitely many successes, from the renewal count identity -/
theorem conditionedSource_ae_infinite_success_of_blockProb
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
    ∀ᵐ p ∂ν, {n : ℕ | (∀ k, k < n + 1 → (p (n + 1)).2 ≤ (p k).2 - 1) ∧
      ∀ i, n + 1 ≤ i → (p (n + 1)).1 ≤ (p i).1}.Infinite :=
  DirectedDistances.Probability.ae_infinite_of_geometric_count ν
    (fun n => {p : ℕ → ℤ × ℤ | (∀ k, k < n + 1 → (p (n + 1)).2 ≤ (p k).2 - 1) ∧
      ∀ i, n + 1 ≤ i → (p (n + 1)).1 ≤ (p i).1})
    (fun n => measurableSet_renewal_success (n + 1))
    (fun m => conditionedSource_successCount_geometric ν hRN0 m)
    (conditionedSource_tsum_success_eq_top_of_blockProb ν hRN0 q hq hE)

/-- Specialization to the constructed law `conditionedVectorPathLaw 0 0`. -/
theorem conditionedVectorPathLaw_ae_infinite_success_of_blockProb
    (q : ℝ) (hq : 0 < q)
    (hE : ∀ N : ℕ, 100 ≤ N → q ≤ (conditionedVectorPathLaw 0 0).real {p : ℕ → ℤ × ℤ |
      (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
        Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
      (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
      ((p N).2 : ℝ) ≤ -2 * Real.sqrt N}) :
    ∀ᵐ p ∂(conditionedVectorPathLaw 0 0), {n : ℕ | (∀ k, k < n + 1 → (p (n + 1)).2 ≤ (p k).2 - 1) ∧
      ∀ i, n + 1 ≤ i → (p (n + 1)).1 ≤ (p i).1}.Infinite :=
  conditionedSource_ae_infinite_success_of_blockProb _
    conditionedVectorPathLaw_zero_RN q hq hE

end DirectedDistances.RandomWalk
