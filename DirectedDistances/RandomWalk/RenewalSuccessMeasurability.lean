/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.RenewalTimeCharacterization
public import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-! # Measurability of the literal positive renewal success sections

Internal measurable-event producers for Lemma 4.9 (`lem-renewal`), unchanged
strict record condition, and the left coordinate has its simultaneous
all-time barrier. This module defines no paper renewal time, assumes no
recurrence, and does not supply the geometric equivalence of Lemma 4.8. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory
open scoped Classical

/-- The strict right-coordinate record event of the source is measurable
in the full integer-vector path product sigma algebra. -/
theorem measurableSet_renewal_strict_record (n : ℕ) :
    MeasurableSet {p : ℕ → ℤ × ℤ |
      ∀ k, k < n → (p n).2 ≤ (p k).2 - 1} := by
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  apply (MeasurableSet.const (k < n)).imp
  exact (Set.to_countable {q : (ℤ × ℤ) × (ℤ × ℤ) |
    q.1.2 ≤ q.2.2 - 1}).measurableSet.preimage
      ((measurable_pi_apply (X := fun _ : ℕ => ℤ × ℤ) n).prodMk (measurable_pi_apply (X := fun _ : ℕ => ℤ × ℤ) k))

/-- The simultaneous all-time left-coordinate barrier is measurable. -/
theorem measurableSet_renewal_future_barrier (n : ℕ) :
    MeasurableSet {p : ℕ → ℤ × ℤ |
      ∀ k, (p n).1 ≤ (p (n + k)).1} := by
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  exact (Set.to_countable {q : (ℤ × ℤ) × (ℤ × ℤ) |
    q.1.1 ≤ q.2.1}).measurableSet.preimage
      ((measurable_pi_apply (X := fun _ : ℕ => ℤ × ℤ) n).prodMk (measurable_pi_apply (X := fun _ : ℕ => ℤ × ℤ) (n + k)))

/-- The positive successful-time section uses only positive indices and
retains the source's strict record and entire future barrier. -/
theorem measurableSet_positive_renewal_success (n : ℕ) :
    MeasurableSet {p : ℕ → ℤ × ℤ |
      0 < n ∧ (∀ k, k < n → (p n).2 ≤ (p k).2 - 1) ∧
        ∀ k, (p n).1 ≤ (p (n + k)).1} := by
  exact (MeasurableSet.const (0 < n)).inter
    ((measurableSet_renewal_strict_record n).inter
      (measurableSet_renewal_future_barrier n))

/-- The literal `A_n ∩ B_n` section with the source's absolute future
indices is measurable; no finite-horizon barrier replaces it. -/
theorem measurableSet_renewal_success (n : ℕ) :
    MeasurableSet {p : ℕ → ℤ × ℤ |
      (∀ k, k < n → (p n).2 ≤ (p k).2 - 1) ∧
        ∀ i, n ≤ i → (p n).1 ≤ (p i).1} := by
  change MeasurableSet ({p : ℕ → ℤ × ℤ |
    ∀ k, k < n → (p n).2 ≤ (p k).2 - 1} ∩
      {p | ∀ i, n ≤ i → (p n).1 ≤ (p i).1})
  apply (measurableSet_renewal_strict_record n).inter
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply (MeasurableSet.const (n ≤ i)).imp
  exact (Set.to_countable {q : (ℤ × ℤ) × (ℤ × ℤ) |
    q.1.1 ≤ q.2.1}).measurableSet.preimage
      ((measurable_pi_apply (X := fun _ : ℕ => ℤ × ℤ) n).prodMk (measurable_pi_apply (X := fun _ : ℕ => ℤ × ℤ) i))

/-- The generic finite positive-rank event is measurable for the actual
source success predicate. The count measurability is consumed from the
proved generic order-statistic infrastructure. -/
theorem measurableSet_renewal_positiveSuccessRank (m n : ℕ) :
    MeasurableSet {p : ℕ → ℤ × ℤ |
      PositiveSuccessRank (fun j =>
        (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
          ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m n} := by
  exact measurableSet_positiveSuccessRank _
    (fun j _ => measurableSet_renewal_success j) m n

/-- The finite global-success rank slice is measurable with the count on
`[1,n]`, retaining strict records and all-time barriers at every success. -/
theorem measurableSet_renewal_positive_global_rank_slice (m n : ℕ) :
    MeasurableSet {p : ℕ → ℤ × ℤ |
      0 < n ∧
        (∀ k, k < n → (p n).2 ≤ (p k).2 - 1) ∧
        (((Finset.Icc 1 n).filter fun j =>
          (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
            ∀ i, j ≤ i → (p j).1 ≤ (p i).1).card = m) ∧
        (∀ i, n ≤ i → (p n).1 ≤ (p i).1)} := by
  have h := measurableSet_renewal_positiveSuccessRank m n
  simp only [PositiveSuccessRank, positiveSuccessCount_eq_card] at h
  convert h using 1
  ext p
  constructor
  · rintro ⟨hn, hrecord, hcount, hbar⟩
    refine ⟨hn, ⟨hrecord, hbar⟩, ?_⟩
    convert hcount using 1; congr 2
  · rintro ⟨hn, ⟨hrecord, hbar⟩, hcount⟩
    refine ⟨hn, hrecord, ?_, hbar⟩
    convert hcount using 1; congr 2

/-- Distinct endpoints of one positive success rank are disjoint; this is
an application of generic rank uniqueness, without a finiteness assumption. -/
theorem pairwise_disjoint_renewal_positiveSuccessRank (m : ℕ) :
    Pairwise (fun n k => Disjoint
      {p : ℕ → ℤ × ℤ | PositiveSuccessRank (fun j =>
        (∀ i, i < j → (p j).2 ≤ (p i).2 - 1) ∧
          ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m n}
      {p : ℕ → ℤ × ℤ | PositiveSuccessRank (fun j =>
        (∀ i, i < j → (p j).2 ≤ (p i).2 - 1) ∧
          ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m k}) := by
  intro n k hne
  apply Set.disjoint_left.mpr
  intro p hn hk
  exact hne (positiveSuccessRank_unique
    (fun j => (∀ i, i < j → (p j).2 ≤ (p i).2 - 1) ∧
      ∀ i, j ≤ i → (p j).1 ≤ (p i).1) hn hk)

end DirectedDistances.RandomWalk
