/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ConditionedFutureLaw
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Logic.Encodable.Pi

/-! # Finite-prefix measurability of the renewal rank condition

Internal ingredients for Lemma 4.9 (`lem-renewal`), original
the proof depend only on coordinates through `n`. Their conjunction is
measurable in that finite-prefix sigma algebra. The future barrier and the
conditional renewal law are not included in the finite-prefix predicate. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory
open scoped Classical

private theorem strict_record_congr (p q : ℕ → ℤ × ℤ) {j n : ℕ}
    (hjn : j ≤ n) (hpq : ∀ i, i ≤ n → p i = q i) :
    (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ↔
      ∀ k, k < j → (q j).2 ≤ (q k).2 - 1 := by
  constructor
  · intro h k hk
    simpa only [hpq j hjn, hpq k ((Nat.le_of_lt hk).trans hjn)] using h k hk
  · intro h k hk
    simpa only [hpq j hjn, hpq k ((Nat.le_of_lt hk).trans hjn)] using h k hk

private theorem truncated_barrier_congr (p q : ℕ → ℤ × ℤ) {j n : ℕ}
    (hjn : j ≤ n) (hpq : ∀ i, i ≤ n → p i = q i) :
    (∀ i, j ≤ i → i ≤ n → (p j).1 ≤ (p i).1) ↔
      ∀ i, j ≤ i → i ≤ n → (q j).1 ≤ (q i).1 := by
  constructor
  · intro h i hji hin
    simpa only [hpq j hjn, hpq i hin] using h i hji hin
  · intro h i hji hin
    simpa only [hpq j hjn, hpq i hin] using h i hji hin

/-- The literal conjunction of the first two conditions in the proof of
Lemma 4.9 is invariant under equality of the entire prefix through `n`. -/
theorem renewal_prefix_condition_congr (p q : ℕ → ℤ × ℤ) (m n : ℕ)
    (hpq : ∀ i, i ≤ n → p i = q i) :
    ((∀ k, k < n → (p n).2 ≤ (p k).2 - 1) ∧
      (((Finset.Icc 1 n).filter fun j =>
        (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
          ∀ i, j ≤ i → i ≤ n → (p j).1 ≤ (p i).1).card = m)) ↔
    ((∀ k, k < n → (q n).2 ≤ (q k).2 - 1) ∧
      (((Finset.Icc 1 n).filter fun j =>
        (∀ k, k < j → (q j).2 ≤ (q k).2 - 1) ∧
          ∀ i, j ≤ i → i ≤ n → (q j).1 ≤ (q i).1).card = m)) := by
  have he :
      ((Finset.Icc 1 n).filter fun j =>
        (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
          ∀ i, j ≤ i → i ≤ n → (p j).1 ≤ (p i).1) =
      ((Finset.Icc 1 n).filter fun j =>
        (∀ k, k < j → (q j).2 ≤ (q k).2 - 1) ∧
          ∀ i, j ≤ i → i ≤ n → (q j).1 ≤ (q i).1) := by
    apply Finset.filter_congr
    intro j hj
    exact and_congr (strict_record_congr p q (Finset.mem_Icc.mp hj).2 hpq)
      (truncated_barrier_congr p q (Finset.mem_Icc.mp hj).2 hpq)
  exact and_congr (strict_record_congr p q le_rfl hpq) (by rw [he])

/-- The finite-prefix rank condition belongs to the sigma algebra pulled
back from the actual coordinates `0,…,n`, as required in Lemma 4.9's proof. -/
theorem measurableSet_renewal_prefix_condition_comap (m n : ℕ) :
    MeasurableSet[MeasurableSpace.comap
      ((Finset.Iic n).restrict : (ℕ → ℤ × ℤ) → ((i : Finset.Iic n) → ℤ × ℤ))
      inferInstance]
      {p : ℕ → ℤ × ℤ |
        (∀ k, k < n → (p n).2 ≤ (p k).2 - 1) ∧
          (((Finset.Icc 1 n).filter fun j =>
            (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
              ∀ i, j ≤ i → i ≤ n → (p j).1 ≤ (p i).1).card = m)} := by
  let E : Set (ℕ → ℤ × ℤ) :=
    {p | (∀ k, k < n → (p n).2 ≤ (p k).2 - 1) ∧
      (((Finset.Icc 1 n).filter fun j =>
        (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
          ∀ i, j ≤ i → i ≤ n → (p j).1 ≤ (p i).1).card = m)}
  let F := (Finset.Iic n).restrict '' E
  apply MeasurableSpace.measurableSet_comap.mpr
  refine ⟨F, (Set.to_countable F).measurableSet, ?_⟩
  ext p
  constructor
  · rintro ⟨q, hq, hpq⟩
    have hprefix : ∀ i, i ≤ n → q i = p i := by
      intro i hi
      exact congrFun hpq ⟨i, Finset.mem_Iic.mpr hi⟩
    exact (renewal_prefix_condition_congr q p m n hprefix).mp hq
  · intro hp
    exact ⟨p, hp, rfl⟩

/-- In particular, the literal finite-prefix rank event is measurable on
the actual full integer-vector path space. -/
theorem measurableSet_renewal_prefix_condition (m n : ℕ) :
    MeasurableSet {p : ℕ → ℤ × ℤ |
      (∀ k, k < n → (p n).2 ≤ (p k).2 - 1) ∧
        (((Finset.Icc 1 n).filter fun j =>
          (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
            ∀ i, j ≤ i → i ≤ n → (p j).1 ≤ (p i).1).card = m)} := by
  obtain ⟨F, hF, hpre⟩ := MeasurableSpace.measurableSet_comap.mp
    (measurableSet_renewal_prefix_condition_comap m n)
  rw [← hpre]
  exact hF.preimage (Finset.measurable_restrict _)

end DirectedDistances.RandomWalk
