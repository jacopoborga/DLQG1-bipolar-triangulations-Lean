/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.RenewalTimeCharacterization
public import DirectedDistances.RandomWalk.ConditionedFutureLaw

/-! Supporting lemmas for paper labels `lem-renewal` (see CORRESPONDENCE.md). -/

/-! # Connecting the generic finite-rank graph to the source history slice

Internal event identities for Lemma 4.9 (`lem-renewal`), pinned unmodified
is consumed, rather than reproved. No source renewal-time selector, conditional
law, recurrence, or geometric equivalence from Lemma 4.8 is introduced here. -/

public section
namespace DirectedDistances.RandomWalk
open scoped Classical

/-- At positive endpoints, the generic rank for the literal source success
predicate equals the truncated rank and simultaneous future barrier. -/
theorem positiveSuccessRank_renewal_iff (p : ℕ → ℤ × ℤ) (m n : ℕ) (hn : 0 < n) :
    PositiveSuccessRank (fun j =>
      (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m n ↔
    ((∀ k, k < n → (p n).2 ≤ (p k).2 - 1) ∧
      (((Finset.Icc 1 n).filter fun j =>
        (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
          ∀ i, j ≤ i → i ≤ n → (p j).1 ≤ (p i).1).card = m)) ∧
      (∀ k, (p n).1 ≤ (p (n + k)).1) := by
  rw [PositiveSuccessRank, positiveSuccessCount_eq_card]
  have hfactor := renewal_success_rank_factorization
    (fun j => (p j).1) (fun j => (p j).2) m n
  have hbar : (∀ i, n ≤ i → (p n).1 ≤ (p i).1) ↔
      ∀ k, (p n).1 ≤ (p (n + k)).1 := by
    constructor
    · intro h k
      exact h (n + k) (Nat.le_add_right n k)
    · intro h i hi
      simpa only [Nat.add_sub_of_le hi] using h (i - n)
  constructor
  · rintro ⟨_, ⟨ha, hb⟩, hc⟩
    obtain ⟨ha', hc', hb'⟩ := hfactor.mp ⟨ha, by
      convert hc using 1; congr 2, hb⟩
    exact ⟨⟨ha', hc'⟩, hbar.mp hb'⟩
  · rintro ⟨⟨ha, hc⟩, hb⟩
    obtain ⟨ha', hc', hb'⟩ := hfactor.mpr ⟨ha, hc, hbar.mpr hb⟩
    exact ⟨hn, ⟨ha', hb'⟩, by convert hc' using 1; congr 2⟩

/-- Positive ranks cannot have finite graph value zero, including for the
literal source success predicate; rank zero is a separate prescribed case. -/
theorem not_isPositiveSuccessTime_zero (S : ℕ → Prop) {m : ℕ} (hm : 0 < m) :
    ¬ IsPositiveSuccessTime S m (0 : ℕ∞) := by
  change ¬ IsPositiveSuccessTime S m ((0 : ℕ) : ℕ∞)
  rw [isPositiveSuccessTime_natCast_iff S hm 0]
  exact fun h => Nat.not_lt_zero 0 h.1




theorem isPositiveSuccessTime_renewal_natCast_iff (p : ℕ → ℤ × ℤ)
    {m : ℕ} (hm : 0 < m) (n : ℕ) :
    IsPositiveSuccessTime (fun j =>
      (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m (n : ℕ∞) ↔
    ((∀ k, k < n → (p n).2 ≤ (p k).2 - 1) ∧
      (((Finset.Icc 1 n).filter fun j =>
        (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
          ∀ i, j ≤ i → i ≤ n → (p j).1 ≤ (p i).1).card = m)) ∧
      (∀ k, (p n).1 ≤ (p (n + k)).1) := by
  by_cases hn : 0 < n
  · exact (isPositiveSuccessTime_natCast_iff _ hm n).trans
      (positiveSuccessRank_renewal_iff p m n hn)
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    constructor
    · intro h
      exact False.elim (not_isPositiveSuccessTime_zero _ hm h)
    · rintro ⟨⟨_, hc⟩, _⟩
      have hempty : Finset.Icc (1 : ℕ) 0 = ∅ := Finset.Icc_eq_empty_of_lt (by decide)
      rw [hempty, Finset.filter_empty, Finset.card_empty] at hc
      exact False.elim (Nat.ne_of_gt hm hc.symm)

/-- Set form of the finite graph identity, ready for restriction and the
already proved deterministic history-tested regeneration law. -/
theorem setOf_isPositiveSuccessTime_renewal_natCast {m : ℕ} (hm : 0 < m) (n : ℕ) :
    {p : ℕ → ℤ × ℤ | IsPositiveSuccessTime (fun j =>
      (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m (n : ℕ∞)} =
    {p | (∀ k, k < n → (p n).2 ≤ (p k).2 - 1) ∧
      (((Finset.Icc 1 n).filter fun j =>
        (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
          ∀ i, j ≤ i → i ≤ n → (p j).1 ≤ (p i).1).card = m)} ∩
      {p | ∀ k, (p n).1 ≤ (p (n + k)).1} := by
  ext p
  exact isPositiveSuccessTime_renewal_natCast_iff p hm n

end DirectedDistances.RandomWalk
