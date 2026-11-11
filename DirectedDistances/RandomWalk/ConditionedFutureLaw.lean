/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Interval.Finset.Nat

/-! # Deterministic barrier and success-rank factorization

Internal ingredients for Lemma 4.9 (`lem-renewal`), original
an earlier future barrier is equivalent to its finite-window restriction.
Consequently the rank event at `n` factors into the source's finite-prefix
condition and its future barrier. No random time or probability law is
defined here; the conditional renewal law remains a separate obligation. -/

public section
namespace DirectedDistances.RandomWalk
open scoped Classical

/-- Under the future lower barrier at `n`, a barrier starting at `j ≤ n`
is equivalent to its restriction to `[j,n]`. This includes `j = n`. -/
theorem future_barrier_iff_prefix_barrier {α : Type*} [Preorder α]
    (L : ℕ → α) {j n : ℕ} (hjn : j ≤ n)
    (hn : ∀ i, n ≤ i → L n ≤ L i) :
    (∀ i, j ≤ i → L j ≤ L i) ↔
      ∀ i, j ≤ i → i ≤ n → L j ≤ L i := by
  constructor
  · intro h i hji _
    exact h i hji
  · intro h i hji
    by_cases hin : i ≤ n
    · exact h i hji hin
    · exact (h n hjn le_rfl).trans (hn i (le_of_not_ge hin))

/-- The source's global-success and finite-window-success sets in `[1,n]`
are literally equal on the future barrier at `n`. The predicate `A` may be
the source's strict right-coordinate record event. -/
theorem future_barrier_success_filter_eq {α : Type*} [Preorder α]
    (L : ℕ → α) (A : ℕ → Prop) (n : ℕ)
    (hn : ∀ i, n ≤ i → L n ≤ L i) :
    ((Finset.Icc 1 n).filter fun j => A j ∧ ∀ i, j ≤ i → L j ≤ L i) =
      ((Finset.Icc 1 n).filter fun j =>
        A j ∧ ∀ i, j ≤ i → i ≤ n → L j ≤ L i) := by
  classical
  apply Finset.filter_congr
  intro j hj
  rw [future_barrier_iff_prefix_barrier L (Finset.mem_Icc.mp hj).2 hn]

/-- The literal finite-rank factorization used in the proof of Lemma 4.9.
The right-coordinate event retains the source's strict `R j ≤ R k - 1`;
successes are counted only at positive times. This is a deterministic rank
identity, including empty intervals, and makes no assertion about `T₀`. -/
theorem renewal_success_rank_factorization (L R : ℕ → ℤ) (m n : ℕ) :
    ((∀ k, k < n → R n ≤ R k - 1) ∧
      (((Finset.Icc 1 n).filter fun j =>
        (∀ k, k < j → R j ≤ R k - 1) ∧
          ∀ i, j ≤ i → L j ≤ L i).card = m) ∧
      (∀ i, n ≤ i → L n ≤ L i)) ↔
    ((∀ k, k < n → R n ≤ R k - 1) ∧
      (((Finset.Icc 1 n).filter fun j =>
        (∀ k, k < j → R j ≤ R k - 1) ∧
          ∀ i, j ≤ i → i ≤ n → L j ≤ L i).card = m) ∧
      (∀ i, n ≤ i → L n ≤ L i)) := by
  classical
  constructor
  · rintro ⟨hA, hcard, hB⟩
    refine ⟨hA, ?_, hB⟩
    convert hcard using 1
    congr 1
    apply Finset.filter_congr
    intro j hj
    exact and_congr_right fun _ =>
      (future_barrier_iff_prefix_barrier L (Finset.mem_Icc.mp hj).2 hB).symm
  · rintro ⟨hA, hcard, hB⟩
    refine ⟨hA, ?_, hB⟩
    convert hcard using 1
    congr 1
    apply Finset.filter_congr
    intro j hj
    exact and_congr_right fun _ =>
      future_barrier_iff_prefix_barrier L (Finset.mem_Icc.mp hj).2 hB

end DirectedDistances.RandomWalk
