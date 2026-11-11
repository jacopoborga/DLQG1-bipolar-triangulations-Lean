/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.RenewalTimeRankBridge
meta import Lean.Elab.Tactic.Omega

/-! # Deterministic success events after a finite path shift

Internal ingredients for the renewal argument, pinned unmodified
independent Claude4 account proof proposal from allocation 27371762. The
strict record and entire future barrier are literal; no renewal time selector,
geometric equivalence, recurrence, or probability-law premise is introduced. -/

public section
namespace DirectedDistances.RandomWalk
open scoped Classical

/-- Translation of the entire future left barrier uses no record premise. -/
theorem renewal_barrier_pathShift_iff (p : ℕ → ℤ × ℤ) (t k : ℕ) :
    (∀ i, k ≤ i → ((fun j => p (t + j) - p t) k).1 ≤
      ((fun j => p (t + j) - p t) i).1) ↔
      ∀ i, t + k ≤ i → (p (t + k)).1 ≤ (p i).1 := by
  constructor
  · intro h i hi
    have hti : t ≤ i := (Nat.le_add_right t k).trans hi
    have hk : k ≤ i - t := by omega
    have h' := h (i - t) hk
    change (p (t + k)).1 - (p t).1 ≤ (p (t + (i - t))).1 - (p t).1 at h'
    rw [Nat.add_sub_of_le hti] at h'
    omega
  · intro h i hi
    have h' := h (t + i) (Nat.add_le_add_left hi t)
    change (p (t + k)).1 - (p t).1 ≤ (p (t + i)).1 - (p t).1
    omega

/-- Restricting the past of a strict record to a later finite origin. -/
theorem renewal_record_pathShift_of_record_add (p : ℕ → ℤ × ℤ) (t k : ℕ)
    (h : ∀ i, i < t + k → (p (t + k)).2 ≤ (p i).2 - 1) :
    ∀ i, i < k → ((fun j => p (t + j) - p t) k).2 ≤
      ((fun j => p (t + j) - p t) i).2 - 1 := by
  intro i hi
  have h' := h (t + i) (Nat.add_lt_add_left hi t)
  change (p (t + k)).2 - (p t).2 ≤ (p (t + i)).2 - (p t).2 - 1
  omega

/-- A strict record at the origin controls the omitted earlier past;
the positive shift endpoint controls the origin itself. -/
theorem renewal_record_add_of_record_pathShift (p : ℕ → ℤ × ℤ) (t k : ℕ)
    (ht : ∀ i, i < t → (p t).2 ≤ (p i).2 - 1) (hk : 0 < k)
    (h : ∀ i, i < k → ((fun j => p (t + j) - p t) k).2 ≤
      ((fun j => p (t + j) - p t) i).2 - 1) :
    ∀ i, i < t + k → (p (t + k)).2 ≤ (p i).2 - 1 := by
  intro i hi
  by_cases hit : i < t
  · have hzero := h 0 hk
    change (p (t + k)).2 - (p t).2 ≤ (p (t + 0)).2 - (p t).2 - 1 at hzero
    rw [Nat.add_zero] at hzero
    have hpast := ht i hit
    omega
  · have hti : t ≤ i := Nat.le_of_not_gt hit
    have hisub : i - t < k := by omega
    have h' := h (i - t) hisub
    change (p (t + k)).2 - (p t).2 ≤ (p (t + (i - t))).2 - (p t).2 - 1 at h'
    rw [Nat.add_sub_of_le hti] at h'
    omega

/-- The literal success event after a strict record is exactly the
success event of the vector path shifted by the actual endpoint. -/
theorem renewal_success_add_iff_pathShift (p : ℕ → ℤ × ℤ) (t k : ℕ)
    (ht : ∀ i, i < t → (p t).2 ≤ (p i).2 - 1) (hk : 0 < k) :
    ((∀ i, i < t + k → (p (t + k)).2 ≤ (p i).2 - 1) ∧
      ∀ i, t + k ≤ i → (p (t + k)).1 ≤ (p i).1) ↔
    ((∀ i, i < k → ((fun j => p (t + j) - p t) k).2 ≤
      ((fun j => p (t + j) - p t) i).2 - 1) ∧
      ∀ i, k ≤ i → ((fun j => p (t + j) - p t) k).1 ≤
        ((fun j => p (t + j) - p t) i).1) := by
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨renewal_record_pathShift_of_record_add p t k ha,
      (renewal_barrier_pathShift_iff p t k).mpr hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨renewal_record_add_of_record_pathShift p t k ht hk ha,
      (renewal_barrier_pathShift_iff p t k).mp hb⟩

/-- At origin zero, success equivalence holds even at endpoint zero;
the strict record there is vacuous, while the barrier is retained. -/
theorem renewal_success_zero_iff_pathShift (p : ℕ → ℤ × ℤ) (k : ℕ) :
    ((∀ i, i < k → (p k).2 ≤ (p i).2 - 1) ∧
      ∀ i, k ≤ i → (p k).1 ≤ (p i).1) ↔
    ((∀ i, i < k → ((fun j => p j - p 0) k).2 ≤
      ((fun j => p j - p 0) i).2 - 1) ∧
      ∀ i, k ≤ i → ((fun j => p j - p 0) k).1 ≤
        ((fun j => p j - p 0) i).1) := by
  by_cases hk : 0 < k
  · simpa only [Nat.zero_add] using
      renewal_success_add_iff_pathShift p 0 k (fun i hi => False.elim (Nat.not_lt_zero i hi)) hk
  · have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    subst k
    have hbar := renewal_barrier_pathShift_iff p 0 0
    simp only [Nat.zero_add] at hbar
    simpa only [Nat.not_lt_zero, false_implies, implies_true, true_and] using hbar.symm

/-- Positive-success counts add after a strict-record origin. The origin's
own success is counted in the initial prefix and is not counted twice. -/
theorem positiveSuccessCount_renewal_add_pathShift (p : ℕ → ℤ × ℤ) (t k : ℕ)
    (ht : ∀ i, i < t → (p t).2 ≤ (p i).2 - 1) :
    positiveSuccessCount (fun j =>
      (∀ i, i < j → (p j).2 ≤ (p i).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) (t + k) =
    positiveSuccessCount (fun j =>
      (∀ i, i < j → (p j).2 ≤ (p i).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) t +
    positiveSuccessCount (fun j =>
      (∀ i, i < j → ((fun a => p (t + a) - p t) j).2 ≤
        ((fun a => p (t + a) - p t) i).2 - 1) ∧
        ∀ i, j ≤ i → ((fun a => p (t + a) - p t) j).1 ≤
          ((fun a => p (t + a) - p t) i).1) k := by
  induction k with
  | zero => rw [Nat.add_zero, positiveSuccessCount_zero, Nat.add_zero]
  | succ k ih =>
      rw [← Nat.add_assoc, positiveSuccessCount_succ, positiveSuccessCount_succ, ih]
      have heq := renewal_success_add_iff_pathShift p t (k + 1) ht (Nat.zero_lt_succ k)
      simp only [heq, Nat.add_assoc]
      split_ifs <;> omega

end DirectedDistances.RandomWalk
