/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.RenewalSuccessShift
meta import Lean.Elab.Tactic.Omega

/-! Supporting lemmas for paper labels `lem-renewal` (see CORRESPONDENCE.md). -/

/-! # Extended positive-rank graphs after a finite path shift

Deterministic ingredients for the renewal consumers of Lemma 4.9, Proposition
4.3 (`eqn-renewal-geometric`) and Lemma 4.15 (`eqn-cut-increments`), pinned
The retained independent Claude4 proof proposal is integrated here, consuming
existing success/count shifts. No source renewal-time selector, geometric
identification, recurrence, or probability law is introduced. -/

public section
namespace DirectedDistances.RandomWalk
open scoped Classical

/-- Generic rank-graph shift from count additivity at a finite rank origin. -/
theorem isPositiveSuccessTime_add_iff_of_count_add (S T : ℕ → Prop) {m t r : ℕ}
    (hr : 0 < r) (hc : positiveSuccessCount S t = m)
    (hadd : ∀ k, positiveSuccessCount S (t + k) =
      positiveSuccessCount S t + positiveSuccessCount T k)
    (hsucc : ∀ k, 0 < k → (S (t + k) ↔ T k)) (s : ℕ∞) :
    IsPositiveSuccessTime S (m + r) ((t : ℕ∞) + s) ↔ IsPositiveSuccessTime T r s := by
  have hmr : 0 < m + r := by omega
  induction s using ENat.recTopCoe with
  | top =>
    change IsPositiveSuccessTime S (m + r) ⊤ ↔ IsPositiveSuccessTime T r ⊤
    rw [isPositiveSuccessTime_top_iff S hmr, isPositiveSuccessTime_top_iff T hr]
    constructor
    · intro h k
      have h' := h (t + k)
      rw [hadd k, hc] at h'
      omega
    · intro h n
      by_cases hn : t ≤ n
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
        rw [hadd k, hc]
        have := h k
        omega
      · have hle := positiveSuccessCount_mono S (Nat.le_of_not_le hn)
        omega
  | coe k =>
    rw [← ENat.natCast_add, isPositiveSuccessTime_natCast_iff S hmr,
      isPositiveSuccessTime_natCast_iff T hr]
    unfold PositiveSuccessRank
    rw [hadd k, hc]
    constructor
    · rintro ⟨-, hs, hcount⟩
      have hk : 0 < k := by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · rw [positiveSuccessCount_zero] at hcount; omega
        · exact hk
      exact ⟨hk, (hsucc k hk).mp hs, by omega⟩
    · rintro ⟨hk, hs, hcount⟩
      exact ⟨by omega, (hsucc k hk).mpr hs, by omega⟩

/-- A finite rank-`m` success time supplies the strict-record origin and prefix
count; at rank zero the graph forces `t = 0`, where both are vacuous. -/
theorem renewal_origin_of_isPositiveSuccessTime (p : ℕ → ℤ × ℤ) {m t : ℕ}
    (hmt : IsPositiveSuccessTime (fun j =>
      (∀ i, i < j → (p j).2 ≤ (p i).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m (t : ℕ∞)) :
    (∀ i, i < t → (p t).2 ≤ (p i).2 - 1) ∧
      positiveSuccessCount (fun j =>
        (∀ i, i < j → (p j).2 ≤ (p i).2 - 1) ∧
          ∀ i, j ≤ i → (p j).1 ≤ (p i).1) t = m := by
  by_cases hm : m = 0
  · subst m
    have ht : t = 0 := ENat.natCast_inj.mp ((isPositiveSuccessTime_zero_iff _ _).mp hmt)
    subst t
    exact ⟨fun i hi => absurd hi (Nat.not_lt_zero i), positiveSuccessCount_zero _⟩
  · have hrank := (isPositiveSuccessTime_natCast_iff _ (Nat.pos_of_ne_zero hm) t).mp hmt
    exact ⟨hrank.2.1.1, hrank.2.2⟩




theorem isPositiveSuccessTime_renewal_add_pathShift_iff (p : ℕ → ℤ × ℤ) {m t r : ℕ}
    (hr : 0 < r)
    (hmt : IsPositiveSuccessTime (fun j =>
      (∀ i, i < j → (p j).2 ≤ (p i).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m (t : ℕ∞)) (s : ℕ∞) :
    IsPositiveSuccessTime (fun j =>
      (∀ i, i < j → (p j).2 ≤ (p i).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) (m + r) ((t : ℕ∞) + s) ↔
    IsPositiveSuccessTime (fun j =>
      (∀ i, i < j → ((fun a => p (t + a) - p t) j).2 ≤
        ((fun a => p (t + a) - p t) i).2 - 1) ∧
        ∀ i, j ≤ i → ((fun a => p (t + a) - p t) j).1 ≤
          ((fun a => p (t + a) - p t) i).1) r s := by
  obtain ⟨ht, hc⟩ := renewal_origin_of_isPositiveSuccessTime p hmt
  exact isPositiveSuccessTime_add_iff_of_count_add _ _ hr hc
    (fun k => positiveSuccessCount_renewal_add_pathShift p t k ht)
    (fun k hk => renewal_success_add_iff_pathShift p t k ht hk) s

end DirectedDistances.RandomWalk
