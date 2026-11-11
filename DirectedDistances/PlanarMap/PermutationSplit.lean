/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PermutationSplice
public import Mathlib.GroupTheory.Perm.Cycle.Factors

/-! # Splitting permutation orbits by a transposition

Local successor equations for the right transposition used in the map -/

public section
namespace DirectedDistances.PlanarMap

open Equiv

universe u

variable {D : Type u} [DecidableEq D]

/-- Right multiplication by a transposition exchanges the successors of its
two points. -/
theorem rightSwap_apply_left (f : Equiv.Perm D) (a b : D) :
    (f * Equiv.swap a b) a = f b := by
  simp

/-- Right multiplication by a transposition exchanges the successors of its
two points. -/
theorem rightSwap_apply_right (f : Equiv.Perm D) (a b : D) :
    (f * Equiv.swap a b) b = f a := by
  simp

/-- Away from the two splice locations, right multiplication leaves the
successor table unchanged. -/
theorem rightSwap_apply_of_ne (f : Equiv.Perm D) {a b x : D}
    (hxa : x ≠ a) (hxb : x ≠ b) :
    (f * Equiv.swap a b) x = f x := by
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxb]

/-- The two new outgoing edges in a same-cycle split. -/
theorem rightSwap_sameCycle_crossings (f : Equiv.Perm D) (a b : D) :
    (f * Equiv.swap a b).SameCycle a (f b) ∧
      (f * Equiv.swap a b).SameCycle b (f a) := by
  constructor <;> exact ⟨1, by simp⟩

/-- If `b` occurs at power `k` from `a`, the first new cycle starts with
`a, f^(k+1) a`. -/
theorem rightSwap_apply_a_of_pow (f : Equiv.Perm D) (a b : D) (k : ℕ)
    (hb : (f ^ k) a = b) :
    (f * Equiv.swap a b) a = (f ^ (k + 1)) a := by
  rw [rightSwap_apply_left, ← hb]
  simp [pow_succ']

/-- If `b` occurs at power `k` from `a`, the second new cycle starts with
`b, f a`. -/
theorem rightSwap_apply_b (f : Equiv.Perm D) (a b : D) :
    (f * Equiv.swap a b) b = f a :=
  rightSwap_apply_right f a b

/-- At every other point, the old successor is retained. This is the local
transition rule for both split cycles away from their cut points. -/
theorem rightSwap_apply_pow_of_ne (f : Equiv.Perm D) (a b : D) (i : ℕ)
    (hia : (f ^ i) a ≠ a) (hib : (f ^ i) a ≠ b) :
    (f * Equiv.swap a b) ((f ^ i) a) = (f ^ (i + 1)) a := by
  rw [rightSwap_apply_of_ne f hia hib]
  simp only [pow_succ', Equiv.Perm.mul_apply]

/-- The shared cycle has a uniquely specified positive power index for its
second point, measured by the support size of its cycle permutation. -/
theorem sameCycle_split_index_unique [Fintype D] (f : Equiv.Perm D)
    {a b : D} (hab : a ≠ b) (h : f.SameCycle a b) :
    ∃! k : ℕ,
      1 ≤ k ∧ k < (f.cycleOf a).support.card ∧ (f ^ k) a = b := by
  classical
  have ha : a ∈ f.support := by
    rw [Equiv.Perm.mem_support]
    intro hfix
    exact hab (h.eq_of_left hfix)
  obtain ⟨k, hk, hpow⟩ := h.exists_pow_eq_of_mem_support ha
  have hkpos : 0 < k := by
    by_contra hnot
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hnot
    subst k
    exact hab (by simpa using hpow)
  have hca : a ∈ (f.cycleOf a).support := by
    rw [Equiv.Perm.mem_support_cycleOf_iff' (Equiv.Perm.mem_support.mp ha)]
  refine ⟨k, ⟨Nat.succ_le_of_lt hkpos, hk, hpow⟩, ?_⟩
  intro j hj
  have hjm : j < (f.cycleOf a).support.card := hj.2.1
  have hpowEq : (f ^ j) a = (f ^ k) a := hj.2.2.trans hpow.symm
  exact (f.isCycleOn_support_cycleOf a).injOn_pow_apply hca hjm hk hpowEq

/-- The support size of the cycle containing `a` is its return period. -/
theorem sameCycle_split_period [Fintype D] (f : Equiv.Perm D) (a : D) :
    (f ^ (f.cycleOf a).support.card) a = a := by
  classical
  by_cases hfix : f a = a
  · exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hfix _
  · exact (f.isCycleOn_support_cycleOf a).pow_card_apply (by
      rw [Equiv.Perm.mem_support_cycleOf_iff' hfix]
      )

/-- The old orbit's power indices divide into the two ranges that become the
two cycles after the successor swap. The first range is
`a, f^(k+1) a, ..., f^(m-1) a`; the second is
`f^k a, f a, ..., f^(k-1) a`. -/
theorem sameCycle_split_index_partition [Fintype D] (f : Equiv.Perm D)
    {a b x : D} (hab : a ≠ b) (k : ℕ)
    (_hk : 1 ≤ k) (_hkm : k < (f.cycleOf a).support.card)
    (hb : (f ^ k) a = b) (hx : f.SameCycle a x) :
    x = a ∨
      (∃ i, k + 1 ≤ i ∧ i < (f.cycleOf a).support.card ∧ (f ^ i) a = x) ∨
      (∃ i, 1 ≤ i ∧ i ≤ k ∧ (f ^ i) a = x) := by
  classical
  have ha : a ∈ f.support := by
    rw [Equiv.Perm.mem_support]
    intro hfix
    have hpowfix := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hfix k
    rw [hpowfix] at hb
    exact hab hb
  obtain ⟨i, hi, hix⟩ := hx.exists_pow_eq_of_mem_support ha
  by_cases hi0 : i = 0
  · left
    simpa [hi0] using hix.symm
  · by_cases hik : i ≤ k
    · right
      right
      refine ⟨i, ?_, hik, hix⟩
      omega
    · right
      left
      refine ⟨i, ?_, hi, hix⟩
      omega

end DirectedDistances.PlanarMap
