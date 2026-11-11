/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.LazyTwoDimensionalPrefix
public import Mathlib.Data.Fin.Tuple.Basic

/-! Supporting lemmas for paper labels `lem-renewal` (see CORRESPONDENCE.md). -/










public section
namespace DirectedDistances.RandomWalk
open scoped BigOperators

private theorem sum_append_before_left {n m : ℕ} (w : Fin n → Fin 3)
    (v : Fin m → Fin 3) (f : Fin 3 → ℤ) (j : Fin (n + 1)) :
    (∑ i : Fin (n + m) with i.val < j.val, f (Fin.append w v i)) =
      ∑ i : Fin n with i.val < j.val, f (w i) := by
  have htail : ∀ i : Fin m, ¬ n + i.val < j.val := by
    intro i
    omega
  simp only [Finset.sum_filter, Fin.sum_univ_add, Fin.val_castAdd, Fin.val_natAdd,
    Fin.append_left, Fin.append_right, htail, ite_false, Finset.sum_const_zero, add_zero]

private theorem sum_append_before_right {n m : ℕ} (w : Fin n → Fin 3)
    (v : Fin m → Fin 3) (f : Fin 3 → ℤ) (j : Fin (m + 1)) :
    (∑ i : Fin (n + m) with i.val < n + j.val, f (Fin.append w v i)) =
      (∑ i : Fin n, f (w i)) + ∑ i : Fin m with i.val < j.val, f (v i) := by
  have hhead : ∀ i : Fin n, i.val < n + j.val := by
    intro i
    omega
  simp only [Finset.sum_filter, Fin.sum_univ_add, Fin.val_castAdd, Fin.val_natAdd,
    Fin.append_left, Fin.append_right, hhead, ite_true, Nat.add_lt_add_iff_left]

/-- Every coordinate of the first word is unchanged by appending a second
source step word, including the shared endpoint. -/
theorem lazyTwoDimensionalPrefix_append_left {n m : ℕ} (x y : ℤ)
    (w : Fin n → Fin 3) (v : Fin m → Fin 3) (j : Fin (n + 1)) :
    lazyTwoDimensionalPrefix x y (Fin.append w v) ⟨j.val, by omega⟩ =
      lazyTwoDimensionalPrefix x y w j := by
  simp only [lazyTwoDimensionalPrefix]
  rw [sum_append_before_left w v (fun c => (lazyTwoDimensionalStep c).1) j,
    sum_append_before_left w v (fun c => (lazyTwoDimensionalStep c).2) j]

/-- The future coordinates of a concatenated source word integrate the
second word from the actual two-dimensional endpoint of the first word. -/
theorem lazyTwoDimensionalPrefix_append_right {n m : ℕ} (x y : ℤ)
    (w : Fin n → Fin 3) (v : Fin m → Fin 3) (j : Fin (m + 1)) :
    lazyTwoDimensionalPrefix x y (Fin.append w v) ⟨n + j.val, by omega⟩ =
      lazyTwoDimensionalPrefix
        (lazyTwoDimensionalPrefix x y w (Fin.last n)).1
        (lazyTwoDimensionalPrefix x y w (Fin.last n)).2 v j := by
  have hhead : ∀ i : Fin n, i.val < (Fin.last n).val := fun i => i.isLt
  simp only [lazyTwoDimensionalPrefix]
  rw [sum_append_before_right w v (fun c => (lazyTwoDimensionalStep c).1) j,
    sum_append_before_right w v (fun c => (lazyTwoDimensionalStep c).2) j]
  simp only [hhead, Finset.filter_true, add_assoc]

/-- The complete nonnegative first-coordinate barrier splits exactly at a
deterministic word boundary. The second barrier starts at the actual first
endpoint; no intermediate time or endpoint is dropped. -/
theorem lazyTwoDimensionalPrefix_append_nonnegative_iff {n m : ℕ} (x y : ℤ)
    (w : Fin n → Fin 3) (v : Fin m → Fin 3) :
    (∀ j : Fin (n + m + 1),
      0 ≤ (lazyTwoDimensionalPrefix x y (Fin.append w v) j).1) ↔
      (∀ j : Fin (n + 1), 0 ≤ (lazyTwoDimensionalPrefix x y w j).1) ∧
      (∀ j : Fin (m + 1), 0 ≤ (lazyTwoDimensionalPrefix
        (lazyTwoDimensionalPrefix x y w (Fin.last n)).1
        (lazyTwoDimensionalPrefix x y w (Fin.last n)).2 v j).1) := by
  constructor
  · intro h
    constructor
    · intro j
      simpa only [lazyTwoDimensionalPrefix_append_left] using
        h ⟨j.val, by omega⟩
    · intro j
      simpa only [lazyTwoDimensionalPrefix_append_right] using
        h ⟨n + j.val, by omega⟩
  · rintro ⟨hw, hv⟩ j
    by_cases hj : j.val ≤ n
    · have h := hw ⟨j.val, by omega⟩
      have he := lazyTwoDimensionalPrefix_append_left x y w v
        (⟨j.val, by omega⟩ : Fin (n + 1))
      simpa only [he] using h
    · have h := hv ⟨j.val - n, by omega⟩
      have he := lazyTwoDimensionalPrefix_append_right x y w v
        (⟨j.val - n, by omega⟩ : Fin (m + 1))
      have hj' : n + (j.val - n) = j.val := by omega
      simp only [hj'] at he
      exact he ▸ h

end DirectedDistances.RandomWalk
