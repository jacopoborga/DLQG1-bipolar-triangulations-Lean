/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.LazyTwoDimensionalPrefix







public section
namespace DirectedDistances.RandomWalk

theorem lazyTwoDimensionalStep_injective : Function.Injective lazyTwoDimensionalStep := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all

theorem lazyTwoDimensionalStep_fst_injective :
    Function.Injective (fun c => (lazyTwoDimensionalStep c).1) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all

private theorem sum_filter_lt_succ {n : ℕ} (f : Fin n → ℤ) (i : Fin n) :
    ∑ k : Fin n with k.val < i.val + 1, f k =
      ∑ k : Fin n with k.val < i.val, f k + f i := by
  have : (Finset.univ.filter fun k : Fin n => k.val < i.val + 1) =
      insert i (Finset.univ.filter fun k : Fin n => k.val < i.val) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff]
    omega
  rw [this, Finset.sum_insert (by simp), add_comm]

theorem lazyTwoDimensionalPrefix_succ {n : ℕ} (x y : ℤ) (w : Fin n → Fin 3) (i : Fin n) :
    lazyTwoDimensionalPrefix x y w i.succ =
      lazyTwoDimensionalPrefix x y w i.castSucc + lazyTwoDimensionalStep (w i) := by
  unfold lazyTwoDimensionalPrefix
  rw [Fin.val_succ, Fin.val_castSucc,
    sum_filter_lt_succ (fun k => (lazyTwoDimensionalStep (w k)).1) i,
    sum_filter_lt_succ (fun k => (lazyTwoDimensionalStep (w k)).2) i]
  ext <;> simp [add_assoc]

theorem mem_range_lazyTwoDimensionalPrefix_iff {n : ℕ} (x y : ℤ)
    (q : Fin (n + 1) → ℤ × ℤ) :
    q ∈ Set.range (@lazyTwoDimensionalPrefix n x y) ↔
      q 0 = (x, y) ∧ ∀ i : Fin n, ∃ c : Fin 3,
        q i.succ = q i.castSucc + lazyTwoDimensionalStep c := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨lazyTwoDimensionalPrefix_zero x y w,
      fun i => ⟨w i, lazyTwoDimensionalPrefix_succ x y w i⟩⟩
  · rintro ⟨h0, hs⟩
    choose c hc using hs
    refine ⟨c, ?_⟩
    funext j
    induction j using Fin.induction with
    | zero => rw [lazyTwoDimensionalPrefix_zero, h0]
    | succ i ih => rw [lazyTwoDimensionalPrefix_succ, ih, hc]

end DirectedDistances.RandomWalk
