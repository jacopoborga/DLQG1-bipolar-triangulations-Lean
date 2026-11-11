/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Finset.Card

/-! # Counting strict records of an integer path

Internal deterministic ingredients for the proof of Lemma 4.12
downward jumps have size at most one must visit every intermediate integer
level at a strict record time. No probabilistic or functional-limit input is
assumed, and no numbered paper result is asserted here. -/

public section
namespace DirectedDistances.RandomWalk

/-- Every level below the entire early path and above the terminal value is
attained at a later strict record. This is the discrete first-passage step in
the record-count argument of Lemma 4.12. -/
theorem exists_strictRecord_eq_of_downStep_le_one
    (r : ℕ → ℤ) (m N : ℕ) (b k : ℤ) (hmN : m ≤ N)
    (hstep : ∀ i, i < N → r i - 1 ≤ r (i + 1))
    (hearly : ∀ i, i ≤ m → b ≤ r i)
    (hterminal : r N ≤ k) (hlevel : k < b) :
    ∃ n ∈ Finset.Icc (m + 1) N,
      r n = k ∧ ∀ j, j < n → r n ≤ r j - 1 := by
  classical
  have hex : ∃ n, n ≤ N ∧ r n ≤ k := ⟨N, le_rfl, hterminal⟩
  let n := Nat.find hex
  have hn : n ≤ N ∧ r n ≤ k := Nat.find_spec hex
  have hprev : ∀ j, j < n → k < r j := by
    intro j hj
    have hnot := Nat.find_min hex hj
    have hjN : j ≤ N := by omega
    omega
  have hmn : m < n := by
    by_contra h
    have hnm : n ≤ m := by omega
    have := hearly n hnm
    omega
  have hnpos : 0 < n := by omega
  have hpred : k < r (n - 1) := hprev (n - 1) (by omega)
  have hs := hstep (n - 1) (by omega)
  have hnsub : n - 1 + 1 = n := by omega
  rw [hnsub] at hs
  have hnk : r n = k := by omega
  refine ⟨n, Finset.mem_Icc.mpr ⟨by omega, hn.1⟩, hnk, ?_⟩
  intro j hj
  have := hprev j hj
  omega

/-- The number of late strict record times bounds the number of integer levels
between the early lower bound and the terminal value. The `toNat` retains the
empty-level case without an extra terminal-height assumption. This supplies
the deterministic counting ingredient in Lemma 4.12. -/
theorem sub_terminal_toNat_le_card_strictRecords
    (r : ℕ → ℤ) (m N : ℕ) (b : ℤ) (hmN : m ≤ N)
    (hstep : ∀ i, i < N → r i - 1 ≤ r (i + 1))
    (hearly : ∀ i, i ≤ m → b ≤ r i) :
    (b - r N).toNat ≤
      ((Finset.Icc (m + 1) N).filter fun n =>
        ∀ j, j < n → r n ≤ r j - 1).card := by
  classical
  let levels := Finset.Icc (r N) (b - 1)
  let records := (Finset.Icc (m + 1) N).filter fun n =>
    ∀ j, j < n → r n ≤ r j - 1
  have hex : ∀ k ∈ levels, ∃ n ∈ records, r n = k := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    obtain ⟨n, hn, hnk, hrec⟩ := exists_strictRecord_eq_of_downStep_le_one
      r m N b k hmN hstep hearly hk'.1 (by omega)
    exact ⟨n, Finset.mem_filter.mpr ⟨hn, hrec⟩, hnk⟩
  choose f hfmem hfeq using hex
  let g : ℤ → ℕ := fun k => if hk : k ∈ levels then f k hk else 0
  have hgmem : ∀ k ∈ levels, g k ∈ records := by
    intro k hk
    simpa only [g, dif_pos hk] using hfmem k hk
  have hgeq : ∀ k ∈ levels, r (g k) = k := by
    intro k hk
    simpa only [g, dif_pos hk] using hfeq k hk
  have hinj : Set.InjOn g (levels : Set ℤ) := by
    intro k hk l hl hkl
    calc k = r (g k) := (hgeq k hk).symm
         _ = r (g l) := congrArg r hkl
         _ = l := hgeq l hl
  have hc := Finset.card_le_card_of_injOn g hgmem hinj
  have hlevels : levels.card = (b - r N).toNat := by
    simp only [levels, Int.card_Icc]
    congr 1
    omega
  rw [hlevels] at hc
  exact hc

end DirectedDistances.RandomWalk
