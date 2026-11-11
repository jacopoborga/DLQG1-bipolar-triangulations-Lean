/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.RecordBlockCount
public import DirectedDistances.RandomWalk.ConditionedVectorFactorization
public import DirectedDistances.RandomWalk.ConditionedVectorTrajectory

/-! # Positivity of the block event under the constructed law

an explicit legal increment word whose path lies in the block event, so that the
block event has positive mass for the constructed conditioned law. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Explicit increment word: `H` pairs `(0,1),(1,-1)`, then `q` triples
`(0,1),(1,-1),(-1,0)`, then pairs `(1,-1),(-1,0)` forever. -/
@[expose] def blockWord (H q : ℕ) (i : ℕ) : Fin 3 :=
  if i < 2 * H then (if i % 2 = 0 then 1 else 2)
  else if i < 2 * H + 3 * q then
    (if (i - 2 * H) % 3 = 0 then 1 else if (i - 2 * H) % 3 = 1 then 2 else 0)
  else (if (i - (2 * H + 3 * q)) % 2 = 0 then 2 else 0)

/-- Closed form of the path of `blockWord H q` from the origin. -/
@[expose] def blockPath (H q : ℕ) (t : ℕ) : ℤ × ℤ :=
  if t ≤ 2 * H then (((t / 2 : ℕ) : ℤ), ((t % 2 : ℕ) : ℤ))
  else if t ≤ 2 * H + 3 * q then
    ((H : ℤ) + (if (t - 2 * H) % 3 = 2 then 1 else 0),
      (if (t - 2 * H) % 3 = 1 then 1 else 0))
  else
    ((H : ℤ) + (if (t - (2 * H + 3 * q)) % 2 = 1 then 1 else 0),
      -(((t - (2 * H + 3 * q) + 1) / 2 : ℕ) : ℤ))

theorem blockPath_succ (H q t : ℕ) :
    blockPath H q (t + 1) = blockPath H q t + lazyTwoDimensionalStep (blockWord H q t) := by
  have hr : t + 1 ≤ 2 * H ∨ t = 2 * H ∨ (2 * H < t ∧ t + 1 ≤ 2 * H + 3 * q) ∨
      t = 2 * H + 3 * q ∨ 2 * H + 3 * q < t := by omega
  rcases hr with h | h | h | h | h <;>
  · simp (disch := omega) only [blockPath, blockWord, if_pos, if_neg]
    split_ifs <;> simp [Prod.ext_iff] <;> omega

theorem blockPath_eq_sum (H q t : ℕ) :
    blockPath H q t =
      (∑ i ∈ Finset.range t, (lazyTwoDimensionalStep (blockWord H q i)).1,
       ∑ i ∈ Finset.range t, (lazyTwoDimensionalStep (blockWord H q i)).2) := by
  induction t with
  | zero => simp [blockPath]
  | succ t ih =>
    rw [blockPath_succ, ih]
    refine Prod.ext ?_ ?_ <;> simp [Finset.sum_range_succ]

theorem sum_filter_lt_eq_range {N : ℕ} (g : ℕ → ℤ) (m : ℕ) (hm : m ≤ N) :
    ∑ i : Fin N with i.val < m, g i.val = ∑ i ∈ Finset.range m, g i := by
  rw [Finset.sum_filter]
  refine (Fin.sum_univ_eq_sum_range (fun i => if i < m then g i else 0) N).trans ?_
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem lazyTwoDimensionalPrefix_blockWord (H q N : ℕ) (j : Fin (N + 1)) :
    lazyTwoDimensionalPrefix ((0 : ℕ) : ℤ) 0 (fun i : Fin N => blockWord H q i.val) j =
      blockPath H q j.val := by
  rw [blockPath_eq_sum]
  have hj : j.val ≤ N := by omega
  refine Prod.ext ?_ ?_
  · simp only [lazyTwoDimensionalPrefix, Nat.cast_zero, zero_add]
    exact sum_filter_lt_eq_range (fun i => (lazyTwoDimensionalStep (blockWord H q i)).1) _ hj
  · simp only [lazyTwoDimensionalPrefix, zero_add]
    exact sum_filter_lt_eq_range (fun i => (lazyTwoDimensionalStep (blockWord H q i)).2) _ hj

theorem blockPath_fst_nonneg (H q t : ℕ) : 0 ≤ (blockPath H q t).1 := by
  unfold blockPath
  split_ifs <;> simp <;> omega

/-- Under the explicit parameters, the closed-form path satisfies the three block
conditions. -/
theorem blockPath_mem (N : ℕ) (hN : 100 ≤ N) :
    (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
      Real.sqrt n / 100 ≤ ((blockPath ⌈Real.sqrt N / 100⌉₊ ((N + 5) / 6) n).1 : ℝ) ∧
        ((blockPath ⌈Real.sqrt N / 100⌉₊ ((N + 5) / 6) n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
    (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 →
      -Real.sqrt N ≤ ((blockPath ⌈Real.sqrt N / 100⌉₊ ((N + 5) / 6) n).2 : ℝ)) ∧
    ((blockPath ⌈Real.sqrt N / 100⌉₊ ((N + 5) / 6) N).2 : ℝ) ≤ -2 * Real.sqrt N := by
  set s := Real.sqrt N with hs
  set H := ⌈s / 100⌉₊ with hH
  set q := (N + 5) / 6 with hq
  have hNR : (100 : ℝ) ≤ N := by exact_mod_cast hN
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s * s = N := Real.mul_self_sqrt (by positivity)
  have hs10 : 10 ≤ s := by nlinarith
  have hH1 : s / 100 ≤ (H : ℝ) := Nat.le_ceil _
  have hH2 : (H : ℝ) < s / 100 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hHpos : 0 < H := Nat.ceil_pos.mpr (by positivity)
  have hq1 : (N : ℝ) ≤ 6 * q := by
    have : N ≤ 6 * q := by omega
    exact_mod_cast this
  have hq2 : 6 * (q : ℝ) ≤ N + 5 := by
    have : 6 * q ≤ N + 5 := by omega
    exact_mod_cast this
  -- the switch time `T = 2H + 3q`
  have hT1 : (N : ℝ) / 2 ≤ 2 * H + 3 * q := by
    have : (0 : ℝ) ≤ H := by positivity
    linarith
  have hT2 : (2 * (H : ℝ) + 3 * q) + 2 * (2 * s) + 1 ≤ N := by nlinarith
  have hTN : 2 * H + 3 * q + 1 ≤ N := by
    have : ((2 * H + 3 * q + 1 : ℕ) : ℝ) ≤ N := by push_cast; nlinarith
    exact_mod_cast this
  have h2H : (2 * (H : ℝ)) ≤ (N : ℝ) / 2 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro n hn1 hn2
    have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn2
    have hn2H : 2 * H < n := by
      have : (2 * (H : ℝ)) < n := by nlinarith
      exact_mod_cast this
    have hsn : Real.sqrt n ≤ s := Real.sqrt_le_sqrt hnR
    have hsn2 : s / 2 ≤ Real.sqrt n := by
      apply Real.le_sqrt_of_sq_le
      nlinarith
    have hform : (blockPath H q n).1 = (H : ℤ) + (if n ≤ 2 * H + 3 * q then
        (if (n - 2 * H) % 3 = 2 then 1 else 0)
        else (if (n - (2 * H + 3 * q)) % 2 = 1 then 1 else 0)) := by
      unfold blockPath
      by_cases h : n ≤ 2 * H + 3 * q
      · rw [if_neg (by omega), if_pos h, if_pos h]
      · rw [if_neg (by omega), if_neg h, if_neg h]
    have hb : (H : ℤ) ≤ (blockPath H q n).1 ∧ (blockPath H q n).1 ≤ H + 1 := by
      rw [hform]
      split_ifs <;> omega
    have hb1 : (H : ℝ) ≤ ((blockPath H q n).1 : ℝ) := by exact_mod_cast hb.1
    have hb2 : ((blockPath H q n).1 : ℝ) ≤ H + 1 := by exact_mod_cast hb.2
    constructor
    · linarith
    · nlinarith
  · intro n hn
    have hnT : n ≤ 2 * H + 3 * q := by
      have : (n : ℝ) ≤ 2 * H + 3 * q := by linarith
      exact_mod_cast this
    have : 0 ≤ (blockPath H q n).2 := by
      unfold blockPath
      split_ifs <;> simp <;> omega
    have h' : (0 : ℝ) ≤ ((blockPath H q n).2 : ℝ) := by exact_mod_cast this
    linarith
  · have hform : (blockPath H q N).2 =
        -(((N - (2 * H + 3 * q) + 1) / 2 : ℕ) : ℤ) := by
      unfold blockPath
      rw [if_neg (by omega), if_neg (by omega)]
    rw [hform, Int.cast_neg, Int.cast_natCast]
    have hc : (N : ℝ) - (2 * H + 3 * q) ≤ 2 * (((N - (2 * H + 3 * q) + 1) / 2 : ℕ) : ℝ) := by
      have : N - (2 * H + 3 * q) ≤ 2 * ((N - (2 * H + 3 * q) + 1) / 2) := by omega
      have h3 : ((N - (2 * H + 3 * q) : ℕ) : ℝ) ≤
          2 * (((N - (2 * H + 3 * q) + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_sub (by omega)] at h3
      push_cast at h3
      exact h3
    linarith

/-- The block event has positive probability under the constructed conditioned law, -/
theorem conditionedVectorPathLaw_recordBlock_pos (N : ℕ) (hN : 100 ≤ N) :
    0 < (conditionedVectorPathLaw 0 0).real {p : ℕ → ℤ × ℤ |
      (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
        Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
      (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
      ((p N).2 : ℝ) ≤ -2 * Real.sqrt N} := by
  set H := ⌈Real.sqrt N / 100⌉₊ with hH
  set q := (N + 5) / 6 with hq
  set w : Fin N → Fin 3 := fun i => blockWord H q i.val with hw
  have hsub : {p : ℕ → ℤ × ℤ | (fun j : Fin (N + 1) => p j.val) =
      lazyTwoDimensionalPrefix ((0 : ℕ) : ℤ) 0 w} ⊆ {p : ℕ → ℤ × ℤ |
      (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
        Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
      (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
      ((p N).2 : ℝ) ≤ -2 * Real.sqrt N} := by
    intro p hp
    have hpn : ∀ n, n ≤ N → p n = blockPath H q n := by
      intro n hn
      have := congrFun hp ⟨n, by omega⟩
      rw [lazyTwoDimensionalPrefix_blockWord] at this
      exact this
    obtain ⟨h1, h2, h3⟩ := blockPath_mem N hN
    have hNN : ∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → n ≤ N := by
      intro n hn
      have : (n : ℝ) ≤ N := by
        have : (0 : ℝ) ≤ N := by positivity
        linarith
      exact_mod_cast this
    refine ⟨?_, ?_, ?_⟩
    · intro n hn1 hn2
      rw [hpn n hn2]
      exact h1 n hn1 hn2
    · intro n hn
      rw [hpn n (hNN n hn)]
      exact h2 n hn
    · rw [hpn N le_rfl]
      exact h3
  have hatom := conditionedSource_prefix_atom 0 0 (conditionedVectorPathLaw 0 0)
    (conditionedVectorPathLaw_map_prefix 0 0) N w
  have hnn : ∀ j, 0 ≤ (lazyTwoDimensionalPrefix ((0 : ℕ) : ℤ) 0 w j).1 := by
    intro j
    rw [hw, lazyTwoDimensionalPrefix_blockWord]
    exact blockPath_fst_nonneg H q j.val
  rw [if_pos hnn] at hatom
  have hpos : 0 < (conditionedVectorPathLaw 0 0) {p : ℕ → ℤ × ℤ |
      (fun j : Fin (N + 1) => p j.val) =
        lazyTwoDimensionalPrefix ((0 : ℕ) : ℤ) 0 w} := by
    rw [hatom]
    apply ENNReal.mul_pos
    · rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      have h0 := hnn (Fin.last N)
      have : (0 : ℝ) ≤ (((lazyTwoDimensionalPrefix ((0 : ℕ) : ℤ) 0 w (Fin.last N)).1 : ℤ) : ℝ) := by
        exact_mod_cast h0
      positivity
    · simp
  have hne : (conditionedVectorPathLaw 0 0) {p : ℕ → ℤ × ℤ |
      (fun j : Fin (N + 1) => p j.val) =
        lazyTwoDimensionalPrefix ((0 : ℕ) : ℤ) 0 w} ≠ 0 := hpos.ne'
  have hreal : 0 < (conditionedVectorPathLaw 0 0).real {p : ℕ → ℤ × ℤ |
      (fun j : Fin (N + 1) => p j.val) =
        lazyTwoDimensionalPrefix ((0 : ℕ) : ℤ) 0 w} :=
    ENNReal.toReal_pos hne (measure_ne_top _ _)
  exact lt_of_lt_of_le hreal (measureReal_mono hsub)

end DirectedDistances.RandomWalk
