/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.QuadrantBridgePadding
public import DirectedDistances.RandomWalk.IIDWalkMaximalTailBound
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! # Counting bounded middle words toward Proposition 3.9 -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- Helper toward Proposition 3.9: the event that the first `m` iid source
codes form a bounded padding middle word. -/
def boundedPaddingMiddleWordsGoodEvent (m k : ℕ) : Set (ℕ → Fin 3) :=
  {ω | ∃ w : BoundedPaddingMiddleWords m k,
    w.1 = List.ofFn (fun i : Fin m => ω (i.val + 1))}

private theorem paddingWordDisplacement_ofFn (n : ℕ) (f : Fin n → Fin 3) :
    paddingWordDisplacement (List.ofFn f) = ∑ i : Fin n, lazyTwoDimensionalStep (f i) := by
  induction n with
  | zero => simp [paddingWordDisplacement]
  | succ n ih =>
      rw [List.ofFn_succ', List.concat_eq_append, paddingWordDisplacement_append, ih,
        Fin.sum_univ_castSucc]
      simp [paddingWordDisplacement]

private theorem listTake_ofFn (m j : ℕ) (hj : j ≤ m) (f : Fin m → Fin 3) :
    List.ofFn (fun i : Fin j => f (Fin.castLE hj i)) = (List.ofFn f).take j := by
  apply List.ext_get
  · simp [hj]
  · intro n hn₁ hn₂
    simp [Fin.castLE]

/-- Helper toward Proposition 3.9: the displacement of the first `j` codes
of a finite iid code block is the source walk at time `j`. -/
theorem paddingWordDisplacement_firstCodes_take_eq_codeWalk
    (m : ℕ) (ω : ℕ → Fin 3) (j : ℕ) (hj : j ≤ m) :
    paddingWordDisplacement
        ((List.ofFn (fun i : Fin m => ω (i.val + 1))).take j) = codeWalk ω j := by
  rw [← listTake_ofFn m j hj (fun i : Fin m => ω (i.val + 1)),
    paddingWordDisplacement_ofFn]
  simp only [Fin.val_castLE]
  simpa [codeWalk] using
    (Fin.sum_univ_eq_sum_range
      (fun i => lazyTwoDimensionalStep (ω (i + 1))) j)

/-- Helper toward Proposition 3.9: the first `m` transition codes have the
uniform law on all length-`m` code words. -/
theorem iidCodeMeasure_map_firstCodes (m : ℕ) :
    iidCodeMeasure.map (fun ω : ℕ → Fin 3 => fun i : Fin m => ω (i.val + 1)) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin m → Fin 3)) := by
  classical
  have hf : (fun ω : ℕ → Fin 3 => fun i : Fin m => ω (i.val + 1)) =
      (fun q : Fin (m + 1) → Fin 3 => fun i : Fin m => q i.succ) ∘
        (fun ω : ℕ → Fin 3 => fun j : Fin (m + 1) => ω j.val) := by
    funext ω i
    rfl
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop), iidCodeMeasure_map_prefix]
  have hmp := measurePreserving_piFinSuccAbove
    (fun j : Fin (m + 1) => if j.val = 0 then Measure.dirac (0 : Fin 3)
      else uniformCodeMeasure) 0
  have hsnd : (fun q : Fin (m + 1) → Fin 3 => fun i : Fin m => q i.succ) =
      Prod.snd ∘ MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Fin 3) 0 := by
    funext q i
    simp [MeasurableEquiv.piFinSuccAbove]
    rfl
  rw [hsnd, ← Measure.map_map measurable_snd (MeasurableEquiv.measurable _),
    hmp.map_eq, Measure.map_snd_prod]
  simp only [Fin.val_zero, ite_true, measure_univ, one_smul, Fin.val_succ,
    Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, Fin.succAbove_zero]
  apply Measure.ext_of_singleton
  intro w
  rw [Measure.pi_singleton, Measure.uniformOfFinset_apply_singleton]
  simp [uniformCodeMeasure, Measure.uniformOfFinset_apply_singleton, ENNReal.inv_pow]

private theorem boundedPaddingMiddleWordsGoodEvent_iff (m k : ℕ) (ω : ℕ → Fin 3) :
    ω ∈ boundedPaddingMiddleWordsGoodEvent m k ↔
      ∀ j ≤ m,
        -(k : ℤ) ≤ (codeWalk ω j).1 ∧ (codeWalk ω j).1 ≤ k ∧
          -(k : ℤ) ≤ (codeWalk ω j).2 ∧ (codeWalk ω j).2 ≤ k := by
  constructor
  · rintro ⟨w, hw⟩ j hj
    have hb := w.2.2 j hj
    rw [hw] at hb
    rw [paddingWordDisplacement_firstCodes_take_eq_codeWalk m ω j hj] at hb
    exact hb
  · intro h
    refine ⟨⟨List.ofFn (fun i : Fin m => ω (i.val + 1)), by simp, ?_⟩, rfl⟩
    intro j hj
    rw [paddingWordDisplacement_firstCodes_take_eq_codeWalk m ω j hj]
    exact h j hj

private theorem paddingAbs_ge_of_not_in_interval (k : ℕ) (x : ℤ)
    (h : ¬ (-(k : ℤ) ≤ x ∧ x ≤ k)) : (k : ℝ) ≤ |(x : ℝ)| := by
  by_cases hx : 0 ≤ x
  · have hxk : (k : ℤ) < x := by
      by_contra hnot
      exact h ⟨by omega, le_of_not_gt hnot⟩
    have hxk' : (k : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxk.le
    simpa [abs_of_nonneg (show (0 : ℝ) ≤ (x : ℝ) by exact_mod_cast hx)] using hxk'
  · have hxk : x < -(k : ℤ) := by
      by_contra hnot
      exact h ⟨le_of_not_gt hnot, by omega⟩
    have hxk' : (k : ℝ) ≤ -((x : ℝ)) := by
      exact_mod_cast (show (k : ℤ) ≤ -x by omega)
    simpa [abs_of_nonpos (show (x : ℝ) ≤ 0 by exact_mod_cast (le_of_not_ge hx))]
      using hxk'

/-- Helper toward Proposition 3.9: failure of the bounded middle-word event
forces a coordinate displacement to reach the cutoff `k` by time `m`. -/
theorem boundedPaddingMiddleWordsGoodEvent_compl_subset_blockMax (m k : ℕ) :
    (boundedPaddingMiddleWordsGoodEvent m k)ᶜ ⊆
      {ω | ∃ j ≤ m,
        (k : ℝ) ≤ |(((codeWalk ω (0 + j) - codeWalk ω 0).1 : ℤ) : ℝ)| ∨
        (k : ℝ) ≤ |(((codeWalk ω (0 + j) - codeWalk ω 0).2 : ℤ) : ℝ)|} := by
  intro ω hω
  have hnot : ¬ ∀ j ≤ m,
      -(k : ℤ) ≤ (codeWalk ω j).1 ∧ (codeWalk ω j).1 ≤ k ∧
        -(k : ℤ) ≤ (codeWalk ω j).2 ∧ (codeWalk ω j).2 ≤ k := by
    intro hgood
    exact hω ((boundedPaddingMiddleWordsGoodEvent_iff m k ω).2 hgood)
  push Not at hnot
  obtain ⟨j, hj, hbad⟩ := hnot
  have hpair :
      ¬ (-(k : ℤ) ≤ (codeWalk ω j).1 ∧ (codeWalk ω j).1 ≤ k) ∨
      ¬ (-(k : ℤ) ≤ (codeWalk ω j).2 ∧ (codeWalk ω j).2 ≤ k) := by
    by_cases hx : -(k : ℤ) ≤ (codeWalk ω j).1 ∧ (codeWalk ω j).1 ≤ k
    · by_cases hy0 : -(k : ℤ) ≤ (codeWalk ω j).2
      · right
        intro hy
        have hout := hbad hx.1 hx.2 hy0
        exact (not_le_of_gt hout) hy.2
      · right
        intro hy
        exact hy0 hy.1
    · exact Or.inl hx
  refine ⟨j, hj, ?_⟩
  rcases hpair with hx | hy
  · left
    have habs := paddingAbs_ge_of_not_in_interval k (codeWalk ω j).1 hx
    simpa [Nat.zero_add, codeWalk_zero] using habs
  · right
    have habs := paddingAbs_ge_of_not_in_interval k (codeWalk ω j).2 hy
    simpa [Nat.zero_add, codeWalk_zero] using habs

end DirectedDistances.RandomWalk
