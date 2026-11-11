/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.IIDVectorWalk

/-! # Lattice obstruction for the cone endpoint estimate

The exact endpoint event in `lem-cone-prob-lower`
congruence. This file records that congruence for the literal source walk. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory

private theorem sourceStep_weighted_congruence (c : Fin 3) :
    ∃ q : ℤ, 2 * (lazyTwoDimensionalStep c).1 + (lazyTwoDimensionalStep c).2 =
      1 + 3 * q := by
  fin_cases c
  · exact ⟨-1, by norm_num [lazyTwoDimensionalStep]⟩
  · exact ⟨0, by norm_num [lazyTwoDimensionalStep]⟩
  · exact ⟨0, by norm_num [lazyTwoDimensionalStep]⟩

/-- The linear functional `2x + y` on the literal source walk agrees with -/
theorem codeWalk_weighted_modThree (ω : ℕ → Fin 3) (n : ℕ) :
    ∃ q : ℤ, 2 * (codeWalk ω n).1 + (codeWalk ω n).2 = (n : ℤ) + 3 * q := by
  induction n with
  | zero =>
      refine ⟨0, ?_⟩
      simp [codeWalk_zero]
  | succ n ih =>
      obtain ⟨q, hq⟩ := ih
      obtain ⟨r, hr⟩ := sourceStep_weighted_congruence (ω (n + 1))
      have hstep : codeWalk ω (n + 1) =
          codeWalk ω n + lazyTwoDimensionalStep (ω (n + 1)) := by
        have h := codeWalk_succ_sub ω n
        rw [sub_eq_iff_eq_add] at h
        calc
          codeWalk ω (n + 1) = lazyTwoDimensionalStep (ω (n + 1)) + codeWalk ω n := h
          _ = codeWalk ω n + lazyTwoDimensionalStep (ω (n + 1)) := by abel
      refine ⟨q + r, ?_⟩
      calc
        2 * (codeWalk ω (n + 1)).1 + (codeWalk ω (n + 1)).2 =
            (2 * (codeWalk ω n).1 + (codeWalk ω n).2) +
              (2 * (lazyTwoDimensionalStep (ω (n + 1))).1 +
                (lazyTwoDimensionalStep (ω (n + 1))).2) := by
                  rw [hstep, Prod.fst_add, Prod.snd_add]
                  ring
        _ = (n : ℤ) + 3 * q + (1 + 3 * r) := by rw [hq, hr]
        _ = (↑(n + 1) : ℤ) + 3 * (q + r) := by push_cast; ring

/-- A translated path from `(l, 0)` can reach the origin at time `n` only
This is a necessary lattice condition for the endpoint event. -/
theorem translated_codeWalk_endpoint_modThree (ω : ℕ → Fin 3) (l : ℤ) (n : ℕ)
    (hend : (l, 0) + codeWalk ω n = (0, 0)) :
    ∃ q : ℤ, (n : ℤ) = l + 3 * q := by
  obtain ⟨q, hq⟩ := codeWalk_weighted_modThree ω n
  have hfst : (codeWalk ω n).1 = -l := by
    have h := congrArg Prod.fst hend
    change l + (codeWalk ω n).1 = 0 at h
    omega
  have hsnd : (codeWalk ω n).2 = 0 := by
    have h := congrArg Prod.snd hend
    change 0 + (codeWalk ω n).2 = 0 at h
    omega
  have hweight : 2 * (codeWalk ω n).1 + (codeWalk ω n).2 = -2 * l := by
    rw [hfst, hsnd]
    ring
  rw [hweight] at hq
  refine ⟨-l - q, ?_⟩
  omega

/-- If the period-three endpoint condition fails, the translated cone endpoint
event is empty and has probability zero. The cone condition is retained here -/
theorem iidCodeMeasure_real_translated_coneEndpoint_zero_of_modThree
    (l : ℤ) (n : ℕ)
    (hbad : ¬ ∃ q : ℤ, (n : ℤ) = l + 3 * q) :
    iidCodeMeasure.real {ω : ℕ → Fin 3 |
      (∀ j ≤ n, 0 ≤ ((l, 0) + codeWalk ω j).1 ∧
        0 ≤ ((l, 0) + codeWalk ω j).2) ∧
      (l, 0) + codeWalk ω n = (0, 0)} = 0 := by
  have hempty : {ω : ℕ → Fin 3 |
      (∀ j ≤ n, 0 ≤ ((l, 0) + codeWalk ω j).1 ∧
        0 ≤ ((l, 0) + codeWalk ω j).2) ∧
      (l, 0) + codeWalk ω n = (0, 0)} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hω
    exact hbad (translated_codeWalk_endpoint_modThree ω l n hω.2)
  rw [hempty]
  simp

/-- The all-size lower bound as printed in `eqn-cone-prob-lower` is false for
the literal period-three walk: `n = 9` and `l = 2` satisfy the `A = 2` window,
This records the source obstruction without changing its quantifiers into a
corrected theorem. -/
theorem coneProbLower_source_bound_false :
    ¬ (∀ A : ℝ, 1 < A → ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, 1 ≤ n → ∀ l : ℤ,
        A⁻¹ * Real.sqrt (n : ℝ) ≤ (l : ℝ) →
        (l : ℝ) ≤ A * Real.sqrt (n : ℝ) →
        c * (n : ℝ) ^ (-3 : ℝ) ≤
          iidCodeMeasure.real {ω : ℕ → Fin 3 |
            (∀ j ≤ n, 0 ≤ ((l, 0) + codeWalk ω j).1 ∧
              0 ≤ ((l, 0) + codeWalk ω j).2) ∧
            (l, 0) + codeWalk ω n = (0, 0)}) := by
  intro hclaim
  obtain ⟨c, hc, hbound⟩ := hclaim 2 (by norm_num)
  have hnot : ¬ ∃ q : ℤ, (9 : ℤ) = 2 + 3 * q := by
    rintro ⟨q, hq⟩
    omega
  have hprob := iidCodeMeasure_real_translated_coneEndpoint_zero_of_modThree
    (l := 2) (n := 9) hnot
  have hsqrt : Real.sqrt (9 : ℝ) = 3 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
    norm_num
  have hlow : (2 : ℝ)⁻¹ * Real.sqrt (9 : ℝ) ≤ ((2 : ℤ) : ℝ) := by
    rw [hsqrt]
    norm_num
  have hup : ((2 : ℤ) : ℝ) ≤ (2 : ℝ) * Real.sqrt (9 : ℝ) := by
    rw [hsqrt]
    norm_num
  have hcontr := hbound 9 (by norm_num) 2 hlow hup
  rw [hprob] at hcontr
  have hpos : 0 < c * (9 : ℝ) ^ (-3 : ℝ) := by positivity
  exact (not_le_of_gt hpos hcontr)

end DirectedDistances.RandomWalk
