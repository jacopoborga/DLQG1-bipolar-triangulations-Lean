/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.QuadrantReturnCount
public import DirectedDistances.RandomWalk.QuadrantReturnProb
public import DirectedDistances.RandomWalk.ConeClosedFormLower
public import DirectedDistances.RandomWalk.ConeProbLower

/-! # Corrected lower bound for the cone endpoint event

This file proves the author-corrected `lem-cone-prob-lower` statement
admissible domain. The proof routes through the exact closed-quadrant return
Denisov–Wachtel cone theorems. The uncorrected printed form is false, as
recorded by `coneProbLower_source_bound_false`. This Lean statement is not an -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory

/-- The finite-word cone count and the recursively defined closed-quadrant
return count agree. -/
theorem coneWordCount_eq_quadrantReturnCount : ∀ n x y,
    coneWordCount n x y = quadrantReturnCount n x y := by
  intro n
  induction n with
  | zero =>
      intro x y
      rw [coneWordCount_zero]
      rfl
  | succ n ih =>
      intro x y
      rw [coneWordCount_succ, quadrantReturnCount]
      rw [ih (x - 1) y, ih x (y + 1), ih (x + 1) (y - 1)]

/-- The author-corrected `lem-cone-prob-lower` statement (Lemma 5.17,
`ℓ ≤ n` and `n ≡ ℓ (mod 3)` are imposed alongside the same band, with one
positive `c(A)` for all admissible sizes. The route uses the exact closed-
instead of the cited Denisov–Wachtel cone theorems. The uncorrected printed
form is false (`coneProbLower_source_bound_false`). This Lean statement is not -/
theorem coneProbLower_corrected (A : ℝ) (hA : 1 < A) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ l : ℤ,
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (l : ℝ) →
      (l : ℝ) ≤ A * Real.sqrt (n : ℝ) →
      l ≤ (n : ℤ) →
      (∃ q : ℤ, (n : ℤ) = l + 3 * q) →
      c * (n : ℝ) ^ (-3 : ℝ) ≤
        iidCodeMeasure.real {ω : ℕ → Fin 3 |
          (∀ j ≤ n, 0 ≤ ((l, 0) + codeWalk ω j).1 ∧
            0 ≤ ((l, 0) + codeWalk ω j).2) ∧
          (l, 0) + codeWalk ω n = (0, 0)} := by
  obtain ⟨c, hc, hclosedLower⟩ := coneClosedForm_lower A hA
  refine ⟨c, hc, ?_⟩
  intro n hn l hlo hhi hln hcong
  have hn0 : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hA0 : 0 < A := by linarith
  have hlpos : 0 < (l : ℝ) :=
    lt_of_lt_of_le (mul_pos (inv_pos.mpr hA0) (Real.sqrt_pos.mpr hn0)) hlo
  have hl0 : (0 : ℤ) ≤ l := by exact_mod_cast (le_of_lt hlpos)
  obtain ⟨L, hL⟩ := Int.eq_ofNat_of_zero_le hl0
  obtain ⟨q, hq⟩ := hcong
  have hq0 : 0 ≤ q := by omega
  have hqt : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq0
  have hqInt : (n : ℤ) = (L : ℤ) + 3 * (q.toNat : ℤ) := by
    rw [hL] at hq
    omega
  have hqNat : n = L + 3 * q.toNat := by exact_mod_cast hqInt
  let r : ℕ := (n - L) / 3
  have hrn : n = 3 * r + L := by
    dsimp [r]
    omega
  have hLle : L ≤ n := by omega
  have hLlo : A⁻¹ * Real.sqrt ((3 * r + L : ℕ) : ℝ) ≤ (L : ℝ) := by
    simpa [hrn, hL] using hlo
  have hLhi : (L : ℝ) ≤ A * Real.sqrt ((3 * r + L : ℕ) : ℝ) := by
    simpa [hrn, hL] using hhi
  have hlower := hclosedLower r L (by omega) hLlo hLhi
  have hevent :
      {ω : ℕ → Fin 3 |
        (∀ j ≤ n, 0 ≤ ((l, 0) + codeWalk ω j).1 ∧
          0 ≤ ((l, 0) + codeWalk ω j).2) ∧
        (l, 0) + codeWalk ω n = (0, 0)} = coneEvent (L : ℤ) 0 n := by
    rw [← hL]
    rfl
  have hcount := quadrantReturnCount_closedForm r L 0
  have hcount' :
      quadrantReturnCount (3 * r + L) L 0 *
          ((r + L + 2).factorial * (r + 1).factorial * r.factorial) =
        (3 * r + L).factorial * ((L + 1) * (L + 2)) := by
    simpa using hcount
  have hcountR' :
      (quadrantReturnCount (3 * r + L) L 0 : ℝ) *
          (((r + L + 2).factorial : ℝ) * ((r + 1).factorial : ℝ) *
            (r.factorial : ℝ)) =
        ((3 * r + L).factorial : ℝ) * (((L + 1) * (L + 2) : ℕ) : ℝ) := by
    exact_mod_cast hcount'
  have hprobFormula :
      iidCodeMeasure.real (coneEvent (L : ℤ) 0 n) =
        ((n.factorial : ℝ) * (((L + 1) * (L + 2) : ℕ) : ℝ)) /
          (((r + L + 2).factorial : ℝ) * ((r + 1).factorial : ℝ) *
            (r.factorial : ℝ) * (3 : ℝ) ^ (3 * r + L)) := by
    rw [iidCodeMeasure_real_coneEvent_zero_snd,
      coneWordCount_eq_quadrantReturnCount]
    rw [hrn]
    have hfacpos :
        0 < ((r + L + 2).factorial : ℝ) * ((r + 1).factorial : ℝ) *
          (r.factorial : ℝ) := by positivity
    have hfacne :
        ((r + L + 2).factorial : ℝ) * ((r + 1).factorial : ℝ) *
          (r.factorial : ℝ) ≠ 0 := ne_of_gt hfacpos
    calc
      (quadrantReturnCount (3 * r + L) L 0 : ℝ) / (3 : ℝ) ^ (3 * r + L) =
          ((quadrantReturnCount (3 * r + L) L 0 : ℝ) *
            (((r + L + 2).factorial : ℝ) * ((r + 1).factorial : ℝ) *
              (r.factorial : ℝ))) /
            ((((r + L + 2).factorial : ℝ) * ((r + 1).factorial : ℝ) *
              (r.factorial : ℝ)) * (3 : ℝ) ^ (3 * r + L)) := by
        field_simp [hfacne]
      _ = _ := by rw [hcountR']
  have hpow :
      (n : ℝ) ^ (-3 : ℝ) = (((3 * r + L : ℕ) : ℝ) ^ (3 : ℕ))⁻¹ := by
    rw [Real.rpow_neg (by positivity) (3 : ℝ)]
    simp [hrn]
  rw [hevent]
  calc
    c * (n : ℝ) ^ (-3 : ℝ) =
        c * (((3 * r + L : ℕ) : ℝ) ^ (3 : ℕ))⁻¹ := by rw [hpow]
    _ ≤ ((n.factorial : ℝ) * (((L + 1) * (L + 2) : ℕ) : ℝ)) /
          (((r + L + 2).factorial : ℝ) * ((r + 1).factorial : ℝ) *
            (r.factorial : ℝ) * (3 : ℝ) ^ (3 * r + L)) := by
      simpa [hrn] using hlower
    _ = iidCodeMeasure.real (coneEvent (L : ℤ) 0 n) := hprobFormula.symm

end DirectedDistances.RandomWalk
