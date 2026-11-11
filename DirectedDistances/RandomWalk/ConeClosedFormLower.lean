module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Supporting lemmas for paper labels `lem-cone-prob-lower` (see CORRESPONDENCE.md). -/

/-! # Analytic estimates for the closed cone return formula

Analytic core of corrected `lem-cone-prob-lower`, -/

public section
namespace DirectedDistances.RandomWalk



private theorem centralTrinomial_lower (r : ℕ) :
    2 / (9 * (r : ℝ) + 2) ≤
      ((3 * r).factorial : ℝ) /
        ((r.factorial : ℝ) ^ 3 * (3 : ℝ) ^ (3 * r)) := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    have hr : 0 ≤ (r : ℝ) := by positivity
    have hf : (r.factorial : ℝ) ≠ 0 := by positivity
    have hp : (3 : ℝ) ^ (3 * r) ≠ 0 := by positivity
    have hrec :
        ((3 * (r + 1)).factorial : ℝ) /
            (((r + 1).factorial : ℝ) ^ 3 * (3 : ℝ) ^ (3 * (r + 1))) =
          (((3 * r).factorial : ℝ) /
            ((r.factorial : ℝ) ^ 3 * (3 : ℝ) ^ (3 * r))) *
            ((3 * (r : ℝ) + 1) * (3 * r + 2) / (9 * (r + 1) ^ 2)) := by
      rw [show 3 * (r + 1) = 3 * r + 1 + 1 + 1 by omega]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat, pow_add, pow_one]
      field_simp
      ring
    rw [hrec]
    have hb : 2 / (9 * ((r : ℝ) + 1) + 2) ≤
        2 / (9 * (r : ℝ) + 2) *
          ((3 * (r : ℝ) + 1) * (3 * r + 2) / (9 * (r + 1) ^ 2)) := by
      rw [div_mul_div_comm]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith
    push_cast
    exact hb.trans (mul_le_mul_of_nonneg_right ih (by positivity))

/-- The multinomial mass before the explicit boundary correction. -/
private noncomputable def coneTrinomialMass (r l : ℕ) : ℝ :=
  ((3 * r + l).factorial : ℝ) /
    (((r + l).factorial : ℝ) * (r.factorial : ℝ) ^ 2 * (3 : ℝ) ^ (3 * r + l))

private theorem coneTrinomialMass_pos (r l : ℕ) : 0 < coneTrinomialMass r l := by
  unfold coneTrinomialMass
  positivity

private theorem coneTrinomialMass_succ (r l : ℕ) :
    coneTrinomialMass r (l + 1) = coneTrinomialMass r l *
      ((3 * (r : ℝ) + l + 1) / (3 * (r + l + 1))) := by
  unfold coneTrinomialMass
  rw [show 3 * r + (l + 1) = (3 * r + l) + 1 by omega,
    show r + (l + 1) = (r + l) + 1 by omega]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    pow_succ]
  field_simp
  ring

private theorem cone_shift_step (r l : ℝ) (hr : 0 < r) (hl : 0 ≤ l) :
    Real.exp (-(2 * (l + 1) / (3 * r))) ≤
      (3 * r + l + 1) / (3 * (r + l + 1)) := by
  have ht : 0 ≤ 2 * (l + 1) / (3 * r) := by positivity
  have he := Real.add_one_le_exp (2 * (l + 1) / (3 * r))
  have hi := one_div_le_one_div_of_le (by positivity :
    0 < 2 * (l + 1) / (3 * r) + 1) he
  rw [Real.exp_neg, ← one_div]
  apply hi.trans
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  field_simp
  nlinarith

/-- A quadratic exponential cost for shifting the central trinomial coefficient.
This is an analytic ingredient of corrected `lem-cone-prob-lower` -/
private theorem coneTrinomialMass_shift_lower (r l : ℕ) (hr : 0 < r) :
    coneTrinomialMass r 0 *
      Real.exp (-((l : ℝ) * (l + 1) / (3 * r))) ≤ coneTrinomialMass r l := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [coneTrinomialMass_succ]
    have hs := cone_shift_step (r : ℝ) (l : ℝ) (by exact_mod_cast hr) (by positivity)
    have he : -(((l + 1 : ℕ) : ℝ) * (((l + 1 : ℕ) : ℝ) + 1) / (3 * r)) =
        -((l : ℝ) * (l + 1) / (3 * r)) + -(2 * ((l : ℝ) + 1) / (3 * r)) := by
      push_cast
      ring
    rw [he, Real.exp_add, ← mul_assoc]
    exact mul_le_mul ih hs (Real.exp_nonneg _) (le_of_lt (coneTrinomialMass_pos r l))

private theorem coneTrinomialMass_zero (r : ℕ) :
    coneTrinomialMass r 0 = ((3 * r).factorial : ℝ) /
      ((r.factorial : ℝ) ^ 3 * (3 : ℝ) ^ (3 * r)) := by
  unfold coneTrinomialMass
  simp only [Nat.add_zero]
  congr 1
  ring



private theorem coneTrinomialMass_lower (r l : ℕ) (hr : 0 < r) :
    2 / (9 * (r : ℝ) + 2) *
      Real.exp (-((l : ℝ) * (l + 1) / (3 * r))) ≤ coneTrinomialMass r l := by
  apply le_trans _ (coneTrinomialMass_shift_lower r l hr)
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  rw [coneTrinomialMass_zero]
  exact centralTrinomial_lower r



private theorem coneClosedForm_factorization (r l : ℕ) :
    ((3 * r + l).factorial : ℝ) * (((l + 1) * (l + 2) : ℕ) : ℝ) /
      (((r + l + 2).factorial : ℝ) * ((r + 1).factorial : ℝ) *
        (r.factorial : ℝ) * (3 : ℝ) ^ (3 * r + l)) =
    coneTrinomialMass r l * (((l : ℝ) + 1) * (l + 2)) /
      (((r : ℝ) + l + 1) * (r + l + 2) * (r + 1)) := by
  unfold coneTrinomialMass
  rw [show r + l + 2 = (r + l + 1) + 1 by omega]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat]
  field_simp
  ring

private theorem coneBand_squares (A n l : ℝ) (hA : 0 < A) (hn : 0 ≤ n)
    (hl : 0 ≤ l) (hlo : A⁻¹ * Real.sqrt n ≤ l)
    (hhi : l ≤ A * Real.sqrt n) :
    n ≤ A ^ 2 * l ^ 2 ∧ l ^ 2 ≤ A ^ 2 * n := by
  have hs := Real.sq_sqrt hn
  have hsn := Real.sqrt_nonneg n
  have ha : Real.sqrt n ≤ A * l := by
    have := mul_le_mul_of_nonneg_left hlo hA.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul] using this
  constructor
  · nlinarith [sq_nonneg (A * l - Real.sqrt n)]
  · nlinarith [sq_nonneg (A * Real.sqrt n - l)]

private theorem coneBand_size (A : ℝ) (r l : ℕ)
    (hhi : (l : ℝ) ≤ A * Real.sqrt ((3 * r + l : ℕ) : ℝ)) :
    ((3 * r + l : ℕ) : ℝ) ≤ 6 * (r : ℝ) + A ^ 2 := by
  have hs := Real.sq_sqrt (show 0 ≤ ((3 * r + l : ℕ) : ℝ) by positivity)
  have hq := sq_nonneg (Real.sqrt ((3 * r + l : ℕ) : ℝ) - A)
  push_cast at *
  nlinarith

/-- Analytic core of corrected `lem-cone-prob-lower`
walk probability is a separate result. -/
theorem coneClosedForm_lower (A : ℝ) (hA : 1 < A) :
    ∃ c : ℝ, 0 < c ∧ ∀ r l : ℕ, 1 ≤ 3 * r + l →
      A⁻¹ * Real.sqrt ((3 * r + l : ℕ) : ℝ) ≤ (l : ℝ) →
      (l : ℝ) ≤ A * Real.sqrt ((3 * r + l : ℕ) : ℝ) →
      c * (((3 * r + l : ℕ) : ℝ) ^ (3 : ℕ))⁻¹ ≤
        ((3 * r + l).factorial : ℝ) * (((l + 1) * (l + 2) : ℕ) : ℝ) /
          (((r + l + 2).factorial : ℝ) * ((r + 1).factorial : ℝ) *
            (r.factorial : ℝ) * (3 : ℝ) ^ (3 * r + l)) := by
  have hA0 : 0 < A := lt_trans zero_lt_one hA
  let K : ℝ := 2 * A ^ 2 * (6 + A ^ 2)
  let c₁ : ℝ := Real.exp (-K) / (297 * A ^ 2)
  let c₀ : ℝ := Real.exp (-(A ^ 2 * Real.log 3))
  have hc₁ : 0 < c₁ := by dsimp [c₁]; positivity
  have hc₀ : 0 < c₀ := Real.exp_pos _
  refine ⟨min c₁ c₀, lt_min hc₁ hc₀, ?_⟩
  intro r l hn hlo hhi
  let n : ℝ := ((3 * r + l : ℕ) : ℝ)
  have hn1 : 1 ≤ n := by dsimp [n]; exact_mod_cast hn
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn1
  have hln : 0 ≤ (l : ℝ) := by positivity
  obtain ⟨hlower, hupper⟩ := coneBand_squares A n l hA0 hn0.le hln hlo hhi
  have hlpos : 0 < (l : ℝ) :=
    lt_of_lt_of_le (mul_pos (inv_pos.mpr hA0) (Real.sqrt_pos.mpr hn0)) hlo
  have hl1nat : 1 ≤ l := by exact_mod_cast (show 0 < l by exact_mod_cast hlpos)
  have hl1 : 1 ≤ (l : ℝ) := by exact_mod_cast hl1nat
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hn_eq : n = (l : ℝ) := by simp [n]
    have hlA : (l : ℝ) ≤ A ^ 2 := by
      rw [hn_eq] at hupper
      nlinarith
    have hpow : (3 : ℝ) ^ l ≤ Real.exp (A ^ 2 * Real.log 3) := by
      calc
        (3 : ℝ) ^ l = Real.exp ((l : ℝ) * Real.log 3) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
        _ ≤ _ := Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right hlA (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)))
    have hzero :
        ((3 * 0 + l).factorial : ℝ) * (((l + 1) * (l + 2) : ℕ) : ℝ) /
          (((0 + l + 2).factorial : ℝ) * ((0 + 1).factorial : ℝ) *
            ((0 : ℕ).factorial : ℝ) * (3 : ℝ) ^ (3 * 0 + l)) = ((3 : ℝ) ^ l)⁻¹ := by
      simp only [Nat.mul_zero, Nat.zero_add, Nat.factorial_one, Nat.factorial_zero,
        Nat.cast_one, mul_one]
      rw [show l + 2 = (l + 1) + 1 by omega]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp
    rw [hzero]
    have hc : c₀ ≤ ((3 : ℝ) ^ l)⁻¹ := by
      dsimp [c₀]
      rw [Real.exp_neg]
      simpa only [one_div] using (one_div_le_one_div_of_le (by positivity) hpow)
    have hn3 : 1 ≤ n ^ 3 := one_le_pow₀ hn1
    calc
      min c₁ c₀ * (n ^ 3)⁻¹ ≤ c₀ * (n ^ 3)⁻¹ :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ ≤ c₀ := by
        apply mul_le_of_le_one_right hc₀.le
        exact (inv_le_one₀ (by positivity)).2 hn3
      _ ≤ _ := hc
  · have hr1 : 1 ≤ (r : ℝ) := by exact_mod_cast hr
    have hr0 : 0 < (r : ℝ) := by exact_mod_cast hr
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hsize : n ≤ 6 * (r : ℝ) + A ^ 2 := coneBand_size A r l hhi
    have hnr : n ≤ (6 + A ^ 2) * (r : ℝ) := by
      nlinarith [mul_nonneg (sq_nonneg A) (sub_nonneg.mpr hr1)]
    have hquad : (l : ℝ) * (l + 1) ≤ K * (r : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hnr (sq_nonneg A)
      dsimp [K]
      nlinarith
    have hE : (l : ℝ) * (l + 1) / (3 * r) ≤ K := by
      apply (div_le_iff₀ (by positivity)).2
      exact hquad.trans (mul_le_mul_of_nonneg_left (by linarith) hK)
    have he : Real.exp (-K) ≤ Real.exp (-((l : ℝ) * (l + 1) / (3 * r))) :=
      Real.exp_le_exp.mpr (neg_le_neg hE)
    have hn_eq : n = 3 * (r : ℝ) + l := by simp [n]
    have hrat : 1 / (11 * n) ≤ 2 / (9 * (r : ℝ) + 2) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith
    have hmass : Real.exp (-K) / (11 * n) ≤ coneTrinomialMass r l := by
      calc
        Real.exp (-K) / (11 * n) = 1 / (11 * n) * Real.exp (-K) := by ring
        _ ≤ 2 / (9 * (r : ℝ) + 2) *
            Real.exp (-((l : ℝ) * (l + 1) / (3 * r))) :=
          mul_le_mul hrat he (by positivity) (by positivity)
        _ ≤ _ := coneTrinomialMass_lower r l hr
    have hden : ((r : ℝ) + l + 1) * (r + l + 2) * (r + 1) ≤ 27 * n ^ 3 := by
      have h₁ : (r : ℝ) + l + 1 ≤ 3 * n := by nlinarith
      have h₂ : (r : ℝ) + l + 2 ≤ 3 * n := by nlinarith
      have h₃ : (r : ℝ) + 1 ≤ 3 * n := by nlinarith
      have hm := mul_le_mul (mul_le_mul h₁ h₂ (by positivity) (by positivity))
        h₃ (by positivity) (by positivity)
      nlinarith only [hm]
    have hpoly : n / A ^ 2 ≤ ((l : ℝ) + 1) * (l + 2) := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith
    rw [coneClosedForm_factorization]
    apply le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
    change c₁ * (n ^ 3)⁻¹ ≤ _
    have hm := mul_le_mul hmass hpoly (by positivity) (coneTrinomialMass_pos r l).le
    have hdpos : 0 < ((r : ℝ) + l + 1) * (r + l + 2) * (r + 1) := by positivity
    apply (le_div_iff₀ hdpos).2
    have hc_id : c₁ * (n ^ 3)⁻¹ * (27 * n ^ 3) =
        Real.exp (-K) / (11 * n) * (n / A ^ 2) := by
      dsimp [c₁]
      field_simp
      ring
    calc
      c₁ * (n ^ 3)⁻¹ * (((r : ℝ) + l + 1) * (r + l + 2) * (r + 1)) ≤
          c₁ * (n ^ 3)⁻¹ * (27 * n ^ 3) :=
        mul_le_mul_of_nonneg_left hden (by positivity)
      _ = _ := hc_id
      _ ≤ _ := hm

end DirectedDistances.RandomWalk
