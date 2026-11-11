/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Semiring

/-! Supporting lemmas for paper labels `lem-cell-ldp-lower` (see CORRESPONDENCE.md). -/

/-! The trivial case `A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ) ≤ 1` is handled by the existence of a single
directed edge, which is a separate map-level obligation. -/

public section
namespace DirectedDistances.PaperProofs.Section7



theorem lower_nontrivial_cell_cutoff_ge_two (A ε : ℝ) (hA : 1 < A) (hε : 0 < ε)
    (hAe : 2 ≤ A ^ ε) (n : ℕ)
    (hthreshold : 1 < A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ)) :
    2 ≤ ⌊A ^ (-(2 / 3 : ℝ) + ε) * (n : ℝ) ^ (1 / 2 : ℝ)⌋₊ := by
  have hApos : 0 < A := lt_trans zero_lt_one hA
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hnnonneg : 0 ≤ (n : ℝ) := by positivity
  have hbase : A < (n : ℝ) ^ (3 / 4 : ℝ) := by
    calc
      A = A * 1 := by ring
      _ < A * (A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ)) :=
        mul_lt_mul_of_pos_left hthreshold hApos
      _ = (n : ℝ) ^ (3 / 4 : ℝ) := by
        rw [← mul_assoc, mul_inv_cancel₀ hAne, one_mul]
  have hpow : A ^ (2 / 3 : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      A ^ (2 / 3 : ℝ) < ((n : ℝ) ^ (3 / 4 : ℝ)) ^ (2 / 3 : ℝ) :=
        Real.rpow_lt_rpow (le_of_lt hApos) hbase (by norm_num)
      _ = (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_mul hnnonneg (3 / 4 : ℝ) (2 / 3 : ℝ)]
        norm_num
  have hAepsgt : 1 < A ^ ε := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt hA hε
  have hAepspos : 0 < A ^ ε := lt_trans zero_lt_one hAepsgt
  have hA23pos : 0 < A ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hApos _
  have hratio : 1 < (A ^ (2 / 3 : ℝ))⁻¹ * (n : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      1 = (A ^ (2 / 3 : ℝ))⁻¹ * A ^ (2 / 3 : ℝ) :=
        (inv_mul_cancel₀ hA23pos.ne').symm
      _ < (A ^ (2 / 3 : ℝ))⁻¹ * (n : ℝ) ^ (1 / 2 : ℝ) :=
        mul_lt_mul_of_pos_left hpow (inv_pos.mpr hA23pos)
  have hfactor : A ^ (-(2 / 3 : ℝ) + ε) =
      A ^ ε * (A ^ (2 / 3 : ℝ))⁻¹ := by
    rw [show -(2 / 3 : ℝ) + ε = ε - (2 / 3 : ℝ) by ring,
      Real.rpow_sub hApos, div_eq_mul_inv]
  have hreal : 2 ≤ A ^ (-(2 / 3 : ℝ) + ε) * (n : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      2 ≤ A ^ ε := hAe
      _ ≤ A ^ ε * ((A ^ (2 / 3 : ℝ))⁻¹ * (n : ℝ) ^ (1 / 2 : ℝ)) :=
        (by
          have hlt := mul_lt_mul_of_pos_left hratio hAepspos
          simpa only [mul_one] using hlt.le)
      _ = (A ^ ε * (A ^ (2 / 3 : ℝ))⁻¹) * (n : ℝ) ^ (1 / 2 : ℝ) := by
        ring
      _ = A ^ (-(2 / 3 : ℝ) + ε) * (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← hfactor]
  exact (Nat.le_floor_iff' (by decide : 2 ≠ 0)).2 hreal

end DirectedDistances.PaperProofs.Section7
