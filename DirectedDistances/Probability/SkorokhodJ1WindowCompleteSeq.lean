/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodJ1WindowDCirc

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/

@[expose] public section
namespace DirectedDistances.Probability

open Filter
open scoped ENNReal





theorem exists_timeChange_of_dCirc_lt {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T) (ε : ℝ) (hε : 0 < ε)
    (h : j1WindowDCirc hT f g < ENNReal.ofReal ε) :
    ∃ φ : J1TimeChange T, j1TimeChangeSlopeNorm φ < ENNReal.ofReal ε ∧
      ∀ t, |f.1 (φ t) - g.1 t| < ε := by
  let : Nonempty (J1Window T) :=
    ⟨⟨0, ⟨le_rfl, hT.le⟩⟩⟩
  let : Nonempty (J1TimeChange T) := ⟨OrderIso.refl _⟩
  change (⨅ φ : J1TimeChange T, j1WindowDCircCost f g φ) < _ at h
  obtain ⟨φ, hφ⟩ := exists_lt_of_ciInf_lt h
  change max (j1TimeChangeSlopeNorm φ)
      (ENNReal.ofReal (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|)) < _ at hφ
  have hnorm : j1TimeChangeSlopeNorm φ < ENNReal.ofReal ε :=
    (le_max_left _ _).trans_lt hφ
  have hvalue : ENNReal.ofReal (⨆ t : J1Window T,
      |f.1 (φ t) - g.1 t|) < ENNReal.ofReal ε :=
    (le_max_right _ _).trans_lt hφ
  have hsup : (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|) < ε :=
    (ENNReal.ofReal_lt_ofReal_iff hε).mp hvalue
  refine ⟨φ, hnorm, ?_⟩
  intro t
  exact (le_ciSup_of_le (j1WindowValueError_bddAbove f g φ) t le_rfl).trans_lt hsup





theorem exists_dCirc_cauchy_subseq_timeChanges {T : ℝ} (hT : 0 < T)
    (x : ℕ → CadlagWindow T)
    (hC : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      j1WindowDCirc hT (x m) (x n) < ENNReal.ofReal ε) :
    ∃ φ : ℕ → ℕ, ∃ μ : ℕ → J1TimeChange T,
      StrictMono φ ∧
      (∀ k, j1WindowDCirc hT (x (φ (k + 1))) (x (φ k)) <
        ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) ∧
      (∀ k, j1TimeChangeSlopeNorm (μ k) < ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) ∧
      (∀ k t, |(x (φ (k + 1))).1 (μ k t) - (x (φ k)).1 t| <
        (1 / 2 : ℝ) ^ k) ∧
      (∑' j, j1TimeChangeSlopeNorm (μ j) < ⊤) ∧
      (∀ k, ∑' j, j1TimeChangeSlopeNorm (μ (k + j)) ≤
        ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ k)) := by
  classical
  let δ : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k
  let N : ℕ → ℕ := fun k => Classical.choose (hC (δ k) (by positivity))
  have hN (k m n : ℕ) (hm : N k ≤ m) (hn : N k ≤ n) :
      j1WindowDCirc hT (x m) (x n) < ENNReal.ofReal (δ k) :=
    Classical.choose_spec (hC (δ k) (by positivity)) m n hm hn
  obtain ⟨φ, hφmono, hφN⟩ :=
    Filter.extraction_forall_of_eventually
      (P := fun k m => N k ≤ m)
      (fun k => Filter.eventually_atTop.2 ⟨N k, fun m hm => hm⟩)
  have hstep (k : ℕ) :
      j1WindowDCirc hT (x (φ (k + 1))) (x (φ k)) < ENNReal.ofReal (δ k) := by
    apply hN k (φ (k + 1)) (φ k)
    · exact le_trans (hφN k) (Nat.le_of_lt (hφmono (Nat.lt_succ_self k)))
    · exact hφN k
  let μ : ℕ → J1TimeChange T := fun k =>
    Classical.choose (exists_timeChange_of_dCirc_lt hT
      (x (φ (k + 1))) (x (φ k)) (δ k) (by positivity) (hstep k))
  have hμ (k : ℕ) :
      j1TimeChangeSlopeNorm (μ k) < ENNReal.ofReal (δ k) ∧
      ∀ t, |(x (φ (k + 1))).1 (μ k t) - (x (φ k)).1 t| < δ k :=
    Classical.choose_spec (exists_timeChange_of_dCirc_lt hT
      (x (φ (k + 1))) (x (φ k)) (δ k) (by positivity) (hstep k))
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2⁻¹ : ℝ≥0∞) := by
    have hdiv : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
    rw [hdiv, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hterm (j : ℕ) :
      j1TimeChangeSlopeNorm (μ j) ≤ (2⁻¹ : ℝ≥0∞) ^ j := by
    apply le_of_lt
    calc
      j1TimeChangeSlopeNorm (μ j) < ENNReal.ofReal (δ j) := (hμ j).1
      _ = (2⁻¹ : ℝ≥0∞) ^ j := by
        rw [ENNReal.ofReal_pow (by norm_num : 0 ≤ (1 / 2 : ℝ)), hhalf]
  have hsum_le :
      (∑' j, j1TimeChangeSlopeNorm (μ j)) ≤ (2 : ℝ≥0∞) := by
    calc
      (∑' j, j1TimeChangeSlopeNorm (μ j)) ≤
          ∑' j, (2⁻¹ : ℝ≥0∞) ^ j := tsum_le_tsum (fun j => hterm j)
      _ = 2 := ENNReal.tsum_geometric_two
  have htail_le (k : ℕ) :
      (∑' j, j1TimeChangeSlopeNorm (μ (k + j))) ≤
        ENNReal.ofReal (2 * δ k) := by
    calc
      (∑' j, j1TimeChangeSlopeNorm (μ (k + j))) ≤
          ∑' j, (2⁻¹ : ℝ≥0∞) ^ (k + j) :=
        tsum_le_tsum (fun j => hterm (k + j))
      _ = (2⁻¹ : ℝ≥0∞) ^ k *
          ∑' j, (2⁻¹ : ℝ≥0∞) ^ j := by
        simp_rw [pow_add]
        rw [ENNReal.tsum_mul_left]
      _ = ENNReal.ofReal (2 * δ k) := by
        rw [ENNReal.tsum_geometric_two]
        change (2⁻¹ : ℝ≥0∞) ^ k * 2 =
          ENNReal.ofReal (2 * ((1 / 2 : ℝ) ^ k))
        calc
          (2⁻¹ : ℝ≥0∞) ^ k * 2 = 2 * (2⁻¹ : ℝ≥0∞) ^ k := by
            rw [mul_comm]
          _ = ENNReal.ofReal 2 * ENNReal.ofReal (1 / 2 : ℝ) ^ k := by
            rw [hhalf]
            norm_num
          _ = ENNReal.ofReal (2 * ((1 / 2 : ℝ) ^ k)) := by
            rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ)),
              ENNReal.ofReal_pow (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  refine ⟨φ, μ, hφmono, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [δ] using hstep
  · intro k
    simpa [δ] using (hμ k).1
  · intro k t
    simpa [δ] using (hμ k).2 t
  · exact lt_of_le_of_lt hsum_le (by norm_num)
  · intro k
    simpa [δ] using htail_le k

end DirectedDistances.Probability
