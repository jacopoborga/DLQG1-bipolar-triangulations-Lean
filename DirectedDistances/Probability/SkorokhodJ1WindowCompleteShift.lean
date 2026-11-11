/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodJ1WindowCompleteChainIso

import Mathlib.Analysis.SpecificLimits.Basic

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/

@[expose] public section
namespace DirectedDistances.Probability

open Filter
open scoped ENNReal Topology




theorem j1TimeChangeChain_front {T : ℝ} (μ : ℕ → J1TimeChange T)
    (k n : ℕ) :
    j1TimeChangeChain μ k (n + 1) =
      (μ k).trans (j1TimeChangeChain μ (k + 1) n) := by
  induction n with
  | zero => simp [j1TimeChangeChain]
  | succ n ih =>
      have hidx : k + (n + 1) = (k + 1) + n := by omega
      change (j1TimeChangeChain μ k (n + 1)).trans (μ (k + (n + 1))) =
        (μ k).trans
          ((j1TimeChangeChain μ (k + 1) n).trans (μ ((k + 1) + n)))
      rw [ih, hidx]
      exact OrderIso.trans_assoc (μ k) (j1TimeChangeChain μ (k + 1) n)
        (μ ((k + 1) + n))




theorem chainLimit_front {T : ℝ} (hT : 0 < T)
    (μ : ℕ → J1TimeChange T)
    (hsum : ∑' j, j1TimeChangeSlopeNorm (μ j) < ⊤)
    (k : ℕ) (t : J1Window T) :
    chainLimit hT μ hsum k t =
      chainLimit hT μ hsum (k + 1) (μ k t) := by
  have hsucc : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => by omega⟩
  have hleft : Tendsto
      (fun n => (j1TimeChangeChain μ k (n + 1) t : ℝ)) atTop
      (𝓝 (chainLimit hT μ hsum k t)) :=
    (chain_tendstoUniformly hT μ hsum k).tendsto_at t |>.comp hsucc
  have hpoint (n : ℕ) :
      (j1TimeChangeChain μ k (n + 1) t : ℝ) =
        (j1TimeChangeChain μ (k + 1) n (μ k t) : ℝ) := by
    have h := congrArg (fun φ : J1TimeChange T => (φ t : ℝ))
      (j1TimeChangeChain_front μ k n)
    simpa [OrderIso.trans_apply] using h
  have hleft' : Tendsto
      (fun n => (j1TimeChangeChain μ (k + 1) n (μ k t) : ℝ)) atTop
      (𝓝 (chainLimit hT μ hsum k t)) := by
    simpa only [hpoint] using hleft
  have hright : Tendsto
      (fun n => (j1TimeChangeChain μ (k + 1) n (μ k t) : ℝ)) atTop
      (𝓝 (chainLimit hT μ hsum (k + 1) (μ k t))) :=
    (chain_tendstoUniformly hT μ hsum (k + 1)).tendsto_at (μ k t)
  exact tendsto_nhds_unique hleft' hright




theorem chainTimeChange_succ_eq {T : ℝ} (hT : 0 < T)
    (μ : ℕ → J1TimeChange T)
    (hsum : ∑' j, j1TimeChangeSlopeNorm (μ j) < ⊤)
    (k : ℕ) :
    chainTimeChange hT μ hsum k =
      (μ k).trans (chainTimeChange hT μ hsum (k + 1)) := by
  ext t
  simpa only [chainTimeChange_apply, OrderIso.trans_apply] using
    chainLimit_front hT μ hsum k t




theorem chainTimeChange_symm_succ_eq {T : ℝ} (hT : 0 < T)
    (μ : ℕ → J1TimeChange T)
    (hsum : ∑' j, j1TimeChangeSlopeNorm (μ j) < ⊤)
    (k : ℕ) :
    (chainTimeChange hT μ hsum k).symm =
      (chainTimeChange hT μ hsum (k + 1)).symm.trans (μ k).symm := by
  rw [chainTimeChange_succ_eq]
  exact OrderIso.symm_trans _ _




theorem chainTimeChange_slopeNorm_le_geometric {T : ℝ} (hT : 0 < T)
    (μ : ℕ → J1TimeChange T)
    (hsum : ∑' j, j1TimeChangeSlopeNorm (μ j) < ⊤)
    (hμ : ∀ j, j1TimeChangeSlopeNorm (μ j) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ j))
    (k : ℕ) :
    j1TimeChangeSlopeNorm (chainTimeChange hT μ hsum k) ≤
      ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ k) := by
  let r : ℝ≥0∞ := (1 / 2 : ℝ≥0∞)
  have hdom (j : ℕ) :
      j1TimeChangeSlopeNorm (μ (k + j)) ≤ r ^ (k + j) := by
    calc
      j1TimeChangeSlopeNorm (μ (k + j)) ≤
          ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + j)) := hμ (k + j)
      _ = r ^ (k + j) := by
        simp [r]
        rw [ENNReal.inv_pow]
  have hr : r = (2⁻¹ : ℝ≥0∞) := by norm_num [r]
  have htail : (∑' j, r ^ (k + j)) = r ^ k * 2 := by
    calc
      (∑' j, r ^ (k + j)) = ∑' j, r ^ k * r ^ j :=
        tsum_congr fun j => by rw [pow_add]
      _ = r ^ k * ∑' j, r ^ j := ENNReal.tsum_mul_left
      _ = r ^ k * 2 := by rw [hr, ENNReal.tsum_geometric_two]
  calc
    j1TimeChangeSlopeNorm (chainTimeChange hT μ hsum k) ≤
        ∑' j, j1TimeChangeSlopeNorm (μ (k + j)) :=
      chainTimeChange_slopeNorm_le_tsum hT μ hsum k
    _ ≤ ∑' j, r ^ (k + j) := tsum_le_tsum hdom
    _ = r ^ k * 2 := htail
    _ = ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ k) := by
      simp [r, ENNReal.inv_pow]
      exact mul_comm _ _

end DirectedDistances.Probability
