/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodJ1WindowCompleteLemmas
public import DirectedDistances.Probability.SkorokhodJ1WindowDCirc

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/

@[expose] public section
namespace DirectedDistances.Probability

open Filter
open scoped ENNReal Topology




theorem j1TimeChangeSlopeNorm_le_of_tendsto {T : ℝ}
    (φ : ℕ → J1TimeChange T) (ψ : J1TimeChange T)
    (hlim : ∀ t, Tendsto (fun k => (φ k t : ℝ)) atTop (𝓝 (ψ t : ℝ)))
    (a : ℝ≥0∞) (ha : ∀ k, j1TimeChangeSlopeNorm (φ k) ≤ a) :
    j1TimeChangeSlopeNorm ψ ≤ a := by
  apply iSup_le
  intro p
  let x : ℝ := (p.1.1 : ℝ)
  let y : ℝ := (p.1.2 : ℝ)
  let d : ℝ := y - x
  have hd : d ≠ 0 := by
    dsimp [d, x, y]
    exact ne_of_gt (sub_pos.mpr p.2)
  have hnum : Tendsto
      (fun k => (φ k p.1.2 : ℝ) - (φ k p.1.1 : ℝ)) atTop
      (𝓝 ((ψ p.1.2 : ℝ) - (ψ p.1.1 : ℝ))) :=
    (hlim p.1.2).sub (hlim p.1.1)
  have hquot : Tendsto
      (fun k => ((φ k p.1.2 : ℝ) - (φ k p.1.1 : ℝ)) / d) atTop
      (𝓝 (((ψ p.1.2 : ℝ) - (ψ p.1.1 : ℝ)) / d)) := by
    exact ((continuous_id.div_const d).continuousAt.tendsto).comp hnum
  have hpos : 0 < ((ψ p.1.2 : ℝ) - (ψ p.1.1 : ℝ)) / d := by
    apply div_pos
    · have hmono : ψ p.1.1 < ψ p.1.2 := ψ.strictMono p.2
      have hmonoR : (ψ p.1.1 : ℝ) < (ψ p.1.2 : ℝ) := by
        exact_mod_cast hmono
      exact sub_pos.mpr hmonoR
    · exact sub_pos.mpr p.2
  have hlog : Tendsto
      (fun k => Real.log (((φ k p.1.2 : ℝ) - (φ k p.1.1 : ℝ)) / d)) atTop
      (𝓝 (Real.log (((ψ p.1.2 : ℝ) - (ψ p.1.1 : ℝ)) / d))) :=
    (Real.continuousAt_log (ne_of_gt hpos)).tendsto.comp hquot
  have habs : Tendsto
      (fun k => |Real.log (((φ k p.1.2 : ℝ) - (φ k p.1.1 : ℝ)) / d)|) atTop
      (𝓝 |Real.log (((ψ p.1.2 : ℝ) - (ψ p.1.1 : ℝ)) / d)|) := hlog.abs
  have hterm : Tendsto
      (fun k => ENNReal.ofReal
        |Real.log (((φ k p.1.2 : ℝ) - (φ k p.1.1 : ℝ)) / d)|) atTop
      (𝓝 (ENNReal.ofReal
        |Real.log (((ψ p.1.2 : ℝ) - (ψ p.1.1 : ℝ)) / d)|)) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp habs
  have hbound : ∀ k, ENNReal.ofReal
      |Real.log (((φ k p.1.2 : ℝ) - (φ k p.1.1 : ℝ)) / d)| ≤ a := by
    intro k
    have hle : ENNReal.ofReal |j1ChordLogSlope (φ k) p| ≤
        j1TimeChangeSlopeNorm (φ k) := by
      exact le_iSup_of_le p le_rfl
    have heq : j1ChordLogSlope (φ k) p =
        Real.log (((φ k p.1.2 : ℝ) - (φ k p.1.1 : ℝ)) / d) := by
      simp [j1ChordLogSlope, x, y, d]
    rw [heq] at hle
    exact hle.trans (ha k)
  have hlimle : ENNReal.ofReal
      |Real.log (((ψ p.1.2 : ℝ) - (ψ p.1.1 : ℝ)) / d)| ≤ a :=
    le_of_tendsto hterm (Filter.Eventually.of_forall hbound)
  have heq : j1ChordLogSlope ψ p =
      Real.log (((ψ p.1.2 : ℝ) - (ψ p.1.1 : ℝ)) / d) := by
    simp [j1ChordLogSlope, x, y, d]
  rw [heq]
  exact hlimle




noncomputable def j1TimeChangeChain {T : ℝ} (μ : ℕ → J1TimeChange T)
    (k n : ℕ) : J1TimeChange T :=
  match n with
  | 0 => OrderIso.refl _
  | n + 1 => (j1TimeChangeChain μ k n).trans (μ (k + n))




theorem j1TimeChangeChain_slopeNorm_le_sum {T : ℝ}
    (μ : ℕ → J1TimeChange T) (k n : ℕ) :
    j1TimeChangeSlopeNorm (j1TimeChangeChain μ k n) ≤
      ∑ i ∈ Finset.range n, j1TimeChangeSlopeNorm (μ (k + i)) := by
  induction n with
  | zero => simp [j1TimeChangeChain, j1TimeChangeSlopeNorm_refl]
  | succ n ih =>
      rw [j1TimeChangeChain, Finset.sum_range_succ]
      exact (j1TimeChangeSlopeNorm_trans_le _ _).trans
        (add_le_add ih le_rfl)

private theorem j1TimeChangeChain_append {T : ℝ}
    (μ : ℕ → J1TimeChange T) (k n r : ℕ) :
    j1TimeChangeChain μ k (n + r) =
      (j1TimeChangeChain μ k n).trans (j1TimeChangeChain μ (k + n) r) := by
  induction r with
  | zero => simp [j1TimeChangeChain]
  | succ r ih =>
      change (j1TimeChangeChain μ k (n + r)).trans (μ (k + (n + r))) =
        (j1TimeChangeChain μ k n).trans
          ((j1TimeChangeChain μ (k + n) r).trans (μ ((k + n) + r)))
      rw [ih, Nat.add_assoc]
      exact OrderIso.trans_assoc _ _ _

end DirectedDistances.Probability
