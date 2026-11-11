/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodJ1WindowCompleteChain
public import DirectedDistances.Probability.SkorokhodJ1WindowCompleteLimit
public import DirectedDistances.Probability.SkorokhodJ1WindowCompleteLemmas

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Order.IntermediateValue

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/

@[expose] public section
namespace DirectedDistances.Probability

open Filter
open scoped ENNReal Topology




theorem chainLimit_mem_window {T : ℝ} (hT : 0 < T)
    (μ : ℕ → J1TimeChange T)
    (hsum : ∑' j, j1TimeChangeSlopeNorm (μ j) < ⊤)
    (k : ℕ) (t : J1Window T) :
    0 ≤ chainLimit hT μ hsum k t ∧ chainLimit hT μ hsum k t ≤ T := by
  let z : J1Window T := ⟨0, ⟨le_rfl, hT.le⟩⟩
  let b : J1Window T := ⟨T, ⟨hT.le, le_rfl⟩⟩
  have hend := chainLimit_endpoints hT μ hsum k
  have hmono := (chainLimit_strictMono hT μ hsum k).monotone
  have hz : z ≤ t := t.property.1
  have ht : t ≤ b := t.property.2
  constructor
  · rw [← hend.1]
    exact hmono hz
  · calc
      chainLimit hT μ hsum k t ≤ chainLimit hT μ hsum k b := hmono ht
      _ = T := hend.2




theorem chainLimit_continuous {T : ℝ} (hT : 0 < T)
    (μ : ℕ → J1TimeChange T)
    (hsum : ∑' j, j1TimeChangeSlopeNorm (μ j) < ⊤)
    (k : ℕ) : Continuous (chainLimit hT μ hsum k) := by
  exact (chain_tendstoUniformly hT μ hsum k).continuous
    (Filter.Frequently.of_forall fun n =>
      continuous_subtype_val.comp (j1TimeChangeChain μ k n).continuous)




noncomputable def chainTimeChange {T : ℝ} (hT : 0 < T)
    (μ : ℕ → J1TimeChange T)
    (hsum : ∑' j, j1TimeChangeSlopeNorm (μ j) < ⊤)
    (k : ℕ) : J1TimeChange T := by
  let z : J1Window T := ⟨0, ⟨le_rfl, hT.le⟩⟩
  let b : J1Window T := ⟨T, ⟨hT.le, le_rfl⟩⟩
  let clip : ℝ → J1Window T := fun x =>
    ⟨max 0 (min x T), ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩⟩
  have hclip_cont : Continuous clip := by
    change Continuous (fun x : ℝ =>
      (⟨max 0 (min x T), ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩⟩ :
        J1Window T))
    exact ((continuous_max.comp (continuous_const.prodMk
      (continuous_min.comp (continuous_id.prodMk continuous_const)))).subtype_mk
        fun x => ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩)
  have hclip_zero : clip 0 = z := by
    apply Subtype.ext
    simp [clip, z, hT.le]
  have hclip_top : clip T = b := by
    apply Subtype.ext
    simp [clip, b, hT.le]
  let g : ℝ → ℝ := fun x => chainLimit hT μ hsum k (clip x)
  have hg_cont : Continuous g :=
    (chainLimit_continuous hT μ hsum k).comp hclip_cont
  have hend := chainLimit_endpoints hT μ hsum k
  have hg_zero : g 0 = 0 := by
    change chainLimit hT μ hsum k (clip 0) = 0
    rw [hclip_zero]
    exact hend.1
  have hg_top : g T = T := by
    change chainLimit hT μ hsum k (clip T) = T
    rw [hclip_top]
    exact hend.2
  have hIVT : Set.Icc (g 0) (g T) ⊆ g '' Set.Icc (0 : ℝ) T :=
    intermediate_value_Icc hT.le hg_cont.continuousOn
  let f : J1Window T → J1Window T := fun t =>
    ⟨chainLimit hT μ hsum k t, chainLimit_mem_window hT μ hsum k t⟩
  have hf : StrictMono f := by
    intro s t hst
    change chainLimit hT μ hsum k s < chainLimit hT μ hsum k t
    exact chainLimit_strictMono hT μ hsum k hst
  have hsurj : Function.Surjective f := by
    intro y
    have hymem : (y : ℝ) ∈ Set.Icc (g 0) (g T) := by
      rw [hg_zero, hg_top]
      exact y.property
    obtain ⟨x, hx, hxy⟩ := hIVT hymem
    let t : J1Window T := ⟨x, hx⟩
    have hclipx : clip x = t := by
      apply Subtype.ext
      simp [clip, t, hx.1, hx.2]
    refine ⟨t, ?_⟩
    apply Subtype.ext
    change chainLimit hT μ hsum k t = (y : ℝ)
    rw [← hclipx]
    exact hxy
  exact StrictMono.orderIsoOfSurjective f hf hsurj




theorem chainTimeChange_apply {T : ℝ} (hT : 0 < T)
    (μ : ℕ → J1TimeChange T)
    (hsum : ∑' j, j1TimeChangeSlopeNorm (μ j) < ⊤)
    (k : ℕ) (t : J1Window T) :
    (chainTimeChange hT μ hsum k t : ℝ) = chainLimit hT μ hsum k t := rfl

private theorem chainLimit_slopeNorm_le_tail {T : ℝ}
    (μ : ℕ → J1TimeChange T) (k n : ℕ) :
    j1TimeChangeSlopeNorm (j1TimeChangeChain μ k n) ≤
      ∑' i, j1TimeChangeSlopeNorm (μ (k + i)) := by
  calc
    j1TimeChangeSlopeNorm (j1TimeChangeChain μ k n) ≤
        ∑ i ∈ Finset.range n, j1TimeChangeSlopeNorm (μ (k + i)) :=
      j1TimeChangeChain_slopeNorm_le_sum μ k n
    _ ≤ ∑' i, j1TimeChangeSlopeNorm (μ (k + i)) :=
      CompleteLattice.summable.sum_le_tsum (f := fun i =>
        j1TimeChangeSlopeNorm (μ (k + i))) (Finset.range n) (fun _ _ => zero_le)




theorem chainTimeChange_slopeNorm_le_tsum {T : ℝ} (hT : 0 < T)
    (μ : ℕ → J1TimeChange T)
    (hsum : ∑' j, j1TimeChangeSlopeNorm (μ j) < ⊤)
    (k : ℕ) :
    j1TimeChangeSlopeNorm (chainTimeChange hT μ hsum k) ≤
      ∑' j, j1TimeChangeSlopeNorm (μ (k + j)) := by
  apply j1TimeChangeSlopeNorm_le_of_tendsto
    (φ := fun n => j1TimeChangeChain μ k n)
    (ψ := chainTimeChange hT μ hsum k)
    (a := ∑' j, j1TimeChangeSlopeNorm (μ (k + j)))
  · intro t
    rw [chainTimeChange_apply hT μ hsum k t]
    exact (chain_tendstoUniformly hT μ hsum k).tendsto_at t
  · exact chainLimit_slopeNorm_le_tail μ k

end DirectedDistances.Probability
