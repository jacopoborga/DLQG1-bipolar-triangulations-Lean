/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodJ1Window

import Mathlib.Topology.Order.LeftRight

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/

@[expose] public section
namespace DirectedDistances.Probability

open Filter Set
open scoped Topology




theorem j1TimeChange_tendsto_nhdsGE {T : ℝ} (φ : J1TimeChange T)
    (a : J1Window T) :
    Tendsto φ (𝓝[≥] a) (𝓝[≥] (φ a)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨(j1TimeChange_continuous φ).continuousAt.mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_of_forall ?_⟩
  intro x hx
  exact φ.monotone hx




theorem j1TimeChange_tendsto_nhdsLT {T : ℝ} (φ : J1TimeChange T)
    (a : J1Window T) :
    Tendsto φ (𝓝[<] a) (𝓝[<] (φ a)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨(j1TimeChange_continuous φ).continuousAt.mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_of_forall ?_⟩
  intro x hx
  exact φ.strictMono hx




theorem isCadlag_comp_timeChange {T : ℝ} {f : J1Window T → ℝ}
    (hf : IsCadlag f) (φ : J1TimeChange T) : IsCadlag (f ∘ φ) := by
  refine ⟨?_, ?_⟩
  · intro a
    rw [continuousWithinAt_Ioi_iff_Ici]
    have hf' : ContinuousWithinAt f (Ici (φ a)) (φ a) :=
      continuousWithinAt_Ioi_iff_Ici.mp (hf.isRightContinuous (φ a))
    exact hf'.tendsto.comp (j1TimeChange_tendsto_nhdsGE φ a)
  · intro a
    obtain ⟨l, hl⟩ := hf.tendsto_nhdsLT (φ a)
    exact ⟨l, hl.comp (j1TimeChange_tendsto_nhdsLT φ a)⟩




theorem isCadlag_comp_timeChange_symm {T : ℝ} {f : J1Window T → ℝ}
    (hf : IsCadlag f) (φ : J1TimeChange T) : IsCadlag (f ∘ φ.symm) :=
  isCadlag_comp_timeChange hf φ.symm




def CadlagWindow.compTimeChange {T : ℝ} (x : CadlagWindow T)
    (φ : J1TimeChange T) : CadlagWindow T :=
  ⟨fun u => x.1 (φ u), isCadlag_comp_timeChange x.2 φ⟩




@[simp]
theorem CadlagWindow.compTimeChange_apply {T : ℝ} (x : CadlagWindow T)
    (φ : J1TimeChange T) (u : J1Window T) :
    (x.compTimeChange φ).1 u = x.1 (φ u) := rfl

end DirectedDistances.Probability
