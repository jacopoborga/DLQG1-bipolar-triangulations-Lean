/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-! # Compactness barrier for Appendix A.1

Necessary infrastructure for `lem-holo-asymp`. A local small bound near the
distinguished boundary point extends to the whole compact boundary after
adding a multiple of a weight positive away from that point. This lemma does
not assume a Poisson representation or the paper's radial conclusion. -/

public section
namespace DirectedDistances.Tauberian

open Set Filter
open scoped Topology

/-- Extend a local boundary bound globally on a compact set. The correction
weight vanishes only at the distinguished point. The coefficient may depend
on the local tolerance but is uniform over the whole compact set. -/
theorem exists_global_compact_barrier {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {a : X} (e : X → ℂ) (p q : X → ℝ)
    (he : ContinuousOn e K) (hp : ContinuousOn p K)
    (hp_nonneg : ∀ x ∈ K, 0 ≤ p x)
    (hp_pos : ∀ x ∈ K, x ≠ a → 0 < p x)
    (hq_nonneg : ∀ x ∈ K, 0 ≤ q x) {ε : ℝ} (hε : 0 ≤ ε)
    (hlocal : ∀ᶠ x in 𝓝[K] a, ‖e x‖ ≤ ε * q x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖e x‖ ≤ ε * q x + C * p x := by
  obtain ⟨V, hV, hlocalV⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hlocal
  obtain ⟨U, hUV, hU, haU⟩ := mem_nhds_iff.1 hV
  have hpos : ∀ x ∈ K \ U, 0 < p x := by
    intro x hx
    apply hp_pos x hx.1
    intro hxa
    exact hx.2 (hxa ▸ haU)
  have hquot : ContinuousOn (fun x => ‖e x‖ / p x) (K \ U) :=
    (he.norm.mono diff_subset).div (hp.mono diff_subset) (fun x hx => (hpos x hx).ne')
  obtain ⟨B, hB⟩ := (hK.diff hU).bddAbove_image hquot
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro x hx
  by_cases hxU : x ∈ U
  · have hl := hlocalV ⟨hUV hxU, hx⟩
    exact hl.trans (le_add_of_nonneg_right (mul_nonneg (le_max_right B 0) (hp_nonneg x hx)))
  · have hx' : x ∈ K \ U := ⟨hx, hxU⟩
    have hb : ‖e x‖ / p x ≤ max B 0 :=
      (hB (mem_image_of_mem (fun x => ‖e x‖ / p x) hx')).trans (le_max_left _ _)
    have hm := (div_le_iff₀ (hpos x hx')).1 hb
    have hq := mul_nonneg hε (hq_nonneg x hx)
    linarith only [hm, hq]

end DirectedDistances.Tauberian
