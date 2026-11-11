/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallIso11

/-! Helper toward Proposition 5.16. This file isolates the exact composition step
for two straighteners on a common source set and records the remaining local
shrinking and full-star rotation obligations. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16. If two plane homeomorphisms send the same
set to radial segments, their composite sends the first radial segment exactly
to the second. This is the set-theoretic composition step for straighteners
once a common initial arc piece has been identified. -/
theorem d39_composite_straightener_maps_common_radial_segment
    {A : Set ℂ} (H₁ H₂ : ℂ ≃ₜ ℂ) (u v : ℂ)
    (h₁ : H₁ '' A =
      {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = (t : ℂ) * u})
    (h₂ : H₂ '' A =
      {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = (t : ℂ) * v}) :
    (H₁.symm.trans H₂) ''
      {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = (t : ℂ) * u} =
      {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = (t : ℂ) * v} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change H₂ (H₁.symm w) ∈ _
    rw [← h₁] at hw
    rcases hw with ⟨a, ha, rfl⟩
    rw [H₁.symm_apply_apply]
    simpa only [h₂] using
      (show H₂ a ∈ H₂ '' A from ⟨a, ha, rfl⟩)
  · intro hz
    rw [← h₂] at hz
    rcases hz with ⟨a, ha, rfl⟩
    refine ⟨H₁ a, ?_, ?_⟩
    · simpa only [h₁] using
        (show H₁ a ∈ H₁ '' A from ⟨a, ha, rfl⟩)
    · change H₂ (H₁.symm (H₁ a)) = H₂ a
      rw [H₁.symm_apply_apply]

















































































end DirectedDistances.PaperProofs.Section5

end
