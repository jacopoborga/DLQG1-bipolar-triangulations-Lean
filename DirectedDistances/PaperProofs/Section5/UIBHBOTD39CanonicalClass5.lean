/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalClass4
public import DirectedDistances.PaperProofs.SourceResults.D39GeometricSourceProviderV2

/-! Helper toward Definition 3.8: local edge data for a finite ordered star. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open unitInterval

/-- Helper toward Definition 3.8: the orientation-preserving extension for
two ordered stars maps each radial edge with the same interval parameter.
This gives the pointwise edge-skeleton compatibility needed before extending
across several vertices and the retained faces of a ball. -/
theorem exists_oriented_root_star_edge_parameterization
    (n : ℕ) (hn : 1 ≤ n)
    (a b : Fin n → ℝ) (ha : StrictMono a) (hb : StrictMono b)
    (ha0 : ∀ j, 0 ≤ a j) (ha2 : ∀ j, a j < 2 * Real.pi)
    (hb0 : ∀ j, 0 ≤ b j) (hb2 : ∀ j, b j < 2 * Real.pi) :
    ∃ H : ℂ ≃ₜ ℂ,
      OrientationPreserving H ∧ H 0 = 0 ∧
        ∀ (j : Fin n) (ρ : ℝ) (s : I), 0 ≤ ρ →
          H (((ρ * (s : ℝ) : ℝ) : ℂ) * (Circle.exp (a j) : ℂ)) =
            (((ρ * (s : ℝ) : ℝ) : ℂ) * (Circle.exp (b j) : ℂ)) := by
  rcases exists_oriented_plane_star_cone_extension n hn a b ha hb ha0 ha2 hb0 hb2 with
    ⟨f, H, hf, hperiod, hangle, hzero, hradial, hnorm, hrays,
      hsegments, horient⟩
  refine ⟨H, horient, hzero, ?_⟩
  intro j ρ s hρ
  have hs : 0 ≤ ρ * (s : ℝ) := mul_nonneg hρ s.property.1
  simpa only [hangle j] using hradial (ρ * (s : ℝ)) (a j) hs
























































end DirectedDistances.PaperProofs.Section5

end
