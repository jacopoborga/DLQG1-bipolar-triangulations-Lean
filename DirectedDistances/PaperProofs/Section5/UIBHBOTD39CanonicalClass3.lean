/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalClass
public import DirectedDistances.PlanarMap.PlaneStarExtension3

/-! Supporting lemmas for paper labels `def-bs-topology` (see CORRESPONDENCE.md). -/

/-! # Finite-window geometric balls for the canonical UIBHBOT drawing

Helpers toward Definition 3.8 (`def-bs-topology`) and the UIBHBOT construction. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.8: an ordered finite star at the origin can be
matched to another ordered finite star by an orientation-preserving plane
homeomorphism that also matches every radial segment. -/
theorem exists_oriented_plane_star_cone_extension (n : ℕ) (hn : 1 ≤ n)
    (a b : Fin n → ℝ) (ha : StrictMono a) (hb : StrictMono b)
    (ha0 : ∀ j, 0 ≤ a j) (ha2 : ∀ j, a j < 2 * Real.pi)
    (hb0 : ∀ j, 0 ≤ b j) (hb2 : ∀ j, b j < 2 * Real.pi) :
    ∃ (f : ℝ ≃ₜ ℝ) (H : ℂ ≃ₜ ℂ),
      StrictMono f ∧
      (∀ t : ℝ, f (t + 2 * Real.pi) = f t + 2 * Real.pi) ∧
      (∀ j : Fin n, f (a j) = b j) ∧
      H 0 = 0 ∧
      (∀ (r t : ℝ), 0 ≤ r →
        H ((r : ℂ) * (Circle.exp t : ℂ)) =
          (r : ℂ) * (Circle.exp (f t) : ℂ)) ∧
      (∀ z : ℂ, ‖H z‖ = ‖z‖) ∧
      (∀ j : Fin n,
        H '' {z : ℂ | ∃ r : ℝ, 0 ≤ r ∧
          z = (r : ℂ) * (Circle.exp (a j) : ℂ)} =
          {z : ℂ | ∃ r : ℝ, 0 ≤ r ∧
            z = (r : ℂ) * (Circle.exp (b j) : ℂ)}) ∧
      (∀ (j : Fin n) (ρ : ℝ), 0 ≤ ρ →
        H '' segment ℝ (0 : ℂ) ((ρ : ℂ) * (Circle.exp (a j) : ℂ)) =
          segment ℝ (0 : ℂ) ((ρ : ℂ) * (Circle.exp (b j) : ℂ))) ∧
      OrientationPreserving H := by
  obtain ⟨f, h, c, d, hf, hper, hh, hj, hc, hd, hknots, hperiodC,
      hperiodD, haffine⟩ :=
    exists_circle_homeomorph_finite_angles n hn a b ha hb ha0 ha2 hb0 hb2
  refine ⟨f, starConeHomeomorph h, hf, hper, fun j => (hj j).1,
    starConeMap_zero h, starConeHomeomorph_exp f h hh,
    norm_starConeMap h, ?_, ?_,
    orientationPreserving_starConeHomeomorph f hf hper h hh⟩
  · intro j
    rw [starConeHomeomorph_image_ray, (hj j).2]
  · intro j ρ hρ
    rw [starConeHomeomorph_image_segment h _ ρ hρ, (hj j).2]


























end DirectedDistances.PaperProofs.Section5

end

