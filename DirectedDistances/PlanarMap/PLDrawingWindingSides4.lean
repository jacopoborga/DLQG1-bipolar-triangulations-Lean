/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingWindingSides3
import DirectedDistances.PlanarMap.GeneralPlaneMapOrientedSideTransport

/-! # Straight-segment winding-side helpers for PL drawings -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

/-- Helper toward Definition 3.2: a path affine on a parameter interval
has the expected affine formula on its paused edge subarc. -/
theorem edgeSubarc_affine_apply {x y : ℂ} (γ : Path x y) {a b : I}
    (hab : a < b)
    (hline : ∀ u : I, a ≤ u → u ≤ b →
      γ u = γ a +
        (((((u : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)) : ℝ) : ℂ) *
          (γ b - γ a)))
    (t : I) :
    edgeSubarc γ a b (le_of_lt hab) t =
      γ a +
        (((((min (max t a) b : I) : ℝ) - (a : ℝ)) /
          ((b : ℝ) - (a : ℝ)) : ℝ) : ℂ) * (γ b - γ a) := by
  rw [edgeSubarc_apply_clamp]
  let c : I := min (max t a) b
  have hac : a ≤ c := le_min (le_max_right _ _) (le_of_lt hab)
  have hcb : c ≤ b := min_le_right _ _
  change γ c = _
  exact hline c hac hcb

/-- Helper toward Definition 3.2: on a straight path segment, the paused
subarc evaluates along that segment at the parameter clamped to its selected
interval. -/
theorem edgeSubarc_segment_apply {x y : ℂ} {a b : I} (hab : a < b)
    (t : I) :
    edgeSubarc (Path.segment x y) a b (le_of_lt hab) t =
      Path.segment x y (min (max t a) b) := by
  exact edgeSubarc_apply_clamp (Path.segment x y) a b (le_of_lt hab) t












































end DirectedDistances.PlanarMap

end
