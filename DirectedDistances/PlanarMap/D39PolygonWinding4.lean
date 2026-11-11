/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PolygonWinding3
public import DirectedDistances.PlanarMap.D39WindingExistence

/-! # Logarithmic winding and polygonal angle sums

Helpers toward Proposition 5.16. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap
namespace Polyline

open unitInterval
open scoped Topology

/-- Helper toward Proposition 5.16: a closed polyline's logarithmic winding
vanishes outside a disk containing its image. This is the winding-side
vanishing statement needed before identifying winding with `angleSum`. -/
theorem exists_radius_hasWinding_zero (p : Polyline)
    (hclosed : p.start = p.finish) :
    ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ →
      HasWinding (p.toPath.cast rfl hclosed) z 0 := by
  obtain ⟨R, hR⟩ := p.isCompact_image.isBounded.subset_closedBall (0 : ℂ)
  let L : Path p.start p.start := p.toPath.cast rfl hclosed
  refine ⟨max R 0, ?_⟩
  intro z hz
  have hbound : ∀ t : unitInterval, ‖L t‖ ≤ max R 0 := by
    intro t
    have ht : p.toPath t ∈ p.image := by
      rw [← p.range_toPath]
      exact ⟨t, rfl⟩
    have hball : p.toPath t ∈ Metric.closedBall (0 : ℂ) R := hR ht
    have hnorm : ‖p.toPath t‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hball
    simpa [L] using hnorm.trans (le_max_left R 0)
  have hRnonneg : 0 ≤ max R 0 := le_max_right R 0
  exact hasWinding_zero_of_norm_bound L hRnonneg hbound hz




























































end Polyline
end DirectedDistances.PlanarMap

end
