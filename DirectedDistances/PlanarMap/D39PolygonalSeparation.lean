/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingGeneralCarrier








public section

namespace DirectedDistances.PlanarMap
namespace Polyline

/-- Helper toward Proposition 5.16: the image of a finite polyline is compact,
using its existing continuous path traversal. -/
theorem isCompact_image (p : Polyline) : IsCompact p.image := by
  rw [← p.range_toPath]
  exact isCompact_range p.toPath.continuous

/-- Helper toward Proposition 5.16: two finite polyline images have open
complement. -/
theorem isOpen_compl_image_union (p q : Polyline) :
    IsOpen ((p.image ∪ q.image)ᶜ) := by
  exact (p.isCompact_image.union q.isCompact_image).isClosed.isOpen_compl

/-- Helper toward Proposition 5.16: a finite union of polyline images has
complement points outside every norm ball. This gives only the unbounded
point clause; it does not construct an unbounded complementary component. -/
theorem exists_point_outside_image_union_of_norm_gt (p q : Polyline) (R : ℝ) :
    ∃ z : ℂ, z ∉ p.image ∪ q.image ∧ R < ‖z‖ := by
  have hb : Bornology.IsBounded (p.image ∪ q.image) :=
    (p.isCompact_image.union q.isCompact_image).isBounded
  obtain ⟨r, hr⟩ := hb.subset_closedBall (0 : ℂ)
  let z : ℂ := ((max r 0 + |R| + 2 : ℝ) : ℂ)
  have hz_norm : ‖z‖ = max r 0 + |R| + 2 := by
    dsimp [z]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    positivity
  refine ⟨z, ?_, ?_⟩
  · intro hz
    have hzball : z ∈ Metric.closedBall (0 : ℂ) r := hr hz
    rw [Metric.mem_closedBall, dist_zero_right, hz_norm] at hzball
    have hrle : r ≤ max r 0 := le_max_left r 0
    have hAbs : 0 ≤ |R| := abs_nonneg R
    linarith
  · rw [hz_norm]
    have hR : R ≤ |R| := le_abs_self R
    have hmax : 0 ≤ max r 0 := le_max_right r 0
    linarith

end Polyline
































end DirectedDistances.PlanarMap

end
