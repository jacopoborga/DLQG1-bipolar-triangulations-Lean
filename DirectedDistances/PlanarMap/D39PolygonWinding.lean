/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PolygonParity
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg







public section

noncomputable section

namespace DirectedDistances.PlanarMap
namespace Polyline

/-- Helper toward Proposition 5.16: the principal signed angle from the ray
`p.point i - z` to the next ray `p.point (i + 1) - z`. -/
def signedEdgeAngle (p : Polyline) (z : ℂ) (i : ℕ) : ℝ :=
  Complex.arg ((p.point (i + 1) - z) / (p.point i - z))




def windingAngleSum (p : Polyline) (z : ℂ) : ℝ :=
  (∑ i ∈ Finset.range (p.points.length - 1), p.signedEdgeAngle z i) /
    (2 * Real.pi)

/-- Helper toward Proposition 5.16: a known logarithmic winding integer of a
closed polyline persists for every sufficiently nearby point off its image. -/
theorem hasWinding_stable_nearby_of_closed (p : Polyline)
    (hclosed : p.start = p.finish) (w : ℂ) (n : ℤ)
    (hw : w ∉ p.image)
    (hwind : HasWinding (p.toPath.cast rfl hclosed) w n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w' : ℂ, dist w' w < ε →
      HasWinding (p.toPath.cast rfl hclosed) w' n := by
  let L : Path p.start p.start := p.toPath.cast rfl hclosed
  have havoid : ∀ t : unitInterval, L t ≠ w := by
    intro t ht
    apply hw
    rw [← p.range_toPath]
    refine ⟨t, ?_⟩
    simpa [L] using ht
  simpa [L] using hasWinding_stable_nearby L w n havoid hwind

/-- Helper toward Proposition 5.16: wherever a logarithmic winding integer
of a closed polyline exists, that integer is locally constant on the polygonal
complement. -/
theorem hasWinding_value_eq_of_nearby_of_closed (p : Polyline)
    (hclosed : p.start = p.finish) (w : ℂ) (n : ℤ)
    (hw : w ∉ p.image)
    (hwind : HasWinding (p.toPath.cast rfl hclosed) w n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w' : ℂ, dist w' w < ε →
      ∀ m : ℤ, HasWinding (p.toPath.cast rfl hclosed) w' m → m = n := by
  obtain ⟨ε, hε, hstable⟩ :=
    hasWinding_stable_nearby_of_closed p hclosed w n hw hwind
  refine ⟨ε, hε, ?_⟩
  intro w' hnear m hm
  exact hasWinding_unique hm (hstable w' hnear)






















































end Polyline
end DirectedDistances.PlanarMap

end
