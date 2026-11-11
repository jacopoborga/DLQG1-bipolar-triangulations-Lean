/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingWindingSides7

/-! # Winding sides on paused PL segments

Helpers toward Definition 3.2. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

namespace Polyline

/-- Helper toward Definition 3.2: a parameter strictly inside one dyadic
segment maps to the open geometric segment between its vertices. -/
theorem toPath_mem_openSegment_of_parameter (p : Polyline) {i : ℕ}
    (hi : i + 1 < p.points.length) (t : I)
    (hstart : segmentParameterStart i < (t : ℝ))
    (hend : (t : ℝ) < segmentParameterEnd p.points.length i) :
    p.toPath t ∈ openSegment ℝ (p.point i) (p.point (i + 1)) := by
  let u := ((t : ℝ) - segmentParameterStart i) /
    (segmentParameterEnd p.points.length i - segmentParameterStart i)
  have hden : 0 < segmentParameterEnd p.points.length i -
      segmentParameterStart i :=
    sub_pos.mpr (segmentParameterStart_lt_end p.points.length i)
  have hu0 : 0 < u := by
    dsimp [u]
    exact div_pos (sub_pos.mpr hstart) hden
  have hu1 : u < 1 := by
    apply (div_lt_one hden).2
    linarith
  rw [openSegment_eq_image_lineMap]
  refine ⟨u, ⟨hu0, hu1⟩, ?_⟩
  rw [AffineMap.lineMap_apply_module]
  rw [Complex.real_smul, Complex.real_smul]
  rw [toPath_segment_affine_apply p hi t hstart.le hend.le]
  dsimp [u]
  push_cast
  ring

end Polyline

namespace PLDrawing















end PLDrawing

end DirectedDistances.PlanarMap

end
