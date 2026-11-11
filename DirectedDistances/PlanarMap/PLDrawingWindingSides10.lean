/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingWindingSides9






public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

namespace PLDrawing

/-- Helper toward Definition 3.2: a bordering face touches the left side
at every parameter strictly inside one segment of the PL arc. -/
theorem dartBorders_toPath_leftAtOn_of_strictSegment
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (s : {t : I // t ∈ openParams}) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length)
    (hstart : Polyline.segmentParameterStart i < (s.1 : ℝ))
    (hend : (s.1 : ℝ) < Polyline.segmentParameterEnd (P.arc d).points.length i) :
    LeftAtOn F.val (P.arc d).toPath s := by
  exact P.dartBorders_toPath_leftAtOn_of_parameter_in_segment
    hvert d F hborder s hi hstart hend
















end PLDrawing

end DirectedDistances.PlanarMap

end
