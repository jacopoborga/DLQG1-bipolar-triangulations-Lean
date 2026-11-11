/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.GeneralPlaneMapOrientedSideTransport
public import DirectedDistances.PlanarMap.GeneralPlaneMapSides

/-! # Side transport for directed plane maps with missing edges

existing `DirectedPlaneMapWithMissing.HomeoEquiv` transports the drawing,
missing tags, and orientations of present edges. Orientation of the plane
homeomorphism is recorded by `OrientationPreserving`. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

variable {V E V' E' : Type*}
variable {M : DirectedPlaneMapWithMissing V E}
variable {M' : DirectedPlaneMapWithMissing V' E'}

/-- The image of a face under a homeomorphism equivalence of directed plane
maps with missing edges. Helper toward Definition 3.2. -/
@[expose] def DirectedPlaneMapWithMissing.HomeoEquiv.faceMap
    (e : DirectedPlaneMapWithMissing.HomeoEquiv M M')
    (F : PlaneGraphDrawing.Face (Drawing M)) :
    PlaneGraphDrawing.Face (Drawing M') :=
  e.drawing.drawing.faceMap F

/-- External-face status is preserved by a homeomorphism equivalence of
directed plane maps with missing edges. Helper toward Definition 3.2. -/
theorem DirectedPlaneMapWithMissing.HomeoEquiv.isExternal_faceMap_iff
    (e : DirectedPlaneMapWithMissing.HomeoEquiv M M')
    (F : PlaneGraphDrawing.Face (Drawing M)) :
    (Drawing M').IsExternal (e.faceMap F) ↔ (Drawing M).IsExternal F := by
  exact e.drawing.drawing.isExternal_faceMap_iff F

/-- A present dart maps to the corresponding present dart. Helper toward
Definition 3.2. -/
@[expose] def DirectedPlaneMapWithMissing.HomeoEquiv.presentEdgeMap
    (e : DirectedPlaneMapWithMissing.HomeoEquiv M M')
    (d : PresentEdge M) : PresentEdge M' :=
  ⟨e.drawing.drawing.σE d.1, by
    simpa [e.drawing.missing_map] using d.2⟩




















end DirectedDistances.PlanarMap

end
