/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry23
public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry22
import DirectedDistances.PaperProofs.Section3.BoundaryChanneledPart2

 

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: every drawing of the same boundary-channelling
map has the finite cyclic position order induced by its geometric rotation. -/
theorem boundaryChanneledPresentation_finitePositionOrder25
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (rot : Equiv.Perm (G.GeometricEdge × Bool))
    (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial (boundaryChanneledPlaneMap R G)))
    (hdraw : DrawsMap (boundaryChanneledPlaneMap R G) H) :
    FiniteBoundaryPositionOrder4
      (boundaryChanneledPresentationWithJunctions R G).presentation
      (fun d => rot.symm (d.1, !d.2)) :=
  boundaryChanneled_drawsMap_finitePositionOrder_part2 R G rot H hdraw

end DirectedDistances.PaperProofs.Section3

end
