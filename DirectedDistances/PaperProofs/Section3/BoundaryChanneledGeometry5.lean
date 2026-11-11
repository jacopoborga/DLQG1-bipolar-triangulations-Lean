/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry3
public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation16

 

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: under the separately proved geometric
identification of the marked outer face with the unbounded face, every dart
of the directed left boundary path borders that unbounded face.

The displayed outer-face identification is an intermediate dependency only;
it is not a premise of the final wrapper target. -/
theorem boundaryChanneled_leftPath_dartBorders_of_outerFaceIdentification
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R)
    (U : G.Face)
    (h_outerFace_identification :
      ∀ d : Fin R.dartCount, G.dartBorders d U ↔ R.B.map.IsOuter d)
    (d : Fin R.dartCount) (hd : d ∈ R.B.leftPath.darts) :
    G.dartBorders d U := by
  apply (h_outerFace_identification d).mpr
  exact (boundaryChanneled_isOuter_iff_mem_boundaryPaths R d).2 (Or.inl hd)

/-- Helper toward Definition 3.2: under the separately proved geometric
identification of the marked outer face with the unbounded face, every dart
in the reversed, oppositely oriented right boundary path borders that face.

The displayed outer-face identification is an intermediate dependency only;
it is not a premise of the final wrapper target. -/
theorem boundaryChanneled_reversedRightPath_dartBorders_of_outerFaceIdentification
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R)
    (U : G.Face)
    (h_outerFace_identification :
      ∀ d : Fin R.dartCount, G.dartBorders d U ↔ R.B.map.IsOuter d)
    (d : Fin R.dartCount)
    (hd : d ∈ R.B.rightPath.darts.reverse.map
      R.B.map.toCombinatorialMap.edgeInv) :
    G.dartBorders d U := by
  apply (h_outerFace_identification d).mpr
  exact (boundaryChanneled_isOuter_iff_mem_boundaryPaths R d).2 (Or.inr hd)





































































































































end DirectedDistances.PaperProofs.Section3

end
