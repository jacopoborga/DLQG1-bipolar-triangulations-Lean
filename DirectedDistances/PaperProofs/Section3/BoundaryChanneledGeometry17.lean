/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry16

 

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the marked outer face borders exactly the
darts of the left path and of the reversed right path, with the right-path
darts taken in reversed orientation. -/
theorem boundaryChanneled_markedOuterFace_borders_iff_boundaryPaths
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) (d : Fin R.dartCount) :
    G.dartBorders d (boundaryChanneledMarkedOuterFace R G) ↔
      d ∈ R.B.leftPath.darts ∨
        d ∈ R.B.rightPath.darts.reverse.map R.B.map.toCombinatorialMap.edgeInv := by
  rw [boundaryChanneled_markedOuterFace_borders_iff_outerWord]
  exact boundaryChanneled_mem_outerWord_iff R d

/-- Helper toward Definition 3.2: every left-path dart borders the marked
outer face. -/
theorem boundaryChanneled_leftPath_dartBorders_markedOuterFace
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) (d : Fin R.dartCount)
    (hd : d ∈ R.B.leftPath.darts) :
    G.dartBorders d (boundaryChanneledMarkedOuterFace R G) := by
  exact (boundaryChanneled_markedOuterFace_borders_iff_boundaryPaths R G d).2
    (Or.inl hd)

/-- Helper toward Definition 3.2: every reversed right-path dart borders the
marked outer face. -/
theorem boundaryChanneled_reversedRightPath_dartBorders_markedOuterFace
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) (d : Fin R.dartCount)
    (hd : d ∈ R.B.rightPath.darts.reverse.map R.B.map.toCombinatorialMap.edgeInv) :
    G.dartBorders d (boundaryChanneledMarkedOuterFace R G) := by
  exact (boundaryChanneled_markedOuterFace_borders_iff_boundaryPaths R G d).2
    (Or.inr hd)

/-- Helper toward Definition 3.2: when the marked face is unbounded, every
unbounded face's border darts are exactly the two directed boundary-path runs. -/
theorem boundaryChanneled_unboundedFace_borders_iff_boundaryPaths
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G))
    (U : G.Face) (hU : G.IsUnbounded U) (d : Fin R.dartCount) :
    G.dartBorders d U ↔
      d ∈ R.B.leftPath.darts ∨
        d ∈ R.B.rightPath.darts.reverse.map R.B.map.toCombinatorialMap.edgeInv := by
  rw [boundaryChanneled_unboundedFace_borders_iff_outerWord
    R G hOuterUnbounded U hU d]
  exact boundaryChanneled_mem_outerWord_iff R d



































end DirectedDistances.PaperProofs.Section3

end
