/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry2
public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry3
public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry4
public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry5
public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry6
public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry7

/-! The results in this file are conditional on the outer-face encoding decision:
the marked face from `boundaryChanneled_existsUnique_markedOuterFace` must be
unbounded. This condition is kept explicit and is not inferred from an
arbitrary drawing representation. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the face uniquely bordering the marked
combinatorial outer cycle in Geometry4. -/
noncomputable def boundaryChanneledMarkedOuterFace
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) : G.Face :=
  Classical.choose (boundaryChanneled_existsUnique_markedOuterFace R G).exists

/-- Helper toward Definition 3.2: the Geometry4 marked face has exactly the
border darts of the combinatorial outer face. -/
theorem boundaryChanneled_markedOuterFace_borders_iff
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) (d : Fin R.dartCount) :
    G.dartBorders d (boundaryChanneledMarkedOuterFace R G) ↔ R.B.map.IsOuter d := by
  exact Classical.choose_spec
    (boundaryChanneled_existsUnique_markedOuterFace R G).exists d

/-- Helper toward Definition 3.2: if the Geometry4 marked face is
unbounded, it is the unique unbounded face of the drawing. -/
theorem boundaryChanneled_unboundedFace_eq_markedOuterFace
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G))
    (U : G.Face) (hU : G.IsUnbounded U) :
    U = boundaryChanneledMarkedOuterFace R G := by
  exact boundaryChanneled_unbounded_faces_eq R G U
    (boundaryChanneledMarkedOuterFace R G) hU hOuterUnbounded

/-- Helper toward Definition 3.2: every left-path dart borders any unbounded
face when the marked face is unbounded. -/
theorem boundaryChanneled_leftPath_dartBorders_of_outerUnbounded
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G))
    (U : G.Face) (hU : G.IsUnbounded U)
    (d : Fin R.dartCount) (hd : d ∈ R.B.leftPath.darts) :
    G.dartBorders d U := by
  rw [boundaryChanneled_unboundedFace_eq_markedOuterFace R G
    hOuterUnbounded U hU]
  exact boundaryChanneled_leftPath_dartBorders_of_outerFaceIdentification
    R G (boundaryChanneledMarkedOuterFace R G)
    (fun e => boundaryChanneled_markedOuterFace_borders_iff R G e) d hd

/-- Helper toward Definition 3.2: every reversed right-path dart borders any
unbounded face when the marked face is unbounded. -/
theorem boundaryChanneled_reversedRightPath_dartBorders_of_outerUnbounded
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G))
    (U : G.Face) (hU : G.IsUnbounded U)
    (d : Fin R.dartCount)
    (hd : d ∈ R.B.rightPath.darts.reverse.map
      R.B.map.toCombinatorialMap.edgeInv) :
    G.dartBorders d U := by
  rw [boundaryChanneled_unboundedFace_eq_markedOuterFace R G
    hOuterUnbounded U hU]
  exact boundaryChanneled_reversedRightPath_dartBorders_of_outerFaceIdentification
    R G (boundaryChanneledMarkedOuterFace R G)
    (fun e => boundaryChanneled_markedOuterFace_borders_iff R G e) d hd

/-- Helper toward Definition 3.2: the marked face's border darts are exactly
the letters of the finite outer word. -/
theorem boundaryChanneled_markedOuterFace_borders_iff_outerWord
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) (d : Fin R.dartCount) :
    G.dartBorders d (boundaryChanneledMarkedOuterFace R G) ↔
      d ∈ R.B.outerWord.letters := by
  rw [boundaryChanneled_markedOuterFace_borders_iff]
  exact (mem_iff_isOuter R.B.map R.B.outerWord R.B.outerSplit.1 d).symm

/-- Helper toward Definition 3.2: any unbounded face borders exactly the
darts of the finite outer word, assuming the marked face is unbounded. -/
theorem boundaryChanneled_unboundedFace_borders_iff_outerWord
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G))
    (U : G.Face) (hU : G.IsUnbounded U) (d : Fin R.dartCount) :
    G.dartBorders d U ↔ d ∈ R.B.outerWord.letters := by
  rw [boundaryChanneled_unboundedFace_eq_markedOuterFace R G
    hOuterUnbounded U hU]
  exact boundaryChanneled_markedOuterFace_borders_iff_outerWord R G d








































































































end DirectedDistances.PaperProofs.Section3

end
end
