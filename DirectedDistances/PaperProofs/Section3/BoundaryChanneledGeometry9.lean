/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry8

/-! All results and remaining targets in this module are conditional on the
outer-face encoding decision: the marked face characterized by
`boundaryChanneledMarkedOuterFace` is assumed unbounded where indicated. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the marked-face hypothesis makes the border
darts of every unbounded face exactly the finite outer-word letters. -/
theorem boundaryChanneled_unboundedFace_outerWord_of_outerUnbounded
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G))
    (U : G.Face) (hU : G.IsUnbounded U) (d : Fin R.dartCount) :
    G.dartBorders d U ↔ d ∈ R.B.outerWord.letters :=
  boundaryChanneled_unboundedFace_borders_iff_outerWord
    R G hOuterUnbounded U hU d

/- The following exact targets were not discharged. In particular, the first
proved bridge above supplies the source-side outer-word characterization, but
does not by itself transfer `dartBorders` to an arbitrary `DrawsMap` drawing.
Three routes were tried:

1. Apply the marked-face characterization and then the four-run/list-index
   argument used in KMSWFiniteBoundaryPresentation12. The latter needs a
   border characterization for the target drawing H, while the available
   characterization is for G.
2. Use `DrawsMap.image_eq` and face correspondence to identify the unbounded
   component, then transfer the border wedge across matching edge traces.
   `DrawsMap` supplies trace-range equality, not the positive-ray equality of
   the oriented initial segments needed by `dartBorders`.
3. Port KMSWFiniteBoundaryPresentation14/16/21/23. Those arguments use
   `StageDrawing`, the stage finite presentation, and a stage-map realization;
   there is no checked identification of the arbitrary R and G here with
   those stage data.

The same missing oriented-arc bridge blocks the two side-orientation clauses.
Successor and finite position order still require generic geometric or
combinatorial transport beyond the checked stage-specific lemmas. Boundary
order still needs a generic finite-frontier correspondence. No premise has
been added to any target.

OPEN (1): dart coverage for every transported drawing:

    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded : G.IsUnbounded (boundaryChanneledMarkedOuterFace R G))
    (rot : Equiv.Perm (G.GeometricEdge × Bool))
    (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial (boundaryChanneledPlaneMap R G))) (U : H.Face)
    (hDraws : DrawsMap (boundaryChanneledPlaneMap R G) H)
    (hU : H.IsUnbounded U) :
    ∀ d, H.dartBorders d U ↔
      ∃ i : InfiniteBoundaryDartIndex
        (boundaryChanneledPresentationWithJunctions R G).presentation,
        InfiniteBoundaryDartIndex.dart
          (boundaryChanneledPresentationWithJunctions R G).presentation i = d

OPEN (2a): upper-left orientation:

    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded : G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    ULOkInf (boundaryChanneledPresentationWithJunctions R G).presentation

OPEN (2b): lower-right orientation:

    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded : G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    LROkInf (boundaryChanneledPresentationWithJunctions R G).presentation

OPEN (3): geometric successor for every transported drawing:

    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded : G.IsUnbounded (boundaryChanneledMarkedOuterFace R G))
    (rot : Equiv.Perm (G.GeometricEdge × Bool))
    (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial (boundaryChanneledPlaneMap R G))) (U : H.Face)
    (hDraws : DrawsMap (boundaryChanneledPlaneMap R G) H)
    (hU : H.IsUnbounded U) :
    IsGeometricExternalFaceSucc H U (fun d => rot.symm (d.1, !d.2))

OPEN (4): finite position order for every transported drawing:

    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded : G.IsUnbounded (boundaryChanneledMarkedOuterFace R G))
    (rot : Equiv.Perm (G.GeometricEdge × Bool))
    (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial (boundaryChanneledPlaneMap R G)))
    (hDraws : DrawsMap (boundaryChanneledPlaneMap R G) H) :
    FiniteBoundaryPositionOrder4
      (boundaryChanneledPresentationWithJunctions R G).presentation
      (fun d => rot.symm (d.1, !d.2))

OPEN (5): boundary order:

    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded : G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    IsBoundaryOrderOfInf (boundaryChanneledPlaneMap R G)
      (boundaryChanneledPresentationWithJunctions R G).presentation

OPEN (6): Geometry2's package with only the marked-face unboundedness
hypothesis:

    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded : G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    let M := boundaryChanneledPlaneMap R G
    ∃ (B : BoundaryPresentationWithJunctions M)
      (rot : Equiv.Perm (G.GeometricEdge × Bool))
      (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
        (fun d => (d.1, !d.2)) rot (boundaryDartInitial M))
      (U : H.Face) (S : G.GeometricEdge × Bool → G.GeometricEdge × Bool),
      B = boundaryChanneledPresentationWithJunctions R G ∧ DrawsMap M H ∧
        IsFiniteExternalFaceIntervalOrder7 M B H U S

No paper-completion claim is made. -/

end DirectedDistances.PaperProofs.Section3

end
end
