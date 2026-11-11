/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry17

/-! The source drawing's unbounded-face border characterization and the
presentation index-range characterization are available from Geometry17 and
Geometry16. The first remaining transport obligation is recorded below with
its full binders. The transported drawing currently exposes equality of each
arc only up to reversal; it does not expose the dartwise orientation identity
needed to identify its initial wedge with the corresponding presentation
index. No additional geometric premise is introduced. -/

/- OPEN transported-drawing dart coverage (full binders):

    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    ∃ (rot : Equiv.Perm (G.GeometricEdge × Bool))
      (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
        (fun d => (d.1, !d.2)) rot
        (boundaryDartInitial (boundaryChanneledPlaneMap R G))),
      DrawsMap (boundaryChanneledPlaneMap R G) H ∧
      ∀ U : H.Face, H.IsUnbounded U →
        ∀ d, H.dartBorders d U ↔
          ∃ i : InfiniteBoundaryDartIndex
            (boundaryChanneledPresentationWithJunctions R G).presentation,
            InfiniteBoundaryDartIndex.dart
              (boundaryChanneledPresentationWithJunctions R G).presentation i = d

Routes assessed:
1. Transfer `G.dartBorders` through the geometric-edge dart equivalence and
   use the proved unbounded-face component equality. The remaining identity is
   which orientation of each geometric edge the transported drawing assigns
   to its initial wedge, followed by the identification with the indexed path
   dart.
2. Use `DrawsMap.image_eq` and uniqueness of the unbounded component. This
   proves face-set equality, but image equality does not determine local dart
   incidence or its orientation.
3. Use Geometry8's outer-word characterization and split the word into the
   left and reversed-right boundary runs. Geometry16 identifies the two
   presentation index families, but the exact oriented dart transport from
   the chosen drawing to those indexed darts is still required.

Only `hOuterUnbounded` is used as a geometric premise. The UL/LR orientation
clauses and the package variant remain downstream of this coverage statement
and are not claimed here. -/

