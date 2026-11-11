/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry14

 

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: for a drawing of the boundary-channeled
plane map, an unbounded face is the same component as the marked outer face
of the original drawing, provided that marked face is unbounded. -/
theorem boundaryChanneled_transport_unboundedFace_eq_marked
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G))
    (rot : Equiv.Perm (G.GeometricEdge × Bool))
    (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial (boundaryChanneledPlaneMap R G)))
    (hDraws : DrawsMap (boundaryChanneledPlaneMap R G) H)
    (U : H.Face) (hU : H.IsUnbounded U) :
    U.val = (boundaryChanneledMarkedOuterFace R G).val := by
  let M := boundaryChanneledPlaneMap R G
  have himage : H.image = G.image := by
    calc
      H.image = M.toPlaneMapWithMissing.toPlaneGraphDrawing.image := hDraws.image_eq
      _ = G.image := by
        exact G.toPlaneGraphDrawing_image
  obtain ⟨z, hz, hcomponent⟩ := U.property
  have hzG : z ∉ G.image := by
    rw [← himage]
    exact hz
  have hcomponentG : U.val = connectedComponentIn G.imageᶜ z := by
    simpa only [himage] using hcomponent
  let V : G.Face := ⟨U.val, z, hzG, hcomponentG⟩
  have hV : G.IsUnbounded V := by
    exact hU
  have hVM : V = boundaryChanneledMarkedOuterFace R G :=
    boundaryChanneled_unboundedFace_eq_markedOuterFace R G hOuterUnbounded V hV
  calc
    U.val = V.val := rfl
    _ = (boundaryChanneledMarkedOuterFace R G).val := congrArg Subtype.val hVM

/- OPEN next target (dart coverage for the specific transported drawing):

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

Routes tried:
1. Transfer `G.dartBorders` through the geometric-edge dart equivalence and
   use `boundaryChanneled_transport_unboundedFace_eq_marked` for the face
   component. The remaining obligation is to identify the exact orientation
   selected by each transported dart so that its initial wedge agrees, then
   identify the source outer-word darts with the presentation index image.
2. Use `DrawsMap.image_eq` and uniqueness of the unbounded component. The
   component equality is proved above; image equality alone does not imply
   equality of the transported dart's initial wedge or its indexed boundary
   incidence.
3. Use Geometry8's outer-word characterization and split the finite word
   into the left and reversed-right boundary runs. This reduces source border
   membership to the combinatorial partition, but still requires the exact
   dart-orientation transport and a proof that the presentation indices cover
   exactly those transported darts.

No extra geometric premise is introduced. No paper-completion claim is made. -/

end DirectedDistances.PaperProofs.Section3

end
