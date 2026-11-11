/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry9
public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation16

/-! Every boundary-channeled conclusion in this module is conditional on the
encoding condition that the marked combinatorial outer face of the chosen
finite drawing is unbounded. This condition identifies the marked face as the
unique unbounded face; it does not identify dart borders in a second drawing
from equality of edge-trace ranges alone. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: `DrawsMap` transfers the full image of a
boundary-channeled drawing to the geometric-edge dart drawing. -/
theorem boundaryChanneled_drawsMap_image_eq
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (rot : Equiv.Perm (G.GeometricEdge × Bool))
    (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
      (fun d => (d.1, !d.2)) rot (boundaryDartInitial (boundaryChanneledPlaneMap R G)))
    (hDraws : DrawsMap (boundaryChanneledPlaneMap R G) H) :
    H.image = (boundaryChanneledPlaneMap R G).toPlaneMapWithMissing.toPlaneGraphDrawing.image :=
  hDraws.image_eq

/-- Helper toward Definition 3.2: an unbounded face in the transported
drawing gives an external face of the corresponding plane-map drawing. -/
theorem boundaryChanneled_drawsMap_externalFace
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (rot : Equiv.Perm (G.GeometricEdge × Bool))
    (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
      (fun d => (d.1, !d.2)) rot (boundaryDartInitial (boundaryChanneledPlaneMap R G)))
    (U : H.Face)
    (hDraws : DrawsMap (boundaryChanneledPlaneMap R G) H)
    (hU : H.IsUnbounded U) :
    ∃ F : (boundaryChanneledPlaneMap R G).toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
      F.val = U.val ∧
        (boundaryChanneledPlaneMap R G).toPlaneMapWithMissing.toPlaneGraphDrawing.IsExternal F :=
  hDraws.unbounded_face_to_external U hU

/-- Helper toward Definition 3.2: simultaneous left-side tests on two
injective parameterizations agree when their oriented ranges agree. -/
theorem boundaryChanneled_leftAtOn_transfer_of_injective_range_eq
    {x y : ℂ} (F : Set ℂ) (γ δ : Path x y)
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hrange : Set.range δ = Set.range γ) :
    (∀ s : {t : unitInterval // t ∈ openParams}, LeftAtOn F δ s) ↔
      ∀ s : {t : unitInterval // t ∈ openParams}, LeftAtOn F γ s :=
  forall_leftAtOn_iff_of_injective_range_eq F γ δ hγ hδ hrange

/-- Helper toward Definition 3.2: simultaneous right-side tests on two
injective parameterizations agree when their oriented ranges agree. -/
theorem boundaryChanneled_rightAtOn_transfer_of_injective_range_eq
    {x y : ℂ} (F : Set ℂ) (γ δ : Path x y)
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hrange : Set.range δ = Set.range γ) :
    (∀ s : {t : unitInterval // t ∈ openParams}, RightAtOn F δ s) ↔
      ∀ s : {t : unitInterval // t ∈ openParams}, RightAtOn F γ s := by
  have hleft := forall_leftAtOn_iff_of_injective_range_eq F γ.symm δ.symm
    (hγ.comp unitInterval.symm_bijective.injective)
    (hδ.comp unitInterval.symm_bijective.injective)
    (by simpa only [Path.symm_range] using hrange)
  exact (forall_leftAtOn_symm_iff F δ).symm.trans
    (hleft.trans (forall_leftAtOn_symm_iff F γ))

/- The generic side lemmas above do not discharge the boundary-channeled side
transfer: `DrawsMap` gives range equality, but the following oriented path
identifications, with their endpoint and injectivity obligations, remain to
be proved from the encoding and drawing fields.

OPEN side transfer (full binders):

    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded : G.IsUnbounded (boundaryChanneledMarkedOuterFace R G))
    (rot : Equiv.Perm (G.GeometricEdge × Bool))
    (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial (boundaryChanneledPlaneMap R G)))
    (U : H.Face)
    (hDraws : DrawsMap (boundaryChanneledPlaneMap R G) H)
    (hU : H.IsUnbounded U)
    (F : (boundaryChanneledPlaneMap R G).toPlaneMapWithMissing
      .toPlaneGraphDrawing.Face)
    (hF : F.val = U.val)
    (hFext : (boundaryChanneledPlaneMap R G).toPlaneMapWithMissing
      .toPlaneGraphDrawing.IsExternal F) :
    ∀ e (hp : ¬ (boundaryChanneledPlaneMap R G).toPlaneMapWithMissing.missing e),
      ((∀ s : {t : unitInterval // t ∈ openParams},
          LeftAtOn U.val
            (H.arc (e, (boundaryChanneledPlaneMap R G).forward ⟨e, hp⟩)).toPath s) ↔
        LeftOf (boundaryChanneledPlaneMap R G) F ⟨e, hp⟩) ∧
      ((∀ s : {t : unitInterval // t ∈ openParams},
          RightAtOn U.val
            (H.arc (e, (boundaryChanneledPlaneMap R G).forward ⟨e, hp⟩)).toPath s) ↔
        RightOf (boundaryChanneledPlaneMap R G) F ⟨e, hp⟩)

Here `F` can be supplied by `boundaryChanneled_drawsMap_externalFace`. The
remaining path identification still does not follow from range equality
without proving endpoint agreement and injectivity for both parameterizations.

OPEN dart coverage (full binders):

    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded : G.IsUnbounded (boundaryChanneledMarkedOuterFace R G))
    (rot : Equiv.Perm (G.GeometricEdge × Bool))
    (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial (boundaryChanneledPlaneMap R G)))
    (U : H.Face)
    (hDraws : DrawsMap (boundaryChanneledPlaneMap R G) H)
    (hU : H.IsUnbounded U) :
    ∀ d, H.dartBorders d U ↔
      ∃ i : InfiniteBoundaryDartIndex
        (boundaryChanneledPresentationWithJunctions R G).presentation,
        InfiniteBoundaryDartIndex.dart
          (boundaryChanneledPresentationWithJunctions R G).presentation i = d

OPEN upper-left orientation (full binders):

    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded : G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    ULOkInf (boundaryChanneledPresentationWithJunctions R G).presentation

OPEN lower-right orientation (full binders):

    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded : G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    LROkInf (boundaryChanneledPresentationWithJunctions R G).presentation

OPEN Geometry2 wrapper (full binders; the UL and LR premises are removed):

    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded : G.IsUnbounded (boundaryChanneledMarkedOuterFace R G))
    (h_boundary_dart_coverage :
      ∀ (rot : Equiv.Perm (G.GeometricEdge × Bool))
        (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
          (fun d => (d.1, !d.2)) rot
          (boundaryDartInitial (boundaryChanneledPlaneMap R G))) (U : H.Face),
        DrawsMap (boundaryChanneledPlaneMap R G) H → H.IsUnbounded U →
        ∀ d, H.dartBorders d U ↔
          ∃ i : InfiniteBoundaryDartIndex
            (boundaryChanneledPresentationWithJunctions R G).presentation,
            InfiniteBoundaryDartIndex.dart
              (boundaryChanneledPresentationWithJunctions R G).presentation i = d)
    (h_boundary_geometric_successor :
      ∀ (rot : Equiv.Perm (G.GeometricEdge × Bool))
        (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
          (fun d => (d.1, !d.2)) rot
          (boundaryDartInitial (boundaryChanneledPlaneMap R G))) (U : H.Face),
        DrawsMap (boundaryChanneledPlaneMap R G) H → H.IsUnbounded U →
        IsGeometricExternalFaceSucc H U (fun d => rot.symm (d.1, !d.2)))
    (h_boundary_order : IsBoundaryOrderOfInf (boundaryChanneledPlaneMap R G)
      (boundaryChanneledPresentationWithJunctions R G).presentation)
    (h_boundary_finite_position_order :
      ∀ (rot : Equiv.Perm (G.GeometricEdge × Bool))
        (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
          (fun d => (d.1, !d.2)) rot
          (boundaryDartInitial (boundaryChanneledPlaneMap R G))),
        DrawsMap (boundaryChanneledPlaneMap R G) H →
        FiniteBoundaryPositionOrder4
          (boundaryChanneledPresentationWithJunctions R G).presentation
          (fun d => rot.symm (d.1, !d.2))) :
    let M := boundaryChanneledPlaneMap R G
    ∃ (B : BoundaryPresentationWithJunctions M)
      (rot : Equiv.Perm (G.GeometricEdge × Bool))
      (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
        (fun d => (d.1, !d.2)) rot (boundaryDartInitial M))
      (U : H.Face) (S : G.GeometricEdge × Bool → G.GeometricEdge × Bool),
      B = boundaryChanneledPresentationWithJunctions R G ∧ DrawsMap M H ∧
        IsFiniteExternalFaceIntervalOrder7 M B H U S

Three routes were tried for the open statements:
1. Transfer `dartBorders` by applying the marked-face outer-word
   characterization in Geometry8 and then `DrawsMap.image_eq`. This identifies
   complementary component sets, but the range equality does not identify the
   initial oriented wedge in `dartBorders`.
2. Reuse the KMSW finite-presentation side and four-run proofs from
   `KMSWFiniteBoundaryPresentation16`. Their realization lemmas provide
   parameterized oriented-arc identities for a stage map; no such identity is
   yet established for an arbitrary `DrawsMap` drawing here.
3. Reindex the particular transported drawing from Geometry2 and use its
   dart equivalence. This handles that constructed drawing, whereas coverage
   and the Geometry2 wrapper quantify over every drawing satisfying
   `DrawsMap`; it does not prove the arbitrary-drawing clauses.

No extra premise has been introduced, and no paper-completion claim is made. -/

end DirectedDistances.PaperProofs.Section3

end
end
