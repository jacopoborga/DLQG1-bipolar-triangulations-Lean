/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry21
public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry22
public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledPart1

/- The exact boundary-order and infinite-side clauses are available from the
It is distinct from the finite cyclic order required by Package3, whose
successor depends on each compatible drawing's rotation. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the channeled presentation lists precisely
the external frontier edges, with the permitted multiplicity and bridge
conditions, when its marked outer face is unbounded. -/
theorem boundaryChanneledPresentation_boundaryOrder23
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    IsBoundaryOrderOfInf (boundaryChanneledPlaneMap R G)
      (boundaryChanneledPresentationWithJunctions R G).presentation :=
  boundaryChanneledPresentation_boundaryOrder_part1 R G hOuterUnbounded

/-- Helper toward Definition 3.2: the channeled presentation has the exact
UL and LR infinite-side clauses and the integer order of its two finite path
blocks. -/
theorem boundaryChanneledPresentation_fixedBoundaryClauses23
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    ULOkInf (boundaryChanneledPresentationWithJunctions R G).presentation ∧
      LROkInf (boundaryChanneledPresentationWithJunctions R G).presentation ∧
      BoundaryPositionOrder3
        (boundaryChanneledPresentationWithJunctions R G).presentation := by
  exact ⟨boundaryChanneledPresentation_ULOkInf22 R G hOuterUnbounded,
    boundaryChanneledPresentation_LROkInf22 R G hOuterUnbounded,
    boundaryChanneledPresentation_positionOrder3 R G⟩

/-- Helper toward Definition 3.2: every compatible finite dart drawing has
the required geometric external-face successor at any unbounded face. -/
theorem boundaryChanneledPresentation_geometricSuccessor23
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (rot : Equiv.Perm (G.GeometricEdge × Bool))
    (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial (boundaryChanneledPlaneMap R G)))
    (U : H.Face) (hU : H.IsUnbounded U) :
    IsGeometricExternalFaceSucc H U (fun d => rot.symm (d.1, !d.2)) :=
  boundaryChanneled_geometricSuccessor_part1 R G rot H U hU

























end DirectedDistances.PaperProofs.Section3

end
