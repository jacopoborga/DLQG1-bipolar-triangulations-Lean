/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Package3
public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledPresentation7

 

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-! Premise discharge table for `exists_boundaryChanneled_bound_edges32_of_open_clauses4`:

| Package3 premise | Status |
| --- | --- |
| `h_boundary_drawing_transport` | OPEN |
| `h_boundary_dart_coverage` | OPEN |
| `h_boundary_geometric_successor` | OPEN |
| `h_boundary_order` | OPEN |
| `h_boundary_upperLeft_orientation` | OPEN |
| `h_boundary_lowerRight_orientation` | OPEN |
| `h_boundary_upperLeft_simple` | DISCHARGED, `BoundaryChanneledPresentation5.lean:126` |
| `h_boundary_lowerRight_simple` | DISCHARGED, `BoundaryChanneledPresentation5.lean:355` |
| `h_boundary_upperLeft_endpoint_labels` | DISCHARGED, `BoundaryChanneledPresentation6.lean:102` |
| `h_boundary_lowerRight_endpoint_labels` | DISCHARGED, `BoundaryChanneledPresentation6.lean:364` |
| `h_boundary_finite_position_order` | OPEN |
| `h_boundary_required_join_labels` | DISCHARGED, `BoundaryChanneledPresentation7.lean:21` |

The seven OPEN premises are retained in the declaration below with their full
Package3 binders. Three routes were tried for this open geometric group:
(1) transfer the channel's path-edge occurrences through `DrawsMap`;
(2) use dart rotation and local endpoint incidence to identify the external
successor; and (3) transport the finite UL/LR outer-word order to the drawing.
The first needs a proved occurrence correspondence, the second needs the
successor classification, and the third needs that same correspondence.
The available `positionOrder3` does not identify an arbitrary transported
successor, so it does not discharge finite position order. No premise was
added or altered. -/

/-- Helper toward Definition 3.2: the boundary-channeled package with every
premise supplied by Presentations 5–7 discharged. -/
theorem exists_boundaryChanneled_bound_edges32_of_open_clauses4
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R)
    (h_boundary_drawing_transport :
      ∃ (rot : Equiv.Perm (G.GeometricEdge × Bool))
        (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
          (fun d => (d.1, !d.2)) rot
          (boundaryDartInitial (boundaryChanneledPlaneMap R G))),
        DrawsMap (boundaryChanneledPlaneMap R G) H)
    (h_boundary_dart_coverage :
      ∀ (rot : Equiv.Perm (G.GeometricEdge × Bool))
        (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
          (fun d => (d.1, !d.2)) rot
          (boundaryDartInitial (boundaryChanneledPlaneMap R G))) (U : H.Face),
        DrawsMap (boundaryChanneledPlaneMap R G) H → H.IsUnbounded U →
        ∀ d, H.dartBorders d U ↔ ∃ i : InfiniteBoundaryDartIndex
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
    (h_boundary_upperLeft_orientation :
      ULOkInf (boundaryChanneledPresentationWithJunctions R G).presentation)
    (h_boundary_lowerRight_orientation :
      LROkInf (boundaryChanneledPresentationWithJunctions R G).presentation)
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
        IsFiniteExternalFaceIntervalOrder7 M B H U S := by
  exact exists_boundaryChanneled_bound_edges32_of_open_clauses3 R G
    h_boundary_drawing_transport h_boundary_dart_coverage
    h_boundary_geometric_successor h_boundary_order
    h_boundary_upperLeft_orientation h_boundary_lowerRight_orientation
    (boundaryChanneledPresentation_upperLeft_simple R G)
    (boundaryChanneledPresentation_lowerRight_simple R G)
    (boundaryChanneledPresentation_upperLeft_endpointLabels6 R G)
    (boundaryChanneledPresentation_lowerRight_endpointLabels6 R G)
    h_boundary_finite_position_order
    (fun rot H hDraws =>
      boundaryChanneledPresentation_requiredJoinEndpointLabels7 R G rot H hDraws)

end DirectedDistances.PaperProofs.Section3

end
end
