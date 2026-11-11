/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Package2
public import DirectedDistances.PaperProofs.Section4.UIQBOTExternalFaceIntervalOrderInstance5
public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation5
public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledPresentation4
public import DirectedDistances.PaperProofs.Section5.UIBHBOTBoundaryPresentationGeometry5
public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact4

import all DirectedDistances.PaperProofs.Section4.UIQBOTBoundaryIntervalOrder3
import all DirectedDistances.PaperProofs.Section4.UIQBOTExternalFaceGeometry2

/-! Helper toward Definition 3.2: dependency discharge for the conditional packages. -/

public section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the constructed within-side rotation
equation also identifies the common endpoint on the quotient map. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_withinSideSuccessor3
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    ∀ i j : InfiniteBoundaryDartIndex P, sideNext P i = some j →
      uiqbotCanonicalBoundaryDartExternalSucc w hfin
          (InfiniteBoundaryDartIndex.dart P i) = InfiniteBoundaryDartIndex.dart P j ∧
      boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart P i) =
        boundaryDartInitial M (InfiniteBoundaryDartIndex.dart P j) := by
  dsimp only
  intro i j hij
  have hstep :=
    uiqbotCanonicalBoundaryPresentationLabeledX_constructedWithinSideSuccessor
      w hfin htrans hR hL0 i j hij
  refine ⟨?_, ?_⟩
  · simpa only [uiqbotCanonicalBoundaryDartExternalSucc,
      uiqbotCanonicalBoundaryDartEquiv, Equiv.symm_symm] using hstep
  · exact uiqbotCanonicalBoundaryPresentationLabeledX_constructedWithinSideEndpointJoin
      w hfin htrans hR hL0 i j hij

/-- Helper toward Definition 3.2: the UIQBOT existence package with the
within-side successor clause discharged; the classification premise is unchanged. -/
theorem exists_uiqbot_bound_edges32_of_open_clauses3
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (h_uiqbot_successor_classification :
      let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
      let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
      ∀ i j : InfiniteBoundaryDartIndex P,
        uiqbotCanonicalBoundaryDartExternalSucc w hfin
            (InfiniteBoundaryDartIndex.dart P i) = InfiniteBoundaryDartIndex.dart P j →
        sideNext P i = some j ∨
          (sideNext P i = none ∧ firstOnSide P j ∧
            nextNonemptySide P (sideTag P i) (sideTag P j) ∧
            boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart P i) =
              boundaryDartInitial M (InfiniteBoundaryDartIndex.dart P j))) :
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    ∃ (B : BoundaryPresentationWithJunctions M)
      (rot : Equiv.Perm ((uiqbotPresentationDrawing w hfin).GeometricEdge × Bool))
      (G : PLDrawing ((uiqbotPresentationDrawing w hfin).GeometricEdge × Bool) ℕ
        (fun d => (d.1, !d.2)) rot (boundaryDartInitial M))
      (U : G.Face) (S : (uiqbotPresentationDrawing w hfin).GeometricEdge × Bool →
        (uiqbotPresentationDrawing w hfin).GeometricEdge × Bool),
      B = uiqbotCanonicalBoundaryPresentationLabeledXWithJunctions
        w hfin htrans hR hL0 ∧ B.finiteJunctions? = none ∧
        IsBoundEdges32 M B G U S := by
  exact exists_uiqbot_bound_edges32_of_open_clauses2 w hfin htrans hR hL0
    (uiqbotCanonicalBoundaryPresentationLabeledX_withinSideSuccessor3
      w hfin htrans hR hL0) h_uiqbot_successor_classification

end DirectedDistances.PaperProofs.Section4

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: finite transported drawings have an unbounded
face, so the boundary-channeled package no longer assumes its existence. -/
theorem exists_boundaryChanneled_bound_edges32_of_open_clauses3
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
    (h_boundary_upperLeft_simple : IsSimpleBoundarySide (boundaryChanneledPlaneMap R G)
      (boundaryChanneledPresentationWithJunctions R G).presentation.upperLeft)
    (h_boundary_lowerRight_simple : IsSimpleBoundarySide (boundaryChanneledPlaneMap R G)
      (boundaryChanneledPresentationWithJunctions R G).presentation.lowerRight)
    (h_boundary_upperLeft_endpoint_labels :
      BoundarySideEndpointLabels (boundaryChanneledPlaneMap R G)
        (boundaryChanneledPresentationWithJunctions R G).presentation.upperLeft)
    (h_boundary_lowerRight_endpoint_labels :
      BoundarySideEndpointLabels (boundaryChanneledPlaneMap R G)
        (boundaryChanneledPresentationWithJunctions R G).presentation.lowerRight)
    (h_boundary_finite_position_order :
      ∀ (rot : Equiv.Perm (G.GeometricEdge × Bool))
        (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
          (fun d => (d.1, !d.2)) rot
          (boundaryDartInitial (boundaryChanneledPlaneMap R G))),
        DrawsMap (boundaryChanneledPlaneMap R G) H →
        FiniteBoundaryPositionOrder4
          (boundaryChanneledPresentationWithJunctions R G).presentation
          (fun d => rot.symm (d.1, !d.2)))
    (h_boundary_required_join_labels :
      ∀ (rot : Equiv.Perm (G.GeometricEdge × Bool))
        (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
          (fun d => (d.1, !d.2)) rot
          (boundaryDartInitial (boundaryChanneledPlaneMap R G))),
        DrawsMap (boundaryChanneledPlaneMap R G) H →
        RequiredFiniteBoundaryJoinEndpointLabels7
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
  apply exists_boundaryChanneled_bound_edges32_of_open_clauses2 R G
    h_boundary_drawing_transport _ h_boundary_dart_coverage
    h_boundary_geometric_successor h_boundary_order
    h_boundary_upperLeft_orientation h_boundary_lowerRight_orientation
    h_boundary_upperLeft_simple h_boundary_lowerRight_simple
    h_boundary_upperLeft_endpoint_labels h_boundary_lowerRight_endpoint_labels
    h_boundary_finite_position_order h_boundary_required_join_labels
  intro rot H _
  exact H.existsUnique_unbounded_face.exists

end DirectedDistances.PaperProofs.Section3

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: every finite stage drawing has an unbounded
face; all other outstanding named premises retain their original binders. -/
theorem exists_kmswStage_bound_edges32_of_open_clauses3
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (h_stage_map_and_junction_transport :
      ∃ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M ∧
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).upperLeft ∧
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).upperRight ∧
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).lowerRight ∧
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).lowerLeft)
    (h_stage_dart_coverage :
      ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)) (U : P.Face),
        kmsw_stage_map_realization32 w n P M → P.IsUnbounded U →
        ∀ d, P.dartBorders d U ↔ ∃ i : InfiniteBoundaryDartIndex
          (kmswStageFiniteBoundaryPresentation w n M J),
          InfiniteBoundaryDartIndex.dart (kmswStageFiniteBoundaryPresentation w n M J) i = d)
    (h_stage_geometric_successor : ∀ U : P.Face, P.IsUnbounded U →
      IsGeometricExternalFaceSucc P U
        (fun d => (stageRot w n).symm (d.1, !d.2)))
    (h_stage_boundary_order :
      ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M →
        IsBoundaryOrderOfInf M (kmswStageFiniteBoundaryPresentation w n M J))
    (h_stage_upperLeft_orientation :
      ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M →
        ULOkInf (kmswStageFiniteBoundaryPresentation w n M J))
    (h_stage_upperRight_missing_run :
      ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M →
        UROkInf (kmswStageFiniteBoundaryPresentation w n M J))
    (h_stage_lowerRight_orientation :
      ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M →
        LROkInf (kmswStageFiniteBoundaryPresentation w n M J))
    (h_stage_lowerLeft_missing_run :
      ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M →
        LLOkInf (kmswStageFiniteBoundaryPresentation w n M J))
    (h_stage_upperLeft_simple :
      ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M → IsSimpleBoundarySide M
          (kmswStageFiniteBoundaryPresentation w n M J).upperLeft)
    (h_stage_lowerRight_simple :
      ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M → IsSimpleBoundarySide M
          (kmswStageFiniteBoundaryPresentation w n M J).lowerRight)
    (h_stage_finite_position_order :
      ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M →
        FiniteBoundaryPositionOrder4 (kmswStageFiniteBoundaryPresentation w n M J)
          (fun d => (stageRot w n).symm (d.1, !d.2)))
    (h_stage_required_join_labels :
      ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M →
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).upperLeft →
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).upperRight →
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).lowerRight →
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).lowerLeft →
        RequiredFiniteBoundaryJoinEndpointLabels7 (kmswStageFiniteBoundaryPresentation w n M J)
          (fun d => (stageRot w n).symm (d.1, !d.2))) :
    ∃ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
      (B : BoundaryPresentationWithJunctions M)
      (rot : Equiv.Perm (Fin (kmswStage w n).nextEdge × Bool))
      (G : PLDrawing (Fin (kmswStage w n).nextEdge × Bool)
        (Fin (kmswStage w n).nextVertex) (fun d => (d.1, !d.2)) rot
        (boundaryDartInitial M)) (U : G.Face)
      (S : Fin (kmswStage w n).nextEdge × Bool → Fin (kmswStage w n).nextEdge × Bool),
      kmsw_stage_map_realization32 w n P M ∧
      B = kmswStageFiniteBoundaryPresentationWithJunctions w n M J ∧
      G.image = P.image ∧ IsBoundEdges32 M B G U S := by
  exact exists_kmswStage_bound_edges32_of_open_clauses2 w n P
    h_stage_map_and_junction_transport P.existsUnique_unbounded_face.exists
    h_stage_dart_coverage h_stage_geometric_successor h_stage_boundary_order
    h_stage_upperLeft_orientation h_stage_upperRight_missing_run
    h_stage_lowerRight_orientation h_stage_lowerLeft_missing_run
    h_stage_upperLeft_simple h_stage_lowerRight_simple
    h_stage_finite_position_order h_stage_required_join_labels

end DirectedDistances.PaperProofs.Section3






















































































































































































