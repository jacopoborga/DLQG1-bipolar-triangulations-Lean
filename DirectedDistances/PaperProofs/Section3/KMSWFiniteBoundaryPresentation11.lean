/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation10
public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Package3

 

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the finite KMSW package with its exact-tag
map-and-junction transport premise discharged; every remaining package
premise retains the binders and name used by Package3. -/
theorem exists_kmswStage_bound_edges32_of_open_clauses4
    (w : ℕ → Fin 3) (n : ℕ) :
    ∃ (P : StageDrawing w n) (U : P.Face)
      (hU : P.IsUnbounded U)
      (hborder : ∀ d, P.dartBorders d U ↔
        (kmswStageDirectedMap w n).IsOuter d),
    ∀ (h_stage_dart_coverage :
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
          (fun d => (stageRot w n).symm (d.1, !d.2))),
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
  obtain ⟨P, U, hU, _hunique, hborder⟩ :=
    DirectedDistances.PaperProofs.Section5.kmswStageDrawing_uniqueExteriorFace_borders_iff_isOuter
      w n
  refine ⟨P, U, hU, hborder, ?_⟩
  intro h_stage_dart_coverage h_stage_geometric_successor h_stage_boundary_order
    h_stage_upperLeft_orientation h_stage_upperRight_missing_run
    h_stage_lowerRight_orientation h_stage_lowerLeft_missing_run
    h_stage_upperLeft_simple h_stage_lowerRight_simple h_stage_finite_position_order
    h_stage_required_join_labels
  let M := kmswStageFiniteBoundaryPresentation8DirectedPlaneMap w n P U hU hborder
  let J := kmswStageFiniteBoundaryPresentation5Junctions w n
  have hreal : kmsw_stage_map_realization32 w n P M :=
    kmswStageFiniteBoundaryPresentation8_realizes w n P U hU hborder
  have hlabelsUL : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).upperLeft :=
    kmswStageFiniteBoundaryPresentation10_upperLeft_endpointLabels w n P U hU hborder
  have hlabelsUR : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).upperRight :=
    kmswStageFiniteBoundaryPresentation10_upperRight_endpointLabels w n P U hU hborder
  have hlabelsLR : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).lowerRight :=
    kmswStageFiniteBoundaryPresentation10_lowerRight_endpointLabels w n P U hU hborder
  have hlabelsLL : BoundarySideEndpointLabels M
      (kmswStageFiniteBoundaryPresentation w n M J).lowerLeft :=
    kmswStageFiniteBoundaryPresentation10_lowerLeft_endpointLabels w n P U hU hborder
  have htransport :
      ∃ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M ∧
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).upperLeft ∧
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).upperRight ∧
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).lowerRight ∧
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).lowerLeft :=
    ⟨M, J, hreal, hlabelsUL, hlabelsUR, hlabelsLR, hlabelsLL⟩
  exact exists_kmswStage_bound_edges32_of_open_clauses3 w n P htransport
    h_stage_dart_coverage h_stage_geometric_successor h_stage_boundary_order
    h_stage_upperLeft_orientation h_stage_upperRight_missing_run
    h_stage_lowerRight_orientation h_stage_lowerLeft_missing_run
    h_stage_upperLeft_simple h_stage_lowerRight_simple h_stage_finite_position_order
    h_stage_required_join_labels








































end DirectedDistances.PaperProofs.Section3
