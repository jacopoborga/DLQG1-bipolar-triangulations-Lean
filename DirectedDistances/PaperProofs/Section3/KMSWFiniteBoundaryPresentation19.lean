/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation14
public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation15
public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation16
public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation17
public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation18




public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the upper-left orientation premise in the
common binder form of Presentation 14. -/
theorem kmswStageFiniteBoundaryPresentation19_upperLeft_clause
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (_hU : P.IsUnbounded U)
    (_hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) :
    ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      ULOkInf (kmswStageFiniteBoundaryPresentation w n M J) := by
  intro M J hreal
  exact kmswStageFiniteBoundaryPresentation16_upperLeft_ok
    w n P U _hU _hborder M J hreal

/-- Helper toward Definition 3.2: the upper-right missing-run premise in the
common binder form of Presentation 14. -/
theorem kmswStageFiniteBoundaryPresentation19_upperRight_clause
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) :
    ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      UROkInf (kmswStageFiniteBoundaryPresentation w n M J) := by
  intro M J hreal
  exact kmswStageFiniteBoundaryPresentation15_upperRight
    w n P U hU hborder M J hreal

/-- Helper toward Definition 3.2: the lower-right orientation premise in the
common binder form of Presentation 14. -/
theorem kmswStageFiniteBoundaryPresentation19_lowerRight_clause
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (_hU : P.IsUnbounded U)
    (_hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) :
    ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      LROkInf (kmswStageFiniteBoundaryPresentation w n M J) := by
  intro M J hreal
  exact kmswStageFiniteBoundaryPresentation16_lowerRight_ok
    w n P U _hU _hborder M J hreal

/-- Helper toward Definition 3.2: the lower-left missing-run premise in the
common binder form of Presentation 14. -/
theorem kmswStageFiniteBoundaryPresentation19_lowerLeft_clause
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) :
    ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      LLOkInf (kmswStageFiniteBoundaryPresentation w n M J) := by
  intro M J hreal
  exact kmswStageFiniteBoundaryPresentation15_lowerLeft
    w n P U hU hborder M J hreal

/-- Helper toward Definition 3.2: Presentation 14's package with all four
premises discharged by Presentations 15 and 16 removed at once. Boundary
order, finite position order, and cyclic join labels remain explicit. -/
theorem exists_kmswStage_bound_edges32_of_open_clauses19
    (w : ℕ → Fin 3) (n : ℕ) :
    ∃ (P : StageDrawing w n) (U : P.Face)
      (_hU : P.IsUnbounded U)
      (_hborder : ∀ d, P.dartBorders d U ↔
        (kmswStageDirectedMap w n).IsOuter d),
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      IsBoundaryOrderOfInf M (kmswStageFiniteBoundaryPresentation w n M J)) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge)),
      ∀ (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      FiniteBoundaryPositionOrder4
        (kmswStageFiniteBoundaryPresentation w n M J)
        (fun d => (stageRot w n).symm (d.1, !d.2))) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      BoundarySideEndpointLabels M
        (kmswStageFiniteBoundaryPresentation w n M J).upperLeft →
      BoundarySideEndpointLabels M
        (kmswStageFiniteBoundaryPresentation w n M J).upperRight →
      BoundarySideEndpointLabels M
        (kmswStageFiniteBoundaryPresentation w n M J).lowerRight →
      BoundarySideEndpointLabels M
        (kmswStageFiniteBoundaryPresentation w n M J).lowerLeft →
      RequiredFiniteBoundaryJoinEndpointLabels7
        (kmswStageFiniteBoundaryPresentation w n M J)
        (fun d => (stageRot w n).symm (d.1, !d.2))) →
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
  obtain ⟨P, U, hU, hborder, hpackage⟩ :=
    exists_kmswStage_bound_edges32_of_open_clauses14 w n
  refine ⟨P, U, hU, hborder, ?_⟩
  intro hboundary hposition hjoin
  exact hpackage hboundary
    (kmswStageFiniteBoundaryPresentation19_upperLeft_clause
      w n P U hU hborder)
    (kmswStageFiniteBoundaryPresentation19_upperRight_clause
      w n P U hU hborder)
    (kmswStageFiniteBoundaryPresentation19_lowerRight_clause
      w n P U hU hborder)
    (kmswStageFiniteBoundaryPresentation19_lowerLeft_clause
      w n P U hU hborder)
    hposition hjoin

end DirectedDistances.PaperProofs.Section3
