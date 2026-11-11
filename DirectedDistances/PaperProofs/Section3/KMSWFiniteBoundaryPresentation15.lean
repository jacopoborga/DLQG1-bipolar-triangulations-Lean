/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation12

 

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: every upper-right run dart is missing and
every consecutive pair joins under any realization of the stage map. -/
theorem kmswStageFiniteBoundaryPresentation15_upperRight
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (_hU : P.IsUnbounded U)
    (_hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (hreal : kmsw_stage_map_realization32 w n P M) :
    UROkInf (kmswStageFiniteBoundaryPresentation w n M J) := by
  rw [UROkInf_iff]
  constructor
  · intro i
    let d := (kmswStageURDartRun w n)[i.val]'i.isLt
    let e := d.1
    have he : e.val ∈ (kmswStage w n).UR := by
      simp [e, d, kmswStageURDartRun, stageDarts]
    have hmiss := (kmswStage_finite_missing_run_darts w n).1 e he
    have hrealMiss := hreal.2.2.2.1 e
    change M.toPlaneMapWithMissing.missing e
    exact hrealMiss.mpr hmiss.1
  · intro i j hnext
    have hnext' : kmswFiniteRunNext i = some j := by
      simpa [kmswStageFiniteBoundaryPresentation, kmswFiniteRunSide] using hnext
    have hval : j.val = i.val + 1 := by
      unfold kmswFiniteRunNext at hnext'
      split at hnext'
      · exact (congrArg Fin.val (Option.some.inj hnext')).symm
      · simp at hnext'
    have hbound : i.val + 1 < (kmswStageURDartRun w n).length := by
      simpa [hval] using j.isLt
    have hiUR : i.val < (kmswStage w n).UR.length := by
      simpa [kmswStageURDartRun, stageDarts] using i.isLt
    have hchain := (kmswStage_finite_run_junction_record w n).UR_chain
    have hboundUR : i.val + 1 < (kmswStage w n).UR.length := by
      simpa [kmswStageURDartRun, stageDarts] using hbound
    have hstep := (List.isChain_iff_getElem.mp hchain) i.val hboundUR
    let di := (kmswStageURDartRun w n)[i.val]'i.isLt
    let dj := (kmswStageURDartRun w n)[j.val]'j.isLt
    have hjUR : j.val < (kmswStage w n).UR.length := by
      simpa [kmswStageURDartRun, stageDarts] using j.isLt
    let ei : Fin (kmswStage w n).nextEdge := ⟨
      (kmswStage w n).UR[i.val]'hiUR,
      stageRun_edge_bound w n _ (Or.inl (Or.inl (Or.inr (List.getElem_mem hiUR))))⟩
    let ej : Fin (kmswStage w n).nextEdge := ⟨
      (kmswStage w n).UR[j.val]'hjUR,
      stageRun_edge_bound w n _ (Or.inl (Or.inl (Or.inr (List.getElem_mem hjUR))))⟩
    have hdi : di = (ei, false) := by
      simp [di, ei, kmswStageURDartRun, stageDarts]
    have hdj : dj = (ej, false) := by
      simp [dj, ej, kmswStageURDartRun, stageDarts]
    have htail : boundaryDartTerminal M di = stageVertex w n (edgeFlip _ di) :=
      kmswStageFiniteBoundaryPresentation6_terminal_endpoint w n P M hreal di
    have hhead : boundaryDartInitial M dj = stageVertex w n dj :=
      kmswStageFiniteBoundaryPresentation6_initial_endpoint w n P M hreal dj
    change boundaryDartTerminal M di = boundaryDartInitial M dj
    rw [htail, hhead, hdi, hdj]
    apply Fin.ext
    simpa [stageVertex, stageEndpoint, edgeFlip, ei, ej, hval] using hstep.symm

/-- Helper toward Definition 3.2: every lower-left run dart is missing and
every consecutive pair joins under any realization of the stage map. -/
theorem kmswStageFiniteBoundaryPresentation15_lowerLeft
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n) (U : P.Face)
    (_hU : P.IsUnbounded U)
    (_hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (hreal : kmsw_stage_map_realization32 w n P M) :
    LLOkInf (kmswStageFiniteBoundaryPresentation w n M J) := by
  rw [LLOkInf_iff]
  constructor
  · intro i
    let d := (kmswStageLLDartRun w n)[i.val]'i.isLt
    let e := d.1
    have he : e.val ∈ (kmswStage w n).LL.reverse := by
      simp [e, d, kmswStageLLDartRun, stageDarts]
    have hmem : e.val ∈ (kmswStage w n).LL := List.mem_reverse.mp he
    have hmiss := (kmswStage_finite_missing_run_darts w n).2 e hmem
    have hrealMiss := hreal.2.2.2.1 e
    change M.toPlaneMapWithMissing.missing e
    exact hrealMiss.mpr hmiss.1
  · intro i j hnext
    have hnext' : kmswFiniteRunNext i = some j := by
      simpa [kmswStageFiniteBoundaryPresentation, kmswFiniteRunSide] using hnext
    have hval : j.val = i.val + 1 := by
      unfold kmswFiniteRunNext at hnext'
      split at hnext'
      · exact (congrArg Fin.val (Option.some.inj hnext')).symm
      · simp at hnext'
    have hbound : i.val + 1 < (kmswStageLLDartRun w n).length := by
      simpa [hval] using j.isLt
    have hiLL : i.val < ((kmswStage w n).LL.reverse).length := by
      simpa [kmswStageLLDartRun, stageDarts] using i.isLt
    have hchain := (kmswStage_finite_run_junction_record w n).LL_chain
    have hrevchain := List.isChain_reverse.mpr hchain
    have hboundLL : i.val + 1 < ((kmswStage w n).LL.reverse).length := by
      simpa [kmswStageLLDartRun, stageDarts] using hbound
    have hstep := (List.isChain_iff_getElem.mp hrevchain) i.val hboundLL
    let di := (kmswStageLLDartRun w n)[i.val]'i.isLt
    let dj := (kmswStageLLDartRun w n)[j.val]'j.isLt
    have hjLL : j.val < ((kmswStage w n).LL.reverse).length := by
      simpa [kmswStageLLDartRun, stageDarts] using j.isLt
    let ei : Fin (kmswStage w n).nextEdge := ⟨
      (kmswStage w n).LL.reverse[i.val]'hiLL,
      stageRun_edge_bound w n _ (Or.inl (Or.inr
        (List.mem_reverse.mp (List.getElem_mem hiLL))))⟩
    let ej : Fin (kmswStage w n).nextEdge := ⟨
      (kmswStage w n).LL.reverse[j.val]'hjLL,
      stageRun_edge_bound w n _ (Or.inl (Or.inr
        (List.mem_reverse.mp (List.getElem_mem hjLL))))⟩
    have hdi : di = (ei, true) := by
      simp [di, ei, kmswStageLLDartRun, stageDarts]
    have hdj : dj = (ej, true) := by
      simp [dj, ej, kmswStageLLDartRun, stageDarts]
    have htail : boundaryDartTerminal M di = stageVertex w n (edgeFlip _ di) :=
      kmswStageFiniteBoundaryPresentation6_terminal_endpoint w n P M hreal di
    have hhead : boundaryDartInitial M dj = stageVertex w n dj :=
      kmswStageFiniteBoundaryPresentation6_initial_endpoint w n P M hreal dj
    change boundaryDartTerminal M di = boundaryDartInitial M dj
    rw [htail, hhead, hdi, hdj]
    apply Fin.ext
    simpa [stageVertex, stageEndpoint, edgeFlip, ei, ej, hval] using hstep.symm

/-- Helper toward Definition 3.2: the package corollary discharges the
upper-right and lower-left missing-run premises from the stage realization. -/
theorem exists_kmswStage_bound_edges32_of_open_clauses5_of_UR_LL
    (w : ℕ → Fin 3) (n : ℕ) :
    ∃ (P : StageDrawing w n) (U : P.Face)
    (_hU : P.IsUnbounded U)
    (_hborder : ∀ d, P.dartBorders d U ↔
        (kmswStageDirectedMap w n).IsOuter d),
    (∀ U : P.Face, P.IsUnbounded U →
      IsGeometricExternalFaceSucc P U
        (fun d => (stageRot w n).symm (d.1, !d.2))) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      IsBoundaryOrderOfInf M (kmswStageFiniteBoundaryPresentation w n M J)) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      ULOkInf (kmswStageFiniteBoundaryPresentation w n M J)) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge)),
      ∀ (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      LROkInf (kmswStageFiniteBoundaryPresentation w n M J)) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M → IsSimpleBoundarySide M
        (kmswStageFiniteBoundaryPresentation w n M J).upperLeft) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M → IsSimpleBoundarySide M
        (kmswStageFiniteBoundaryPresentation w n M J).lowerRight) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      FiniteBoundaryPositionOrder4 (kmswStageFiniteBoundaryPresentation w n M J)
        (fun d => (stageRot w n).symm (d.1, !d.2))) →
    (∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
        (Fin (kmswStage w n).nextEdge))
      (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
      kmsw_stage_map_realization32 w n P M →
      BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).upperLeft →
      BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).upperRight →
      BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).lowerRight →
      BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).lowerLeft →
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
  obtain ⟨P, U, hU, hborder, hrest⟩ :=
    exists_kmswStage_bound_edges32_of_open_clauses5 w n
  refine ⟨P, U, hU, hborder, ?_⟩
  intro hgeom hboundary hUL hLR hsimpleUL hsimpleLR hposition hjoin
  apply hrest hgeom hboundary hUL
  · intro M J hreal
    exact kmswStageFiniteBoundaryPresentation15_upperRight w n P U hU hborder M J hreal
  · exact hLR
  · intro M J hreal
    exact kmswStageFiniteBoundaryPresentation15_lowerLeft w n P U hU hborder M J hreal
  · exact hsimpleUL
  · exact hsimpleLR
  · exact hposition
  · exact hjoin

end DirectedDistances.PaperProofs.Section3
