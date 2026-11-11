/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Package
public import DirectedDistances.PaperProofs.Section4.UIQBOTExternalFaceIntervalOrderInstance3
public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation4
public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledPresentation3
public import DirectedDistances.PaperProofs.Section5.UIBHBOTBoundaryPresentationGeometry3
public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact3
public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Intervals5

import all DirectedDistances.PaperProofs.Section4.UIQBOTExternalFaceGeometry2

/-! Helper toward Definition 3.2: continuation of the conditional assembly package. -/

public section

namespace DirectedDistances.PaperProofs.Section4
open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the h142 UIQBOT package with proved dart
coverage instantiated; both remaining named premises are unchanged. -/
theorem exists_uiqbot_bound_edges32_of_open_clauses2
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (h_uiqbot_within_side_successor :
      let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
      let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
      ∀ i j : InfiniteBoundaryDartIndex P, sideNext P i = some j →
        uiqbotCanonicalBoundaryDartExternalSucc w hfin
            (InfiniteBoundaryDartIndex.dart P i) = InfiniteBoundaryDartIndex.dart P j ∧
        boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart P i) =
          boundaryDartInitial M (InfiniteBoundaryDartIndex.dart P j))
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
  apply exists_uiqbot_bound_edges32_of_open_clauses w hfin htrans hR hL0
    _ h_uiqbot_within_side_successor h_uiqbot_successor_classification
  intro d
  simpa only [uiqbotCanonicalBoundaryDartEquiv, Equiv.symm_symm] using
    uiqbotCanonicalBoundaryPresentationLabeledX_externalDartCoverage
      w hfin htrans hR hL0 d

end DirectedDistances.PaperProofs.Section4

namespace DirectedDistances.PaperProofs.Section3
open DirectedDistances.KMSW DirectedDistances.PlanarMap


/-- Helper toward Definition 3.2: opposite directed traversal bits separate
UL from LR, while each side's retained embedding separates its own indices. -/
theorem boundaryChanneledPresentation_dart_injective
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) :
    Function.Injective (InfiniteBoundaryDartIndex.dart
      (boundaryChanneledPresentationWithJunctions R G).presentation) := by
  let M := boundaryChanneledPlaneMap R G
  let Q := (boundaryChanneledPresentationWithJunctions R G).presentation
  have hcross (a : Fin ℓ) (b : Fin r) :
      boundaryChanneledLeftDart R G a ≠ boundaryChanneledRightDart R G b := by
    intro h
    have hl : (boundaryChanneledLeftDart R G a).2 =
        M.forward ⟨(boundaryChanneledLeftDart R G a).1,
          boundaryChanneledPlaneMap_noMissing R G _⟩ := rfl
    have hr : (boundaryChanneledRightDart R G b).2 =
        !(M.forward ⟨(boundaryChanneledRightDart R G b).1,
          boundaryChanneledPlaneMap_noMissing R G _⟩) := rfl
    rw [← h, hl] at hr
    cases hb : M.forward ⟨(boundaryChanneledLeftDart R G a).1,
      boundaryChanneledPlaneMap_noMissing R G _⟩ <;> simp [hb] at hr
  intro i j hij
  cases i <;> cases j <;> rename_i a b
  all_goals try { first
    | (change Empty at a; cases a)
    | (change Empty at b; cases b) }
  all_goals simp only [InfiniteBoundaryDartIndex.dart_eq] at hij
  case upperLeft.upperLeft =>
    exact congrArg InfiniteBoundaryDartIndex.upperLeft (Q.upperLeft.darts.injective hij)
  case lowerRight.lowerRight =>
    exact congrArg InfiniteBoundaryDartIndex.lowerRight (Q.lowerRight.darts.injective hij)
  case upperLeft.lowerRight =>
    exact (hcross a b hij).elim
  case lowerRight.upperLeft =>
    exact (hcross b a hij.symm).elim


/-- Helper toward Definition 3.2: retain the boundary-channeled conditional
package. Integer position order does not discharge cyclic successor order. -/
theorem exists_boundaryChanneled_bound_edges32_of_open_clauses2
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R)
    (h_boundary_drawing_transport :
      ∃ (rot : Equiv.Perm (G.GeometricEdge × Bool))
        (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
          (fun d => (d.1, !d.2)) rot
          (boundaryDartInitial (boundaryChanneledPlaneMap R G))),
        DrawsMap (boundaryChanneledPlaneMap R G) H)
    (h_boundary_unbounded_face :
      ∀ (rot : Equiv.Perm (G.GeometricEdge × Bool))
        (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
          (fun d => (d.1, !d.2)) rot
          (boundaryDartInitial (boundaryChanneledPlaneMap R G))),
        DrawsMap (boundaryChanneledPlaneMap R G) H → ∃ U : H.Face, H.IsUnbounded U)
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
  let M := boundaryChanneledPlaneMap R G
  let B := boundaryChanneledPresentationWithJunctions R G
  obtain ⟨rot, H, hdraw⟩ := h_boundary_drawing_transport
  obtain ⟨U, hU⟩ := h_boundary_unbounded_face rot H hdraw
  let S := fun d : G.GeometricEdge × Bool => rot.symm (d.1, !d.2)
  have hmissing := boundaryChanneledPresentation_missingRuns R G
  have hemptyLabels := boundaryChanneledPresentation_emptySideEndpointLabels R G
  refine ⟨B, rot, H, U, S, rfl, hdraw, ?_,
    boundaryChanneledPresentation_suppliedJunctionLabels R G⟩
  refine ⟨h_boundary_order, h_boundary_dart_coverage rot H U hdraw hU,
    boundaryChanneledPresentation_dart_injective R G,
    h_boundary_geometric_successor rot H U hdraw hU,
    h_boundary_upperLeft_orientation, hmissing.1,
    h_boundary_lowerRight_orientation, hmissing.2,
    h_boundary_upperLeft_simple, h_boundary_lowerRight_simple,
    h_boundary_upperLeft_endpoint_labels, hemptyLabels.1,
    h_boundary_lowerRight_endpoint_labels, hemptyLabels.2,
    h_boundary_finite_position_order rot H hdraw, ?_,
    fun _ => h_boundary_required_join_labels rot H hdraw⟩
  intro i j hij
  calc
    boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart B.presentation i) =
        boundaryDartInitial M (S (InfiniteBoundaryDartIndex.dart B.presentation i)) :=
      boundary_dart_terminal_eq_geometric_successor_initial M H _
    _ = boundaryDartInitial M (InfiniteBoundaryDartIndex.dart B.presentation j) :=
      congrArg (boundaryDartInitial M) hij



/-- Helper toward Definition 3.2: the duplicate-free stage outer word
separates all four indexed dart runs, including indices on different sides. -/
theorem kmswStageFiniteBoundaryPresentation_dart_injective
    (w : ℕ → Fin 3) (n : ℕ)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)) :
    Function.Injective (InfiniteBoundaryDartIndex.dart
      (kmswStageFiniteBoundaryPresentation w n M J)) := by
  have hword : (kmswStageULDartRun w n ++ kmswStageURDartRun w n ++
      kmswStageLRDartRun w n ++ kmswStageLLDartRun w n).Nodup := by
    simpa [stageOuterWord, kmswStageULDartRun, kmswStageURDartRun,
      kmswStageLRDartRun, kmswStageLLDartRun] using stageOuterWord_nodup w n
  simp only [List.nodup_append', List.disjoint_append_left] at hword
  rcases hword with ⟨⟨⟨hUL, hUR, hULUR⟩, hLR, hULLR, hURLR⟩,
    hLL, ⟨hULLL, hURLL⟩, hLRLL⟩
  have hne {l r : List (Fin (kmswStage w n).nextEdge × Bool)} (hd : List.Disjoint l r)
      (i : Fin l.length) (j : Fin r.length) : l[i] ≠ r[j] := by
    intro hij
    exact (List.disjoint_left.mp hd) (List.getElem_mem i.isLt)
      (hij.symm ▸ List.getElem_mem j.isLt)
  intro i j h
  cases i <;> cases j <;> rename_i a b
  all_goals simp only [InfiniteBoundaryDartIndex.dart_eq,
    kmswStageFiniteBoundaryPresentation, kmswFiniteRunSide] at h
  all_goals change Fin _ at a b
  case upperLeft.upperLeft =>
    exact congrArg InfiniteBoundaryDartIndex.upperLeft (hUL.get_inj_iff.mp h)
  case upperRight.upperRight =>
    exact congrArg InfiniteBoundaryDartIndex.upperRight (hUR.get_inj_iff.mp h)
  case lowerRight.lowerRight =>
    exact congrArg InfiniteBoundaryDartIndex.lowerRight (hLR.get_inj_iff.mp h)
  case lowerLeft.lowerLeft =>
    exact congrArg InfiniteBoundaryDartIndex.lowerLeft (hLL.get_inj_iff.mp h)
  all_goals
    exfalso
    first
    | exact hne hULUR a b h
    | exact hne hULUR.symm a b h
    | exact hne hULLR a b h
    | exact hne hULLR.symm a b h
    | exact hne hURLR a b h
    | exact hne hURLR.symm a b h
    | exact hne hULLL a b h
    | exact hne hULLL.symm a b h
    | exact hne hURLL a b h
    | exact hne hURLL.symm a b h
    | exact hne hLRLL a b h
    | exact hne hLRLL.symm a b h


/-- Helper toward Definition 3.2: retain the stage conditional package.
Within-run successor equations do not provide cyclic successor order. -/
theorem exists_kmswStage_bound_edges32_of_open_clauses2
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
    (h_stage_unbounded_face : ∃ U : P.Face, P.IsUnbounded U)
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
  obtain ⟨M, J, hreal, hulLabels, hurLabels, hlrLabels, hllLabels⟩ :=
    h_stage_map_and_junction_transport
  obtain ⟨G, himage, hfaces⟩ := DirectedDistances.PaperProofs.Section4.plDrawing_transport
    (flip' := fun d => (d.1, !d.2)) (rot' := stageRot w n)
    (vert' := boundaryDartInitial M) (Equiv.refl _) (fun _ => rfl) (fun _ => rfl)
    hreal.2.1 P
  obtain ⟨U₀, hU₀⟩ := h_stage_unbounded_face
  obtain ⟨U, hUval, hborders⟩ := hfaces U₀
  have hU : G.IsUnbounded U := by
    intro r
    obtain ⟨z, hz, hr⟩ := hU₀ r
    exact ⟨z, hUval ▸ hz, hr⟩
  let S := fun d : Fin (kmswStage w n).nextEdge × Bool =>
    (stageRot w n).symm (d.1, !d.2)
  have hgeom : IsGeometricExternalFaceSucc G U S := by
    refine ⟨hU, ?_⟩
    intro d hd
    have hs := (h_stage_geometric_successor U₀ hU₀).2 d ((hborders d).mp hd)
    exact ⟨hs.1, (hborders (S d)).mpr hs.2⟩
  let B := kmswStageFiniteBoundaryPresentationWithJunctions w n M J
  refine ⟨M, J, B, stageRot w n, G, U, S, hreal, rfl, himage, ?_⟩
  apply (IsBoundEdges32.finite_iff (Set.toFinite _)).mpr
  refine ⟨?_, kmswStage_finite_boundary_supplied_junction_labels w n M J⟩
  refine ⟨h_stage_boundary_order M J hreal,
    (fun d => (hborders d).trans (h_stage_dart_coverage M J U₀ hreal hU₀ d)),
    kmswStageFiniteBoundaryPresentation_dart_injective w n M J, hgeom,
    h_stage_upperLeft_orientation M J hreal, h_stage_upperRight_missing_run M J hreal,
    h_stage_lowerRight_orientation M J hreal, h_stage_lowerLeft_missing_run M J hreal,
    h_stage_upperLeft_simple M J hreal, h_stage_lowerRight_simple M J hreal,
    hulLabels, hurLabels, hlrLabels, hllLabels,
    h_stage_finite_position_order M J hreal, ?_,
    fun _ => h_stage_required_join_labels M J hreal hulLabels hurLabels hlrLabels hllLabels⟩
  intro i j hij
  exact (boundary_dart_terminal_eq_geometric_successor_initial M G _).trans
    (congrArg (boundaryDartInitial M) hij)

end DirectedDistances.PaperProofs.Section3

namespace DirectedDistances.PaperProofs.Section5
open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.SourceResults

/-- Helper toward Definition 3.2: integer order of the sole bi-infinite
lower-left side; no external-face identification is asserted. -/
theorem uibhbotDefinition32Presentation_positionOrder3
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
  (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
  (hfin : KMSWFiniteIncidence (kmswPastCode W))
  (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
  (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
    (uibhbotPastMonotoneDrawing W hfin).pos)
  (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
    ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
  (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (shiftedStream W 0) (H.1 0))
    (kmswLimitDartVertex (shiftedStream W 0)))
  (hf : F.pos = uibhbotSeparationFuturePos W H h0)
  (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})
  (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0)
    h0 (H.1 0) '' ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all _)).arc d).image)
  (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e) :
    BoundaryPositionOrder3 (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj) := by
  rw [uibhbotDefinition32Presentation_eq W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj]
  refine ⟨fun i => ?_, ?_⟩
  ·
    cases i with
    | upperLeft i => exact isEmptyElim i
    | upperRight i => exact isEmptyElim i
    | lowerRight i => exact isEmptyElim i
    | lowerLeft i => exact i
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      cases i <;> cases j <;> rename_i a b
      all_goals try { first
        | (change Empty at a; cases a)
        | (change Empty at b; cases b) }
      exact congrArg InfiniteBoundaryDartIndex.lowerLeft hij
    · intro i j htag
      cases i <;> cases j <;> rename_i a b
      all_goals try { first
        | (change Empty at a; cases a)
        | (change Empty at b; cases b) }
      simp [sideNext, eq_comm]
    · intro i j z hiz hzj
      exact ⟨.lowerLeft z, rfl⟩
    · intro i j k hij hjk htag
      cases i <;> cases j <;> cases k <;> rename_i a b c
      all_goals try { first
        | (change Empty at a; cases a)
        | (change Empty at b; cases b)
        | (change Empty at c; cases c) }
      rfl
    · intro i j k hij hjk htag
      cases i <;> cases j <;> cases k <;> rename_i a b c
      all_goals try { first
        | (change Empty at a; cases a)
        | (change Empty at b; cases b)
        | (change Empty at c; cases c) }
      exact (htag rfl).elim



/-- Helper toward Definition 3.2: every currently listed UIBHBOT dart pulls
back to a false whole-plane traversal bit under the corrected transport.
This calculation identifies a presentation/geometry compatibility obstruction. -/
theorem uibhbotDefinition32Presentation_adjusted_inverse_bit
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
  (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
  (hfin : KMSWFiniteIncidence (kmswPastCode W))
  (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
  (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
    (uibhbotPastMonotoneDrawing W hfin).pos)
  (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
    ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
  (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (shiftedStream W 0) (H.1 0))
    (kmswLimitDartVertex (shiftedStream W 0)))
  (hf : F.pos = uibhbotSeparationFuturePos W H h0)
  (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})
  (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0)
    h0 (H.1 0) '' ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all _)).arc d).image)
  (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e) :
    ∀ i : InfiniteBoundaryDartIndex (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj),
      ((uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa).symm
        (InfiniteBoundaryDartIndex.dart
          (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj) i)).2 = false := by
  rw [uibhbotDefinition32Presentation_eq W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj]
  intro i
  cases i with
  | upperLeft i => cases i
  | upperRight i => cases i
  | lowerRight i => cases i
  | lowerLeft k =>
    let q := Quotient.mk
      (uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa).edgeSetoid (e k, true)
    simp only [InfiniteBoundaryDartIndex.dart_eq, uibhbotAssemblyBoundaryDartEquiv3,
      Equiv.symm_trans_apply, uibhbotAssemblyBoundaryDartAdjust,
      uibhbotAssemblyBoundaryDartEquiv]
    change (!(if q.out.2 then !!q.out.2 else !q.out.2)) = false
    cases hb : q.out.2 <;> simp



/-- Helper toward Definition 3.2: the indexed coverage clause required to
combine the unchanged presentation with Geometry3 is false. This is an exact -/
theorem uibhbotDefinition32Presentation_not_adjusted_externalDartCoverage
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
  (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
  (hfin : KMSWFiniteIncidence (kmswPastCode W))
  (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
  (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
    (uibhbotPastMonotoneDrawing W hfin).pos)
  (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
    ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
  (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (shiftedStream W 0) (H.1 0))
    (kmswLimitDartVertex (shiftedStream W 0)))
  (hf : F.pos = uibhbotSeparationFuturePos W H h0)
  (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})
  (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0)
    h0 (H.1 0) '' ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all _)).arc d).image)
  (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e) :
    ¬ (∀ d,
      (((uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa).symm d).2 = true ∧
        ¬ wholePlaneEdgePresent W
          ((uibhbotAssemblyBoundaryDartEquiv3 W H h0 hL hR hfin P hp ha F hf hFim hFa).symm d).1) ↔
      ∃ i : InfiniteBoundaryDartIndex (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj),
        InfiniteBoundaryDartIndex.dart (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj) i = d) := by
  intro hcover
  have hi : Nonempty (InfiniteBoundaryDartIndex
      (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj)) := by
    rw [uibhbotDefinition32Presentation_eq W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj]
    exact ⟨.lowerLeft 0⟩
  obtain ⟨i⟩ := hi
  have ht := (hcover _).mpr ⟨i, rfl⟩
  have hbit := uibhbotDefinition32Presentation_adjusted_inverse_bit W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj i
  rw [hbit] at ht
  exact Bool.false_ne_true ht.1






















































end DirectedDistances.PaperProofs.Section5

/- Premise -> status table. All paths are relative to DirectedDistances/.
The source-domain premises w/hfin/htrans/hR/hL0, R/G and w/n/P are unchanged.

h_uiqbot_dart_border_coverage -> DISCHARGED by
  PaperProofs/Section4/UIQBOTExternalFaceIntervalOrderInstance2.lean:28,
  instantiated at PlanarMap/BoundEdgesDefinition32Package2.lean:65.
h_boundary_dart_injective -> DISCHARGED by PlanarMap/BoundEdgesDefinition32Package2.lean:80.
h_stage_dart_injective -> DISCHARGED by PlanarMap/BoundEdgesDefinition32Package2.lean:220.
h_uiqbot_within_side_successor -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:36.
h_uiqbot_successor_classification -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:44.
h_boundary_drawing_transport -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:118.
h_boundary_unbounded_face -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:124.
h_boundary_dart_coverage -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:130.
h_boundary_geometric_successor -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:140.
h_boundary_order -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:147.
h_boundary_upperLeft_orientation -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:149.
h_boundary_lowerRight_orientation -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:151.
h_boundary_upperLeft_simple -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:153.
h_boundary_lowerRight_simple -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:155.
h_boundary_upperLeft_endpoint_labels -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:157.
h_boundary_lowerRight_endpoint_labels -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:160.
h_boundary_finite_position_order -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:163.
h_boundary_required_join_labels -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:172.
h_stage_map_and_junction_transport -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:273.
h_stage_unbounded_face -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:282.
h_stage_dart_coverage -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:283.
h_stage_geometric_successor -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:291.
h_stage_boundary_order -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:294.
h_stage_upperLeft_orientation -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:300.
h_stage_upperRight_missing_run -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:306.
h_stage_lowerRight_orientation -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:312.
h_stage_lowerLeft_missing_run -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:318.
h_stage_upperLeft_simple -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:324.
h_stage_lowerRight_simple -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:330.
h_stage_finite_position_order -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:336.
h_stage_required_join_labels -> OPEN at PlanarMap/BoundEdgesDefinition32Package2.lean:343.

UIBHBOT geometric drawing/face/successor -> DISCHARGED by
  PaperProofs/Section5/UIBHBOTBoundaryPresentationGeometry3.lean:166.
UIBHBOT integer position order -> DISCHARGED by PlanarMap/BoundEdgesDefinition32Package2.lean:410.
UIBHBOT presentation/Geometry3 compatibility -> OPEN at
  PlanarMap/BoundEdgesDefinition32Package2.lean:522;
  the proposed fixed-transport coverage clause is REFUTED there.
UIBHBOT complete a.s. package -> OPEN at
  PlanarMap/BoundEdgesDefinition32Package2.lean:573;

Three routes for each remaining group were checked:
UIQBOT successor clauses: (1) canonical KMSW ray equations transported by the
dart equivalence; (2) geometric successor plus proved coverage; (3) stopped
root-join classification. The first still needs the labeled-index reduction,
the second yields total succession but not sideNext identification, and the
third does not classify arbitrary within-side successor pairs.
Boundary-channeled geometric/order clauses: (1) original drawing-to-map
transport, (2) the combinatorial outer-word decomposition, (3) the geometric
rotation successor. None supplies the missing external-face identification on
the transported carrier. Side/endpoint clauses: (1) directed path edge_step,
(2) reversed right-path endpoint reindexing, (3) retained junction labels.
The new join proofs do not supply LeftOf/RightOf or vertex-occurrence
simplicity, and supplied labels do not themselves prove endpoint validity.
Cyclic order/join labels: (1) BoundaryChanneledPresentation3's positionOrder3,
(2) direct finite side reindexing, (3) outer-word successor transport. Integer
positions do not identify the arbitrary transported rot, and exact geometric
cyclic succession and required closing labels remain absent.
Stage geometry/order: (1) StageDrawing on edge IDs, (2) its quotient plane
drawing, (3) Prop516StageDrawingRepresentation4's exterior-face theorem.
The last constructs one drawing, whereas the retained hypotheses quantify
over the supplied arbitrary P; neither of the first two constructs the
required map/junction realization. Stage side/endpoint clauses: (1) the
four-run chain invariant, (2) the four within-run faceSucc theorems in
KMSWFiniteBoundaryPresentation4, (3) endpoint transport through realization32.
These do not prove LeftOf/RightOf or all missing-run vertex joins on an
arbitrary supplied map. Stage cyclic order/required labels: (1) the proved
integer position order, (2) the cyclic outer-word permutation, (3) the retained
junction tuple. The integer and within-run facts do not export the complete
cyclic Fin equivalence with geometric successor, and the tuple alone does not
prove its endpoint validity. None of these open clauses is silently dropped.
SidesExact3 and Intervals5 do not discharge the retained existence premises:
their local side and finite orbit results require a preexisting IsBoundEdges32.

Full binders of every remaining named open statement follow. These are

h_uiqbot_within_side_successor :
  ∀ (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j),

      let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
      let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
      ∀ i j : InfiniteBoundaryDartIndex P, sideNext P i = some j →
        uiqbotCanonicalBoundaryDartExternalSucc w hfin
            (InfiniteBoundaryDartIndex.dart P i) = InfiniteBoundaryDartIndex.dart P j ∧
        boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart P i) =
          boundaryDartInitial M (InfiniteBoundaryDartIndex.dart P j)

h_uiqbot_successor_classification :
  ∀ (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j),

      let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
      let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
      ∀ i j : InfiniteBoundaryDartIndex P,
        uiqbotCanonicalBoundaryDartExternalSucc w hfin
            (InfiniteBoundaryDartIndex.dart P i) = InfiniteBoundaryDartIndex.dart P j →
        sideNext P i = some j ∨
          (sideNext P i = none ∧ firstOnSide P j ∧
            nextNonemptySide P (sideTag P i) (sideTag P j) ∧
            boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart P i) =
              boundaryDartInitial M (InfiniteBoundaryDartIndex.dart P j))

h_boundary_drawing_transport :
  ∀ {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R),

      ∃ (rot : Equiv.Perm (G.GeometricEdge × Bool))
        (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
          (fun d => (d.1, !d.2)) rot
          (boundaryDartInitial (boundaryChanneledPlaneMap R G))),
        DrawsMap (boundaryChanneledPlaneMap R G) H

h_boundary_unbounded_face :
  ∀ {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R),

      ∀ (rot : Equiv.Perm (G.GeometricEdge × Bool))
        (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
          (fun d => (d.1, !d.2)) rot
          (boundaryDartInitial (boundaryChanneledPlaneMap R G))),
        DrawsMap (boundaryChanneledPlaneMap R G) H → ∃ U : H.Face, H.IsUnbounded U

h_boundary_dart_coverage :
  ∀ {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R),

      ∀ (rot : Equiv.Perm (G.GeometricEdge × Bool))
        (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
          (fun d => (d.1, !d.2)) rot
          (boundaryDartInitial (boundaryChanneledPlaneMap R G))) (U : H.Face),
        DrawsMap (boundaryChanneledPlaneMap R G) H → H.IsUnbounded U →
        ∀ d, H.dartBorders d U ↔ ∃ i : InfiniteBoundaryDartIndex
            (boundaryChanneledPresentationWithJunctions R G).presentation,
          InfiniteBoundaryDartIndex.dart
            (boundaryChanneledPresentationWithJunctions R G).presentation i = d

h_boundary_geometric_successor :
  ∀ {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R),

      ∀ (rot : Equiv.Perm (G.GeometricEdge × Bool))
        (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
          (fun d => (d.1, !d.2)) rot
          (boundaryDartInitial (boundaryChanneledPlaneMap R G))) (U : H.Face),
        DrawsMap (boundaryChanneledPlaneMap R G) H → H.IsUnbounded U →
        IsGeometricExternalFaceSucc H U (fun d => rot.symm (d.1, !d.2))

h_boundary_order :
  ∀ {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R),
 IsBoundaryOrderOfInf (boundaryChanneledPlaneMap R G)
      (boundaryChanneledPresentationWithJunctions R G).presentation

h_boundary_upperLeft_orientation :
  ∀ {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R),

      ULOkInf (boundaryChanneledPresentationWithJunctions R G).presentation

h_boundary_lowerRight_orientation :
  ∀ {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R),

      LROkInf (boundaryChanneledPresentationWithJunctions R G).presentation

h_boundary_upperLeft_simple :
  ∀ {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R),
 IsSimpleBoundarySide (boundaryChanneledPlaneMap R G)
      (boundaryChanneledPresentationWithJunctions R G).presentation.upperLeft

h_boundary_lowerRight_simple :
  ∀ {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R),
 IsSimpleBoundarySide (boundaryChanneledPlaneMap R G)
      (boundaryChanneledPresentationWithJunctions R G).presentation.lowerRight

h_boundary_upperLeft_endpoint_labels :
  ∀ {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R),

      BoundarySideEndpointLabels (boundaryChanneledPlaneMap R G)
        (boundaryChanneledPresentationWithJunctions R G).presentation.upperLeft

h_boundary_lowerRight_endpoint_labels :
  ∀ {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R),

      BoundarySideEndpointLabels (boundaryChanneledPlaneMap R G)
        (boundaryChanneledPresentationWithJunctions R G).presentation.lowerRight

h_boundary_finite_position_order :
  ∀ {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R),

      ∀ (rot : Equiv.Perm (G.GeometricEdge × Bool))
        (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
          (fun d => (d.1, !d.2)) rot
          (boundaryDartInitial (boundaryChanneledPlaneMap R G))),
        DrawsMap (boundaryChanneledPlaneMap R G) H →
        FiniteBoundaryPositionOrder4
          (boundaryChanneledPresentationWithJunctions R G).presentation
          (fun d => rot.symm (d.1, !d.2))

h_boundary_required_join_labels :
  ∀ {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R),

      ∀ (rot : Equiv.Perm (G.GeometricEdge × Bool))
        (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
          (fun d => (d.1, !d.2)) rot
          (boundaryDartInitial (boundaryChanneledPlaneMap R G))),
        DrawsMap (boundaryChanneledPlaneMap R G) H →
        RequiredFiniteBoundaryJoinEndpointLabels7
          (boundaryChanneledPresentationWithJunctions R G).presentation
          (fun d => rot.symm (d.1, !d.2))

h_stage_map_and_junction_transport :
  ∀ (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n),

      ∃ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M ∧
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).upperLeft ∧
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).upperRight ∧
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).lowerRight ∧
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).lowerLeft

h_stage_unbounded_face :
  ∀ (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n),
 ∃ U : P.Face, P.IsUnbounded U

h_stage_dart_coverage :
  ∀ (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n),

      ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)) (U : P.Face),
        kmsw_stage_map_realization32 w n P M → P.IsUnbounded U →
        ∀ d, P.dartBorders d U ↔ ∃ i : InfiniteBoundaryDartIndex
          (kmswStageFiniteBoundaryPresentation w n M J),
          InfiniteBoundaryDartIndex.dart (kmswStageFiniteBoundaryPresentation w n M J) i = d

h_stage_geometric_successor :
  ∀ (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n),
 ∀ U : P.Face, P.IsUnbounded U →
      IsGeometricExternalFaceSucc P U
        (fun d => (stageRot w n).symm (d.1, !d.2))

h_stage_boundary_order :
  ∀ (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n),

      ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M →
        IsBoundaryOrderOfInf M (kmswStageFiniteBoundaryPresentation w n M J)

h_stage_upperLeft_orientation :
  ∀ (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n),

      ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M →
        ULOkInf (kmswStageFiniteBoundaryPresentation w n M J)

h_stage_upperRight_missing_run :
  ∀ (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n),

      ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M →
        UROkInf (kmswStageFiniteBoundaryPresentation w n M J)

h_stage_lowerRight_orientation :
  ∀ (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n),

      ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M →
        LROkInf (kmswStageFiniteBoundaryPresentation w n M J)

h_stage_lowerLeft_missing_run :
  ∀ (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n),

      ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M →
        LLOkInf (kmswStageFiniteBoundaryPresentation w n M J)

h_stage_upperLeft_simple :
  ∀ (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n),

      ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M → IsSimpleBoundarySide M
          (kmswStageFiniteBoundaryPresentation w n M J).upperLeft

h_stage_lowerRight_simple :
  ∀ (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n),

      ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M → IsSimpleBoundarySide M
          (kmswStageFiniteBoundaryPresentation w n M J).lowerRight

h_stage_finite_position_order :
  ∀ (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n),

      ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M →
        FiniteBoundaryPositionOrder4 (kmswStageFiniteBoundaryPresentation w n M J)
          (fun d => (stageRot w n).symm (d.1, !d.2))

h_stage_required_join_labels :
  ∀ (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n),

      ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M →
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).upperLeft →
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).upperRight →
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).lowerRight →
        BoundarySideEndpointLabels M (kmswStageFiniteBoundaryPresentation w n M J).lowerLeft →
        RequiredFiniteBoundaryJoinEndpointLabels7 (kmswStageFiniteBoundaryPresentation w n M J)
          (fun d => (stageRot w n).symm (d.1, !d.2)) -/


