/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32
public import DirectedDistances.PlanarMap.BoundEdgesMapDrawingBridge32
public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact2
public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Intervals4
public import DirectedDistances.PaperProofs.Section4.UIQBOTExternalFaceIntervalOrderInstance
public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation2
public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledPresentation2
public import DirectedDistances.PaperProofs.Section5.UIBHBOTBoundaryPresentationGeometry2

import all DirectedDistances.PaperProofs.Section4.UIQBOTExternalFaceGeometry2

/-! conditional packaging only. The provider assumes the supplied v7 certificate;
it does not prove construction compatibility or identify all PL path sides. -/

public section

namespace DirectedDistances.PlanarMap

universe uV uE uUL uUR uLR uLL




theorem bound_edges_provider_of_isBoundEdges32
    {V : Type uV} {E : Type uE}
    (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (U : G.Face) (S : E × Bool → E × Bool)
    (h : IsBoundEdges32 M B G U S) :
    (∀ d, G.dartBorders d U ↔
      ∃ i : InfiniteBoundaryDartIndex B.presentation,
        InfiniteBoundaryDartIndex.dart B.presentation i = d) ∧
    ULOkInf B.presentation ∧ UROkInf B.presentation ∧
    LROkInf B.presentation ∧ LLOkInf B.presentation ∧
    IsSimpleBoundarySide M B.presentation.upperLeft ∧
    IsSimpleBoundarySide M B.presentation.lowerRight ∧
    BoundarySideEndpointLabels M B.presentation.upperLeft ∧
    BoundarySideEndpointLabels M B.presentation.upperRight ∧
    BoundarySideEndpointLabels M B.presentation.lowerRight ∧
    BoundarySideEndpointLabels M B.presentation.lowerLeft ∧
    (∀ e, e ∈ upperLeftBoundary32 B ↔
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        G.dartBorders (e, M.forward ⟨e, hp⟩) U) ∧
    (∀ e, e ∈ lowerRightBoundary32 B ↔
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        G.dartBorders (e, !(M.forward ⟨e, hp⟩)) U) ∧
    (∀ e, e ∈ upperRightBoundary32 B ↔
      ∃ i : B.presentation.upperRight.Index,
        (B.presentation.upperRight.darts i).1 = e ∧
          M.toPlaneMapWithMissing.missing e) ∧
    (∀ e, e ∈ lowerLeftBoundary32 B ↔
      ∃ i : B.presentation.lowerLeft.Index,
        (B.presentation.lowerLeft.darts i).1 = e ∧
          M.toPlaneMapWithMissing.missing e) := by
  rcases h.presentation_facts with ⟨hc, hul, hur, hlr, hll, hsul, hslr⟩
  rcases h.endpoint_labels with ⟨helul, helur, hellr, helll⟩
  exact ⟨hc, hul, hur, hlr, hll, hsul, hslr, helul, helur, hellr, helll,
    mem_upperLeftBoundary32_iff_forward_dartBorders h,
    mem_lowerRightBoundary32_iff_reverse_dartBorders h,
    mem_upperRightBoundary32_iff_missing_run h,
    mem_lowerLeftBoundary32_iff_missing_run h⟩

/-- Helper toward Definition 3.2: rotation preserves the initial vertex, so
the geometric successor joins the incoming dart's terminal vertex. -/
theorem boundary_dart_terminal_eq_geometric_successor_initial
    {V : Type uV} {E : Type uE} (M : DirectedPlaneMapWithMissing V E)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)) (d : E × Bool) :
    boundaryDartTerminal M d =
      boundaryDartInitial M (rot.symm (d.1, !d.2)) := by
  have hv := G.vert_rotation (rot.symm (d.1, !d.2))
  rw [Equiv.apply_symm_apply] at hv
  calc
    boundaryDartTerminal M d = boundaryDartInitial M (d.1, !d.2) := by
      rw [boundaryDartTerminal_eq, boundaryDartInitial_eq]
      cases d.2 <;> rfl
    _ = boundaryDartInitial M (rot.symm (d.1, !d.2)) := hv

end DirectedDistances.PlanarMap

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: assemble the canonical UIQBOT presentation
and an actual quotient drawing, conditional on three outstanding clauses.
Every open premise is displayed separately; none is a v3 or v7 certificate. -/
theorem exists_uiqbot_bound_edges32_of_open_clauses
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (h_uiqbot_dart_border_coverage :
      ∀ d : (uiqbotPresentationDrawing w hfin).GeometricEdge × Bool,
        limitExternalDart w ((uiqbotCanonicalBoundaryDartEquiv w hfin).symm d) ↔
          ∃ i : InfiniteBoundaryDartIndex
              (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0),
            InfiniteBoundaryDartIndex.dart
              (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0) i = d)
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
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let B := uiqbotCanonicalBoundaryPresentationLabeledXWithJunctions w hfin htrans hR hL0
  let e := uiqbotCanonicalBoundaryDartEquiv w hfin
  let rot := uiqbotTransportRotation e.symm (kmswInfRot w hfin)
  let S := uiqbotCanonicalBoundaryDartExternalSucc w hfin
  obtain ⟨G, U, _hU, hborder, hgeom⟩ :=
    uiqbotCanonicalQuotientDrawing_externalFace w hfin htrans hR hL0
  have hS : S = (fun d => e (kmswInfFaceSucc w hfin (e.symm d))) := by
    funext d
    simpa only [S, e, uiqbotCanonicalBoundaryDartEquiv, Equiv.symm_symm] using
      uiqbotCanonicalBoundaryDartExternalSucc_transport w hfin d
  have hgeom' : IsGeometricExternalFaceSucc G U S := by
    rw [hS]
    exact hgeom
  have htotal : ∀ i : InfiniteBoundaryDartIndex P,
      ∃ j : InfiniteBoundaryDartIndex P,
        S (InfiniteBoundaryDartIndex.dart P i) = InfiniteBoundaryDartIndex.dart P j := by
    intro i
    have hcover (d) := (hborder d).trans (h_uiqbot_dart_border_coverage d)
    have hi : G.dartBorders (InfiniteBoundaryDartIndex.dart P i) U :=
      (hcover _).mpr ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := (hcover _).mp (hgeom'.2 _ hi).2
    exact ⟨j, hj.symm⟩
  refine ⟨B, rot, G, U, S, rfl, rfl, ?_⟩
  apply (uiqbotCanonicalBoundaryPresentationLabeledX_externalFaceIntervalOrder7_iff
    w hfin htrans hR hL0 G U S).mpr
  refine ⟨⟨⟨uiqbotLabeledPresentationX_isBoundaryOrderOfInf w hfin htrans hR hL0,
    (fun d => (hborder d).trans (h_uiqbot_dart_border_coverage d)),
    hgeom', h_uiqbot_within_side_successor, htotal,
    h_uiqbot_successor_classification⟩,
    uiqbotCanonicalBoundaryPresentationLabeledX_ULOkInf w hfin htrans hR hL0,
    uiqbotCanonicalBoundaryPresentationLabeledX_UROkInf w hfin htrans hR hL0,
    uiqbotCanonicalBoundaryPresentationLabeledX_LROkInf w hfin htrans hR hL0,
    uiqbotCanonicalBoundaryPresentationLabeledX_LLOkInf w hfin htrans hR hL0,
    uiqbotCanonicalBoundaryPresentationLabeledX_upperLeftSimple w hfin htrans hR hL0,
    uiqbotCanonicalBoundaryPresentationLabeledX_lowerRightSimple w hfin htrans hR hL0,
    uiqbotCanonicalBoundaryPresentationLabeledX_upperLeftEndpointLabels
      w hfin htrans hR hL0,
    uiqbotCanonicalBoundaryPresentationLabeledX_upperRightEndpointLabels
      w hfin htrans hR hL0,
    uiqbotCanonicalBoundaryPresentationLabeledX_lowerRightEndpointLabels
      w hfin htrans hR hL0,
    uiqbotCanonicalBoundaryPresentationLabeledX_lowerLeftEndpointLabels
      w hfin htrans hR hL0,
    uiqbotCanonicalBoundaryPresentationLabeledX_BoundaryJoinEndpointLabels
      w hfin htrans hR hL0⟩,
    uiqbotCanonicalBoundaryPresentationLabeledX_positionOrder3 w hfin htrans hR hL0,
    uiqbotCanonicalBoundaryPresentationLabeledX_requiredJoinLabels_Y
      w hfin htrans hR hL0⟩

end DirectedDistances.PaperProofs.Section4

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: finite boundary-channeled assembly from
separately displayed open clauses. The drawing transport and geometric face
claims remain premises, and no construction compatibility is counted. -/
theorem exists_boundaryChanneled_bound_edges32_of_open_clauses
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
    (h_boundary_dart_injective : Function.Injective (InfiniteBoundaryDartIndex.dart
      (boundaryChanneledPresentationWithJunctions R G).presentation))
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
    h_boundary_dart_injective, h_boundary_geometric_successor rot H U hdraw hU,
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

end DirectedDistances.PaperProofs.Section3

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: explicit geometric identification of a
supplied finite-stage plane map with its stage drawing. This relation retains
the allocated edge IDs, both traversal endpoints, missingness and orientation;
it asserts no boundary presentation or interval-order conclusion. -/
@[expose] def kmsw_stage_map_realization32 (w : ℕ → Fin 3) (n : ℕ)
    (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge)) : Prop :=
  M.toPlaneMapWithMissing.pos = P.pos ∧
  (∀ d, boundaryDartInitial M d = stageVertex w n d) ∧
  (∀ d, Set.range (M.toPlaneMapWithMissing.arc d.1) = Set.range (P.arc d).toPath) ∧
  (∀ e, M.toPlaneMapWithMissing.missing e ↔
    (kmswStageDirectedMap w n).missing (e, false)) ∧
  (∀ (e : Fin (kmswStage w n).nextEdge)
    (hp : ¬ M.toPlaneMapWithMissing.missing e), M.forward ⟨e, hp⟩ = false)

/-- Helper toward Definition 3.2: assemble finite-stage v7, conditional on
the source map/junction transport and each remaining named open clause.
The PL drawing is transported from the supplied stage drawing in the proof. -/
theorem exists_kmswStage_bound_edges32_of_open_clauses
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
    (h_stage_dart_injective :
      ∀ (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
          (Fin (kmswStage w n).nextEdge))
        (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)),
        kmsw_stage_map_realization32 w n P M → Function.Injective
          (InfiniteBoundaryDartIndex.dart (kmswStageFiniteBoundaryPresentation w n M J)))
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
    h_stage_dart_injective M J hreal, hgeom,
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


















































































































































