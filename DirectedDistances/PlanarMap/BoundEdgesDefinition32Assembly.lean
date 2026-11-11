/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Package
public import DirectedDistances.PaperProofs.Section4.UIQBOTSuccessorClassification
public import DirectedDistances.PaperProofs.Section5.UIBHBOTBoundaryOrientation6
public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation28
public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry22
public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Package3

/-! assembly covers the supplied four-side convention and its alternation/type
clauses through the retained `IsBoundEdges32` certificate; it also exposes
external-dart coverage, all four side predicates, simplicity of the present
upper-left/lower-right sides, endpoint labels for all four sides, and the four
boundary-set characterizations. For boundary-channeled maps these conclusions
retain the named open inputs below.

Not covered here: a provider for every oriented map with missing edges; the
identification of the drawing's dart-border predicate with all map-face or
winding-side characterizations; or the bipolar no-missing left/right naming
convention. This is a construction assembly, not a paper-completion claim. -/

public section

namespace DirectedDistances.PlanarMap

open DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4
open DirectedDistances.PaperProofs.Section5
open MeasureTheory
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.RandomWalk

/-- Helper toward Definition 3.2: assemble the UIQBOT supplied presentation,
its `IsBoundEdges32` witness, and every clause exposed by the provider. -/
theorem uiqbotBoundEdgesDefinition32Assembly
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    ∃ (B : BoundaryPresentationWithJunctions M)
      (rot : Equiv.Perm ((uiqbotPresentationDrawing w hfin).GeometricEdge × Bool))
      (G : PLDrawing ((uiqbotPresentationDrawing w hfin).GeometricEdge × Bool) ℕ
        (fun d => (d.1, !d.2)) rot (boundaryDartInitial M))
      (U : G.Face) (S : (uiqbotPresentationDrawing w hfin).GeometricEdge × Bool →
        (uiqbotPresentationDrawing w hfin).GeometricEdge × Bool),
      B = uiqbotCanonicalBoundaryPresentationLabeledXWithJunctions
        w hfin htrans hR hL0 ∧ B.finiteJunctions? = none ∧
        IsBoundEdges32 M B G U S ∧
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
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  rcases exists_uiqbot_bound_edges32 w hfin htrans hR hL0 with
    ⟨B, rot, G, U, S, hB, hnone, h32⟩
  exact ⟨B, rot, G, U, S, hB, hnone, h32,
    bound_edges_provider_of_isBoundEdges32 M B G U S h32⟩

/-- Helper toward Definition 3.2: almost surely assemble the reversed UIBHBOT
presentation, the original `IsBoundEdges32` witness, and every provider clause. -/
theorem ae_uibhbotBoundEdgesDefinition32Assembly :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ (H : WholePlaneRotationHypothesis W)
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
        (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e),
        let M := uibhbotAssemblyDirectedPlaneMapWithMissing
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
        let Q := uibhbotDefinition32ReversedPresentation W H h0 hL hR hfin
          P hp ha F hf hFim hFa hRpos e hinj
        let G₀ := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
        (∀ k : ℤ, wholePlaneEdgeWest W (e k) = (uibhbotBusemannSource k W).id ∧
          wholePlaneEdgeEast W (e k) = (uibhbotBusemannSource (k + 1) W).id ∧
          ¬ wholePlaneEdgePresent W (e k)) ∧
        ∃ (B : BoundaryPresentationWithJunctions M)
          (rot : Equiv.Perm (G₀.GeometricEdge × Bool))
          (G : PLDrawing (G₀.GeometricEdge × Bool) (WholePlaneVertex W)
            (fun d => (d.1, !d.2)) rot (boundaryDartInitial M))
          (U : G.Face) (S : G₀.GeometricEdge × Bool → G₀.GeometricEdge × Bool),
          B = ⟨Q, none⟩ ∧ B.finiteJunctions? = none ∧ IsBoundEdges32 M B G U S ∧
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
  filter_upwards [ae_exists_uibhbot_bound_edges32] with W hW
  rcases hW with ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa,
    hRpos, e, hinj, hsource, B, rot, G, U, S, hB, hnone, h32⟩
  let M := uibhbotAssemblyDirectedPlaneMapWithMissing
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  exact ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa,
    hRpos, e, hinj, hsource, B, rot, G, U, S, hB, hnone, h32,
    bound_edges_provider_of_isBoundEdges32 M B G U S h32⟩

/-- Helper toward Definition 3.2: assemble each KMSW finite-stage supplied
presentation, its `IsBoundEdges32` witness, and every provider clause. -/
theorem kmswStageBoundEdgesDefinition32Assembly (w : ℕ → Fin 3) (n : ℕ) :
    ∃ (P : StageDrawing w n) (U : P.Face)
      (_hU : P.IsUnbounded U)
      (_hborder : ∀ d, P.dartBorders d U ↔
        (kmswStageDirectedMap w n).IsOuter d),
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
      G.image = P.image ∧ IsBoundEdges32 M B G U S ∧
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
  rcases exists_kmswStage_bound_edges32 w n with
    ⟨P, U₀, hU, hborder, M, J, B, rot, G, U₁, S,
      hreal, hB, himage, h32⟩
  exact ⟨P, U₀, hU, hborder, M, J, B, rot, G, U₁, S,
    hreal, hB, himage, h32,
    bound_edges_provider_of_isBoundEdges32 M B G U₁ S h32⟩





theorem boundaryChanneledBoundEdgesDefinition32Assembly
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G))
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
      IsBoundEdges32 M B H U S ∧
      (∀ d, H.dartBorders d U ↔
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
          H.dartBorders (e, M.forward ⟨e, hp⟩) U) ∧
      (∀ e, e ∈ lowerRightBoundary32 B ↔
        ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
          H.dartBorders (e, !(M.forward ⟨e, hp⟩)) U) ∧
      (∀ e, e ∈ upperRightBoundary32 B ↔
        ∃ i : B.presentation.upperRight.Index,
          (B.presentation.upperRight.darts i).1 = e ∧
            M.toPlaneMapWithMissing.missing e) ∧
      (∀ e, e ∈ lowerLeftBoundary32 B ↔
        ∃ i : B.presentation.lowerLeft.Index,
          (B.presentation.lowerLeft.darts i).1 = e ∧
            M.toPlaneMapWithMissing.missing e) := by
  let M := boundaryChanneledPlaneMap R G
  have hOrient := boundaryChanneledPresentation_infiniteSideClauses22
    R G hOuterUnbounded
  rcases exists_boundaryChanneled_bound_edges32_of_open_clauses3
      R G h_boundary_drawing_transport h_boundary_dart_coverage
      h_boundary_geometric_successor h_boundary_order hOrient.1 hOrient.2
      h_boundary_upperLeft_simple h_boundary_lowerRight_simple
      h_boundary_upperLeft_endpoint_labels h_boundary_lowerRight_endpoint_labels
      h_boundary_finite_position_order h_boundary_required_join_labels with
    ⟨B, rot, H, U, S, hB, hdraw, hv7⟩
  have h32 : IsBoundEdges32 M B H U S := by
    have hFinite : (externalBoundaryDartSet4 M).Finite := by
      apply (externalBoundaryDartSet4_finite_iff M).2
      exact Set.toFinite _
    exact (IsBoundEdges32.finite_iff hFinite).2 hv7
  exact ⟨B, rot, H, U, S, hB, hdraw, h32,
    bound_edges_provider_of_isBoundEdges32 M B H U S h32⟩

end DirectedDistances.PlanarMap

end
