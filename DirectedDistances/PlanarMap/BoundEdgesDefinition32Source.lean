/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Assembly
public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Part1
public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Part2
public import DirectedDistances.PlanarMap.BoundEdgesDefinition32LeftRight
public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledPart2
public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry25

/-! Construction-specific assembly under the supplied-presentation and empty-path
rulings. The predicates below abbreviate conclusions, never extra premises of
the sole coordinator. No numbered-result or paper-completion claim is made. -/

public section

namespace DirectedDistances.PlanarMap

open unitInterval MeasureTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk

universe uV uE uUL uUR uLR uLL uI

/-- Helper toward Definition 3.2: a consecutive, possibly empty or unbounded
missing run, with geometric joins and the supplied optional endpoint labels. -/
@[expose] def MissingBoundaryInterval32
    {V : Type uV} {E : Type uE} (M : DirectedPlaneMapWithMissing V E)
    (Q : InfiniteBoundarySide.{uV, uE, uI} V E)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)) (U : G.Face) (S : E × Bool → E × Bool) : Prop :=
  ∃ p : Q.Index ↪ ℤ,
    Set.OrdConnected (Set.range p) ∧
    (∀ i j, Q.next i = some j ↔ p j = p i + 1) ∧
    (∀ i, G.dartBorders (Q.darts i) U ∧
      M.toPlaneMapWithMissing.missing (Q.darts i).1) ∧
    (∀ i j, p j = p i + 1 → S (Q.darts i) = Q.darts j ∧
      boundaryDartTerminal M (Q.darts i) = boundaryDartInitial M (Q.darts j)) ∧
    (∀ i, (∀ j, Q.next j ≠ some i) ↔ ∀ j, p i ≤ p j) ∧
    (∀ i, Q.next i = none ↔ ∀ j, p j ≤ p i) ∧
    BoundarySideEndpointLabels M Q

/-- Helper toward Definition 3.2: a supplied finite missing run between its
specified junction vertices; an empty run identifies the two vertices. -/
@[expose] def SuppliedMissingBoundaryInterval32
    {V : Type uV} {E : Type uE} (M : DirectedPlaneMapWithMissing V E)
    (Q : InfiniteBoundarySide.{uV, uE, uI} V E)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)) (U : G.Face) (S : E × Bool → E × Bool)
    (a b : V) : Prop :=
  ∃ p : Q.Index ↪ ℤ,
    Set.OrdConnected (Set.range p) ∧
    (∀ i, G.dartBorders (Q.darts i) U ∧
      M.toPlaneMapWithMissing.missing (Q.darts i).1) ∧
    (∀ i j, p j = p i + 1 → S (Q.darts i) = Q.darts j ∧
      boundaryDartTerminal M (Q.darts i) = boundaryDartInitial M (Q.darts j)) ∧
    (Nonempty Q.Index → ∃ i j : Q.Index,
      Set.range p = Set.Icc (p i) (p j) ∧
      boundaryDartInitial M (Q.darts i) = a ∧
      boundaryDartTerminal M (Q.darts j) = b) ∧
    (IsEmpty Q.Index → a = b)

/-- Helper toward Definition 3.2: all source clauses for the four edge sets
of a supplied presentation, including winding sides, missing intervals,
finite endpoint conventions, and the bipolar left/right naming convention. -/
@[expose] def BoundEdges32SourceClauses
    {V : Type uV} {E : Type uE} (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)) (U : G.Face) (S : E × Bool → E × Bool) : Prop :=
  IsBoundEdges32 M B G U S ∧
  IsBoundaryOrderOfInf M B.presentation ∧
  IsGeometricExternalFaceSucc G U S ∧
  (∃ p : InfiniteBoundaryDartIndex B.presentation → ℤ,
    Function.Injective p ∧
    (∀ i j, sideTag B.presentation i = sideTag B.presentation j →
      (sideNext B.presentation i = some j ↔ p j = p i + 1)) ∧
    (∀ i j z, p i ≤ z → z ≤ p j → ∃ k, p k = z) ∧
    (∀ i j k, p i ≤ p j → p j ≤ p k →
      sideTag B.presentation i = sideTag B.presentation k →
        sideTag B.presentation j = sideTag B.presentation i) ∧
    (∀ i j, sideNext B.presentation i = some j →
      S (InfiniteBoundaryDartIndex.dart B.presentation i) =
        InfiniteBoundaryDartIndex.dart B.presentation j ∧
      boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart B.presentation i) =
        boundaryDartInitial M (InfiniteBoundaryDartIndex.dart B.presentation j))) ∧
  ((∀ d, G.dartBorders d U ↔ ∃ i : InfiniteBoundaryDartIndex B.presentation,
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
          M.toPlaneMapWithMissing.missing e)) ∧
  (∀ e, (e ∈ upperLeftBoundary32 B ↔
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        ∀ s : {t : I // t ∈ openParams},
          LeftAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s) ∧
    (e ∈ lowerRightBoundary32 B ↔
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        ∀ s : {t : I // t ∈ openParams},
          RightAtOn U.val (G.arc (e, M.forward ⟨e, hp⟩)).toPath s)) ∧
  MissingBoundaryInterval32 M B.presentation.upperRight G U S ∧
  MissingBoundaryInterval32 M B.presentation.lowerLeft G U S ∧
  (∀ J : FiniteBoundaryJunctions V, B.finiteJunctions? = some J →
    FiniteBoundaryJunctionLabels6 B.presentation J ∧
    SuppliedMissingBoundaryInterval32 M B.presentation.upperRight G U S
      J.upperLeftUpperRight J.upperRightLowerRight ∧
    SuppliedMissingBoundaryInterval32 M B.presentation.lowerLeft G U S
      J.lowerRightLowerLeft J.lowerLeftUpperLeft) ∧
  (IsBipolarRel M.step → (∀ e, ¬ M.toPlaneMapWithMissing.missing e) →
    M.IsAcyclic ∧ upperRightBoundary32 B = ∅ ∧ lowerLeftBoundary32 B = ∅ ∧
    (∀ e, e ∈ leftBoundary32 B ↔
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        G.dartBorders (e, M.forward ⟨e, hp⟩) U) ∧
    (∀ e, e ∈ rightBoundary32 B ↔
      ∃ hp : ¬ M.toPlaneMapWithMissing.missing e,
        G.dartBorders (e, !(M.forward ⟨e, hp⟩)) U) ∧
    ULOkInf B.presentation ∧ LROkInf B.presentation ∧
    IsSimpleBoundarySide M B.presentation.upperLeft ∧
    IsSimpleBoundarySide M B.presentation.lowerRight)

private theorem source_clauses_of_certificate
    {V : Type uV} {E : Type uE} (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)) (U : G.Face) (S : E × Bool → E × Bool)
    (h : IsBoundEdges32 M B G U S) (hfinite : LocallyFiniteVertexImage G) :
    BoundEdges32SourceClauses M B G U S := by
  have horder : IsBoundaryOrderOfInf M B.presentation ∧
      IsGeometricExternalFaceSucc G U S := by
    by_cases hf : (externalBoundaryDartSet4 M).Finite
    · have hc := ((IsBoundEdges32.finite_iff hf).mp h).1
      exact ⟨hc.1, hc.2.2.2.1⟩
    · have hc := ((IsBoundEdges32.infinite_iff hf).mp h).2.1.1
      exact ⟨hc.1, hc.2.2.1⟩
  refine ⟨h, horder.1, horder.2, h.linear_positions_part2,
    bound_edges_provider_of_isBoundEdges32 M B G U S h, ?_,
    h.upperRight_geometric_integer_interval_part2,
    h.lowerLeft_geometric_integer_interval_part2, ?_, ?_⟩
  · intro e
    exact ⟨mem_upperLeftBoundary32_iff_mapFaceU_leftAtOn_of_locallyFiniteVertexImage
      M B G U S h hfinite e,
      mem_lowerRightBoundary32_iff_mapFaceU_rightAtOn_of_locallyFiniteVertexImage
      M B G U S h hfinite e⟩
  · intro J hJ
    have hf : (externalBoundaryDartSet4 M).Finite := by
      by_contra hi
      have hn := ((IsBoundEdges32.infinite_iff hi).mp h).1
      rw [hJ] at hn
      cases hn
    exact ⟨((IsBoundEdges32.finite_supplied_junctions_iff hf J hJ).mp h).2,
      h.upperRight_supplied_vertex_interval_part2 J hJ,
      h.lowerLeft_supplied_vertex_interval_part2 J hJ⟩
  · intro hb hn
    exact leftRightBoundaries32_of_bipolar_no_missing_edges hb hn h

/-- Helper toward Definition 3.2: the UIQBOT construction conclusion, retaining
its canonical limiting presentation and all original construction binders. -/
@[expose] def UIQBOTBoundEdges32Source : Prop :=
  ∀ (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j),
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    ∃ (B : BoundaryPresentationWithJunctions M)
      (rot : Equiv.Perm ((uiqbotPresentationDrawing w hfin).GeometricEdge × Bool))
      (G : PLDrawing ((uiqbotPresentationDrawing w hfin).GeometricEdge × Bool) ℕ
        (fun d => (d.1, !d.2)) rot (boundaryDartInitial M))
      (U : G.Face) (S : (uiqbotPresentationDrawing w hfin).GeometricEdge × Bool →
        (uiqbotPresentationDrawing w hfin).GeometricEdge × Bool),
      B = uiqbotCanonicalBoundaryPresentationLabeledXWithJunctions w hfin htrans hR hL0 ∧
      B.finiteJunctions? = none ∧ BoundEdges32SourceClauses M B G U S

/-- Helper toward Definition 3.2: UIQBOT supplies a presentation satisfying
every packaged source clause, with no additional geometric premise. -/
theorem uiqbot_bound_edges32_source : UIQBOTBoundEdges32Source := by
  intro w hfin htrans hR hL0
  obtain ⟨B, rot, G, U, S, hB, hnone, h32, _⟩ :=
    uiqbotBoundEdgesDefinition32Assembly w hfin htrans hR hL0
  exact ⟨B, rot, G, U, S, hB, hnone,
    source_clauses_of_certificate _ B G U S h32
      (uiqbot_boundEdges32_locallyFiniteVertexImage_part1 w hfin G)⟩

/-- Helper toward Definition 3.2: the almost-sure UIBHBOT conclusion, with
the adopted reversed presentation and the original geometric assembly data. -/
@[expose] def UIBHBOTBoundEdges32Source : Prop :=
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
        B = ⟨Q, none⟩ ∧ B.finiteJunctions? = none ∧
          BoundEdges32SourceClauses M B G U S

/-- Helper toward Definition 3.2: almost surely UIBHBOT supplies the reversed
limiting presentation with every packaged source clause. -/
theorem ae_uibhbot_bound_edges32_source : UIBHBOTBoundEdges32Source := by
  filter_upwards [ae_uibhbotBoundEdgesDefinition32Assembly] with W hW
  rcases hW with ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa,
    hRpos, e, hinj, hsource, B, rot, G, U, S, hB, hnone, h32, _⟩
  exact ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa,
    hRpos, e, hinj, hsource, B, rot, G, U, S, hB, hnone,
    source_clauses_of_certificate _ B G U S h32
      (uibhbot_boundEdges32_locallyFiniteVertexImage_part1
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos G)⟩

/-- Helper toward Definition 3.2: the finite KMSW construction conclusion,
retaining its realization, drawing image, and supplied junction record. -/
@[expose] def KMSWStageBoundEdges32Source : Prop :=
  ∀ (w : ℕ → Fin 3) (n : ℕ),
    ∃ (P : StageDrawing w n) (U₀ : P.Face)
      (_hU : P.IsUnbounded U₀)
      (_hborder : ∀ d, P.dartBorders d U₀ ↔ (kmswStageDirectedMap w n).IsOuter d),
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
      B.finiteJunctions? = some J ∧
      G.image = P.image ∧ BoundEdges32SourceClauses M B G U S

/-- Helper toward Definition 3.2: every finite KMSW stage supplies its four
boundary sets with all packaged source clauses. -/
theorem kmswStage_bound_edges32_source : KMSWStageBoundEdges32Source := by
  intro w n
  obtain ⟨P, U₀, hU, hborder, M, J, B, rot, G, U, S, hreal, hB, himage, h32, _⟩ :=
    kmswStageBoundEdgesDefinition32Assembly w n
  have hJ : B.finiteJunctions? = some J := by rw [hB]; rfl
  exact ⟨P, U₀, hU, hborder, M, J, B, rot, G, U, S, hreal, hB, hJ, himage,
    source_clauses_of_certificate M B G U S h32
      (kmswStage_boundEdges32_locallyFiniteVertexImage_part1 w n M G)⟩

/-- Helper toward Definition 3.2: the boundary-channeled conclusion has only
the F1 geometric unboundedness premise, outside the Definition 3.17 predicate. -/
@[expose] def BoundaryChanneledBoundEdges32Source : Prop :=
  ∀ {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (P : BoundaryChanneledPLDrawing R),
    P.IsUnbounded (boundaryChanneledMarkedOuterFace R P) →
    let M := boundaryChanneledPlaneMap R P
    ∃ (B : BoundaryPresentationWithJunctions M)
      (rot : Equiv.Perm (P.GeometricEdge × Bool))
      (G : PLDrawing (P.GeometricEdge × Bool) (MapVertex R.B.map)
        (fun d => (d.1, !d.2)) rot (boundaryDartInitial M))
      (U : G.Face) (S : P.GeometricEdge × Bool → P.GeometricEdge × Bool),
      B = boundaryChanneledPresentationWithJunctions R P ∧
      B.finiteJunctions? = some ⟨R.B.source, R.B.sink, R.B.sink, R.B.source⟩ ∧
      DrawsMap M G ∧
        BoundEdges32SourceClauses M B G U S

/-- Helper toward Definition 3.2: unconditional boundary-channeled assembly
relative only to F1's representation-layer unboundedness premise. -/
theorem boundaryChanneled_bound_edges32_source : BoundaryChanneledBoundEdges32Source := by
  intro ℓ r n R P hOuterUnbounded
  obtain ⟨B, rot, G, U, S, hB, hdraw, h32⟩ :=
    exists_boundaryChanneled_bound_edges32_part2 R P hOuterUnbounded
  have hJ : B.finiteJunctions? =
      some ⟨R.B.source, R.B.sink, R.B.sink, R.B.source⟩ := by rw [hB]; rfl
  exact ⟨B, rot, G, U, S, hB, hJ, hdraw,
    source_clauses_of_certificate _ B G U S h32
      (boundaryChanneled_boundEdges32_locallyFiniteVertexImage_part1 R P G)⟩

/-- Helper toward Definition 3.2: joint construction-specific source package
for UIQBOT, almost-sure UIBHBOT, finite KMSW stages and boundary-channeled maps. -/
theorem bound_edges_definition32_source :
    UIQBOTBoundEdges32Source ∧ UIBHBOTBoundEdges32Source ∧
    KMSWStageBoundEdges32Source ∧ BoundaryChanneledBoundEdges32Source :=
  ⟨uiqbot_bound_edges32_source, ae_uibhbot_bound_edges32_source,
    kmswStage_bound_edges32_source, boundaryChanneled_bound_edges32_source⟩


























































end DirectedDistances.PlanarMap

end
