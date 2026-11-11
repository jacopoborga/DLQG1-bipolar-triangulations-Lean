/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingBoundedFaces
public import DirectedDistances.PlanarMap.PLDrawingGeneralCarrier
public import DirectedDistances.PlanarMap.GeneralPlaneMapSideDegree
public import DirectedDistances.PaperProofs.SourceResults.UIQBOTDefinitionV2
public import DirectedDistances.KMSW.FiniteWalkClassCarrier
public import DirectedDistances.PaperProofs.Section3.UIBOTWholePlaneSourcePart4
public import DirectedDistances.KMSW.MonotoneStepAll
public import DirectedDistances.KMSW.MonotoneLayoutInvariant

/-!
# The source standing domain for boundary poles

The revised Definition 1.1 requires each existing source or sink to lie on an
external-face boundary. This refinement leaves the general library predicates
unchanged. It makes no assertion that a pole or an external face exists when
there are no finite poles.
-/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set
open scoped Topology

variable {V E : Type*}

/-- The boundary-pole standing restriction in revised Definition 1.1.
External faces use the existing unbounded-complementary-component convention. -/
@[expose] def DirectedPlaneMap.PolesOnExternalBoundary (M : DirectedPlaneMap V E) : Prop :=
  ∀ v, M.IsSource v ∨ M.IsSink v →
    ∃ F : M.toPlaneGraphDrawing.Face,
      M.toPlaneGraphDrawing.IsExternal F ∧ M.pos v ∈ frontier F.val

/-- The admissible drawing domain for the revised standing boundary condition.
The separate generic bipolar/triangulation predicates keep their existing meanings. -/
@[expose] def SourceBoundaryDomain (V E : Type*) :=
  {M : DirectedPlaneMap V E // M.PolesOnExternalBoundary}

/-- The paper triangulation domain refines the existing generic predicate. -/
@[expose] def SourceBipolarTriangulation (V E : Type*) :=
  {M : DirectedPlaneMap V E //
    M.IsBipolarTriangulationBySides ∧ M.PolesOnExternalBoundary}

/-- An object with no finite poles meets the standing restriction vacuously. -/
theorem DirectedPlaneMap.polesOnExternalBoundary_of_no_poles
    (M : DirectedPlaneMap V E)
    (hsource : ∀ v, ¬ M.IsSource v) (hsink : ∀ v, ¬ M.IsSink v) :
    M.PolesOnExternalBoundary := by
  intro v hv
  exact (hv.elim (hsource v) (hsink v)).elim

namespace PLDrawing

variable {D : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}

/-- A bordering dart's initial vertex is on that same face's frontier. -/
theorem dartBorders_start_mem_frontier (P : PLDrawing D V flip rot vert)
    {d : D} {F : P.Face} (h : P.dartBorders d F) :
    P.pos (vert d) ∈ frontier F.val := by
  rw [frontier_eq_closure_inter_closure]
  refine ⟨P.dartBorders_start_mem_closure h, subset_closure ?_⟩
  intro hv
  exact P.face_subset_compl F hv (Or.inl ⟨vert d, rfl⟩)

/-- Convert an actual unbounded bordering face to the same directed drawing. -/
theorem externalBoundary_of_dartBorders (P : PLDrawing D V flip rot vert)
    (M : DirectedPlaneMap V P.GeometricEdge)
    (hdraw : M.toPlaneGraphDrawing = P.toPlaneGraphDrawing)
    {d : D} {U : P.Face} (hU : P.IsUnbounded U) (hd : P.dartBorders d U) :
    ∃ F : M.toPlaneGraphDrawing.Face,
      M.toPlaneGraphDrawing.IsExternal F ∧ M.pos (vert d) ∈ frontier F.val := by
  rw [hdraw]
  refine ⟨P.toPlaneGraphDrawingFaceEquiv.symm U, ?_, ?_⟩
  · exact (P.toPlaneGraphDrawing_isExternal_iff _).mpr hU
  · exact P.dartBorders_start_mem_frontier hd

end PLDrawing
end DirectedDistances.PlanarMap


namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.SourceResults Filter MeasureTheory
open scoped Topology

/-- The same UIQBOT realization used by Definition 4.1 satisfies the revised
boundary-pole standing restriction, on its existing probability-one event.
The map and its incidence, orientation, source, sinks and face degrees are
retained; no conditioning or additional event is imposed. -/
theorem uiqbot_ae_source_boundary_domain :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        ∃ P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
            (kmswInfRot w hfin) (kmswLimitDartVertex w),
          ∃ M : DirectedPlaneMap ℕ P.GeometricEdge,
            ∃ iota : ℕ ≃ P.GeometricEdge,
              M.toPlaneGraphDrawing = P.toPlaneGraphDrawing ∧
              (∀ e, M.tail (iota e) = edgeWest w e ∧
                M.head (iota e) = edgeEast w e) ∧
              M.IsAcyclic ∧ M.IsSource 0 ∧
              (∀ v, M.IsSource v → v = 0) ∧
              (∀ v, ¬ M.IsSink v) ∧ M.PolesOnExternalBoundary ∧
              ∀ K : M.toPlaneGraphDrawing.Face,
                M.toPlaneGraphDrawing.IsInternal K →
                  M.toPlaneGraphDrawing.faceDegree K = 3 := by
  filter_upwards [def_uiqbot_provider_v2.2] with ω hω
  let w := pitmanCode (fun i => ω (i + 1))
  rcases hω with ⟨hfin, htrans, hR, hL0, _, Q, hQ, P, hpos, harc,
    U, hUb, hUunique, hBorders, hBoundary, hmapP, hm⟩
  let M := Classical.choose hmapP
  let iota := Classical.choose (Classical.choose_spec hmapP)
  rcases hm with ⟨hdraw, hcompat, hac, hpresent, hsource, hunique, hnosink,
    hrootTail, hrootHead, hleft, hright, hleftSucc, hrightSucc, hjunction, hdegree⟩
  have hzero : kmswLimitDartVertex w (kmswLeftBoundaryEdge w 0, false) = 0 := by
    exact (kmswLeftBoundary_infinite_present_path w htrans hL0 hR).2.2.1
  have hzeroBoundary : ∃ F : M.toPlaneGraphDrawing.Face,
      M.toPlaneGraphDrawing.IsExternal F ∧ M.pos 0 ∈ frontier F.val := by
    have h := P.externalBoundary_of_dartBorders M hdraw hUb (hleft 0)
    rwa [hzero] at h
  refine ⟨hfin, P, M, iota, hdraw, hcompat, hac, hsource, hunique, hnosink, ?_,
    hdegree⟩
  intro v hv
  rcases hv with hs | ht
  · simpa only [hunique v hs] using hzeroBoundary
  · exact (hnosink v ht).elim

end DirectedDistances.KMSW


namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap DirectedDistances.KMSW
open DirectedDistances.RandomWalk

/-- The actual whole-plane source map has no finite poles; hence its revised
boundary-pole restriction is vacuous, without positing an external face. -/
theorem uibotWholePlaneSourceDirectedMap_source_boundary_domain
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    (uibotWholePlaneSourceDirectedMap W H
      (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp).PolesOnExternalBoundary := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
  let M := uibotWholePlaneSourceDirectedMap W H G hp
  have hend (e : WholePlaneEdge W) :
      M.tail e = wholePlaneEdgeWest W e ∧
        M.head e = wholePlaneEdgeEast W e :=
    uibotWholePlaneSourceMap_endpoints W H G hp e
  apply M.polesOnExternalBoundary_of_no_poles
  · intro v hv
    obtain ⟨_, f, hf⟩ := uibotWholePlane_noPoles W h0 hpast v
    exact hv f ((hend f).2.trans hf)
  · intro v hv
    obtain ⟨⟨e, he⟩, _⟩ := uibotWholePlane_noPoles W h0 hpast v
    exact hv e ((hend e).1.trans he)

end DirectedDistances.PaperProofs.Section3


namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology

/-- The two allocated-edge pole positions of a monotone stage lie on the
frontier of its actual unbounded face. This is a geometric statement about
allocated edges; it does not call a partially oriented missing-edge map bipolar. -/
theorem MonotoneStageInvariant.allocated_poles_mem_frontier
    {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) :
    ∃ U : P.Face, P.IsUnbounded U ∧
      ∀ v : Fin (kmswStage w n).nextVertex,
        ((∀ e < (kmswStage w n).nextEdge, (kmswStage w n).east e ≠ v.val) ∨
          (∀ e < (kmswStage w n).nextEdge, (kmswStage w n).west e ≠ v.val)) →
        P.pos v ∈ frontier U.val := by
  obtain ⟨_, U, _, hUb, _, hBorders⟩ := G.face_partition
  refine ⟨U, hUb, ?_⟩
  intro v hv
  rcases hv with hsource | hsink
  · have hpole := ((kmswStage_allocated_poles w n).1 v.val v.isLt).mp hsource
    unfold boundaryStart at hpole
    obtain ⟨e, he, hev⟩ := Option.map_eq_some_iff.mp hpole
    have hemem : e ∈ (kmswStage w n).UL := List.mem_of_mem_head? he
    have hebound := (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hemem)))
    let d : StageDart (kmswStage w n).nextEdge := (⟨e, hebound⟩, false)
    have hd : (kmswStageDirectedMap w n).IsOuter d :=
      ((kmswStageDirectedMap_UL_bridge w n d.1).mp hemem).2.2
    have hvert : stageVertex w n d = v := by
      apply Fin.ext
      exact hev
    have hfront := P.dartBorders_start_mem_frontier ((hBorders d).mpr hd)
    rwa [hvert] at hfront
  · have hpole := ((kmswStage_allocated_poles w n).2 v.val v.isLt).mp hsink
    unfold boundaryEnd at hpole
    obtain ⟨e, he, hev⟩ := Option.map_eq_some_iff.mp hpole
    have hemem : e ∈ (kmswStage w n).LR := List.mem_of_mem_getLast? he
    have hebound := (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append]
      exact Or.inr hemem)
    let d : StageDart (kmswStage w n).nextEdge := (⟨e, hebound⟩, true)
    have hd : (kmswStageDirectedMap w n).IsOuter d :=
      ((kmswStageDirectedMap_LR_bridge w n d.1).mp hemem).2.2
    have hvert : stageVertex w n d = v := by
      apply Fin.ext
      exact hev
    have hfront := P.dartBorders_start_mem_frontier ((hBorders d).mpr hd)
    rwa [hvert] at hfront

/-- Every actual admissible finite walk sample has the geometric boundary-pole
property on an existing monotone realization. All darts of this sample are
present, so the allocated-edge pole test is its directed-edge pole test. -/
theorem finiteWalkClass_source_boundary_realization {ℓ r n : ℕ}
    (hn : 1 ≤ n) (c : KMSWWalkClass ℓ r n) :
    ∃ P : StageDrawing (codeExtend c) (n - 1),
      (∀ d, ¬ (kmswStageDirectedMap (codeExtend c) (n - 1)).missing d) ∧
      ∃ U : P.Face, P.IsUnbounded U ∧
        ∀ v : Fin (kmswStage (codeExtend c) (n - 1)).nextVertex,
          ((∀ e < (kmswStage (codeExtend c) (n - 1)).nextEdge,
              (kmswStage (codeExtend c) (n - 1)).east e ≠ v.val) ∨
            (∀ e < (kmswStage (codeExtend c) (n - 1)).nextEdge,
              (kmswStage (codeExtend c) (n - 1)).west e ≠ v.val)) →
          P.pos v ∈ frontier U.val := by
  obtain ⟨h, ⟨G⟩⟩ := monotone_family_all (codeExtend c) (n - 1)
  exact ⟨_, kmswWalkClassBase_noMissingDarts hn c, G.allocated_poles_mem_frontier⟩

end DirectedDistances.KMSW


namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology

/-- The finite sample's directed plane drawing on its geometric edge orbits.
Its west-to-east orientation is the existing KMSW orientation; the no-missing
property is established separately for the admissible finite sample. -/
@[expose] def finiteWalkClassDirectedPlaneMap {ℓ r n : ℕ}
    (c : KMSWWalkClass ℓ r n) (P : StageDrawing (codeExtend c) (n - 1)) :
    DirectedPlaneMap (Fin (kmswStage (codeExtend c) (n - 1)).nextVertex)
      P.GeometricEdge where
  toPlaneGraphDrawing := P.toPlaneGraphDrawing
  forward e := !e.out.2

/-- Geometric quotient representatives retain the finite sample's endpoints. -/
theorem finiteWalkClassDirectedPlaneMap_endpoints {ℓ r n : ℕ}
    (c : KMSWWalkClass ℓ r n) (P : StageDrawing (codeExtend c) (n - 1))
    (e : Fin (kmswStage (codeExtend c) (n - 1)).nextEdge) :
    (finiteWalkClassDirectedPlaneMap c P).tail (Quotient.mk P.edgeSetoid (e, false)) =
        stageVertex (codeExtend c) (n - 1) (e, false) ∧
      (finiteWalkClassDirectedPlaneMap c P).head (Quotient.mk P.edgeSetoid (e, false)) =
        stageVertex (codeExtend c) (n - 1) (e, true) := by
  let q : P.GeometricEdge := Quotient.mk P.edgeSetoid (e, false)
  change ((if !q.out.2 then stageVertex (codeExtend c) (n - 1) q.out
      else stageVertex (codeExtend c) (n - 1) (edgeFlip _ q.out)) = _) ∧
    ((if !q.out.2 then stageVertex (codeExtend c) (n - 1) (edgeFlip _ q.out)
      else stageVertex (codeExtend c) (n - 1) q.out) = _)
  rcases P.geometricEdge_out_mk (e, false) with h | h
  · change q.out = (e, false) at h
    rw [h]
    exact ⟨rfl, rfl⟩
  · change q.out = edgeFlip _ (e, false) at h
    rw [h]
    exact ⟨rfl, rfl⟩

/-- The actual finite sample drawing satisfies the revised standing restriction.
The proof uses its unchanged directed endpoints and the same monotone drawing. -/
theorem finiteWalkClassDirectedPlaneMap_source_boundary_domain {ℓ r n : ℕ}
    (c : KMSWWalkClass ℓ r n) {P : StageDrawing (codeExtend c) (n - 1)}
    (G : MonotoneStageInvariant (codeExtend c) (n - 1) P) :
    (finiteWalkClassDirectedPlaneMap c P).PolesOnExternalBoundary := by
  obtain ⟨U, hUb, hfront⟩ := G.allocated_poles_mem_frontier
  intro v hv
  have hvfront : P.pos v ∈ frontier U.val := by
    apply hfront v
    rcases hv with hsource | hsink
    · left
      intro e he heq
      let q := Quotient.mk P.edgeSetoid (⟨e, he⟩, false)
      apply hsource q
      rw [(finiteWalkClassDirectedPlaneMap_endpoints c P ⟨e, he⟩).2]
      apply Fin.ext
      exact heq
    · right
      intro e he heq
      let q := Quotient.mk P.edgeSetoid (⟨e, he⟩, false)
      apply hsink q
      rw [(finiteWalkClassDirectedPlaneMap_endpoints c P ⟨e, he⟩).1]
      apply Fin.ext
      exact heq
  refine ⟨P.toPlaneGraphDrawingFaceEquiv.symm U, ?_, hvfront⟩
  exact (P.toPlaneGraphDrawing_isExternal_iff _).mpr hUb

/-- Every finite source sample has a concrete representative in the standing
domain, with the original geometric positions, edges and KMSW orientation. -/
theorem finiteWalkClass_exists_source_boundary_domain {ℓ r n : ℕ}
    (hn : 1 ≤ n) (c : KMSWWalkClass ℓ r n) :
    ∃ P : StageDrawing (codeExtend c) (n - 1),
      (∀ d, ¬ (kmswStageDirectedMap (codeExtend c) (n - 1)).missing d) ∧
      (finiteWalkClassDirectedPlaneMap c P).PolesOnExternalBoundary := by
  obtain ⟨h, ⟨G⟩⟩ := monotone_family_all (codeExtend c) (n - 1)
  exact ⟨_, kmswWalkClassBase_noMissingDarts hn c,
    finiteWalkClassDirectedPlaneMap_source_boundary_domain c G⟩

end DirectedDistances.KMSW
