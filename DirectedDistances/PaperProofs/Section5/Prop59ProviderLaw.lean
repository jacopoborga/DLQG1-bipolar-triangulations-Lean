/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59D39ClassLaw
public import DirectedDistances.PaperProofs.Section5.Prop59ProviderRootedMapIso
public import DirectedDistances.PaperProofs.Section5.Prop516D39ClassTransport

/-! Helpers toward Proposition 5.9 (`prop-uihbot-sym`).

The theorem below identifies the provider realization at the local-topology
planar-class level, under its explicit realization hypotheses. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap MeasureTheory
open DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open scoped Classical

/- Helper toward Proposition 5.9. The provider assembly, packaged with the positive-ball
class as the code-selected planar representative. -/
theorem uibhbotProviderAssembly_d39PlanarClass_eq
    (W : ℤ → Fin 3) (hW : W ∈ uibhbotRootedPlanarMapConullEvent)
    (H : WholePlaneRotationHypothesis W)
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
    (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer
      (shiftedStream W 0) h0 (H.1 0) ''
        ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
          (monotone_family_all _)).arc d).image)
    (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
    (e : ℤ → WholePlaneEdge W)
    (he : e 0 = uibhbotRootEdge W) :
    ∃ (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
      (C₀ : UIBHBOTCertifiedRootCapture W 0)
      (planar : D39PlanarRootedMap),
      planar.toD39RootedMap =
          (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀).toD39RootedMap ∧
      (Quotient.mk D39PlanarRootedMap.setoid planar) =
        (Quotient.mk D39PlanarRootedMap.setoid
          (uibhbotRootedPlanarMapOfCode W).toD39PlanarRootedMap) := by
  obtain ⟨hhit, C₀, hIdentified⟩ :=
    uibhbotProviderAssemblyD39_identification W hW H h0 hL hR hfin P hp ha F hf hFim hFa
      hRpos e he
  let I := Classical.choice hIdentified.1
  let planar : D39PlanarRootedMap := {
    toD39RootedMap :=
      (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀).toD39RootedMap
    positiveBallGenusZero := by
      intro r hr
      exact (I.positiveBallGenusZero_iff r hr).mpr
        ((uibhbotRootedPlanarMapOfCode W).toD39PlanarRootedMap.positiveBallGenusZero r hr)
  }
  refine ⟨hhit, C₀, planar, rfl, ?_⟩
  apply Quotient.sound
  exact ⟨I⟩

/-- Helper toward Proposition 5.9. Almost surely under the code law, the code belongs to the
conull source-map event, the complete Definition 5.8 provider witnesses exist, and the provider
assembly has a positive-ball-genus-zero local topology planar representative in the same class as the
code-selected representative. -/
theorem uibhbotCodeLawRel_ae_provider_d39PlanarClass_eq :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      W ∈ uibhbotRootedPlanarMapConullEvent ∧
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
        (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer
          (shiftedStream W 0) h0 (H.1 0) ''
            ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
              (monotone_family_all _)).arc d).image)
        (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
        (e : ℤ → WholePlaneEdge W),
        (let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
         let M := uibhbotAssemblyDirectedPlaneMapWithMissing
           W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
         let E := uibhbot_assembly_faceOrbitEquiv
           W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
         (∀ a, M.missing a → ∃ K : M.toPlaneGraphDrawing.Face,
           M.toPlaneGraphDrawing.IsExternal K ∧ Set.range (M.arc a) ⊆ closure K.val) ∧
         M.IsAcyclic ∧
         (∃! K : M.toPlaneGraphDrawing.Face, M.toPlaneGraphDrawing.IsExternal K) ∧
         (∀ K : M.toPlaneGraphDrawing.Face, M.toPlaneGraphDrawing.IsExternal K →
           ∀ d : WholePlaneDart W,
             G.dartBorders d (G.toPlaneGraphDrawingFaceEquiv K) ↔
               d.2 = true ∧ M.missing (Quotient.mk G.edgeSetoid d)) ∧
         (∀ K : M.toPlaneGraphDrawing.Face, M.toPlaneGraphDrawing.IsExternal K →
           ∀ a : G.GeometricEdge,
             (∃ d : WholePlaneDart W, Quotient.mk G.edgeSetoid d = a ∧
               G.dartBorders d (G.toPlaneGraphDrawingFaceEquiv K)) ↔ M.missing a) ∧
         (∀ K : M.toPlaneGraphDrawing.Face, M.toPlaneGraphDrawing.IsInternal K →
           ∃ (N : ℕ) (j : TriangleCreationTime (shiftedStream W N)),
             {d : WholePlaneDart W | E (Quotient.mk _ d) =
                 G.toPlaneGraphDrawingFaceEquiv K} =
               wholePlaneDartι W N '' {a | a ∈ stageTriangleDartList (shiftedStream W N) j} ∧
             ((stageTriangleDartList (shiftedStream W N) j).toFinset.image
               (wholePlaneDartι W N)).card = 3) ∧
         (∀ K : M.toPlaneGraphDrawing.Face, M.toPlaneGraphDrawing.IsInternal K →
           M.toPlaneGraphDrawing.faceDegree K = 3) ∧
         uibhbotWordFamilyLaw.map
             (fun w : ℤ → List (Fin 3) => fun n : ℕ =>
               uibhbotConcatWalk w (-(n : ℤ))) =
           (rConditionedPathLaw 0 0).map
             (fun p : ℕ → ℤ × ℤ => fun n : ℕ =>
               if n = 0 then (0, 0) else (p (n - 1)).swap + (1, 0)) ∧
         (∀ k : ℤ,
           wholePlaneEdgeWest W (e k) = (uibhbotBusemannSource k W).id ∧
           wholePlaneEdgeEast W (e k) = (uibhbotBusemannSource (k + 1) W).id ∧
           ¬ wholePlaneEdgePresent W (e k) ∧
           ∃ N n : ℕ, 0 < n ∧ (n : ℤ) - N = uibhbotBoundaryHitTime k W ∧
             e k = wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N) n)) ∧
         Function.Injective e ∧ e 0 = uibhbotRootEdge W ∧
         (∀ k : ℤ, wholePlaneFaceSucc W H (e k, true) = (e (k - 1), true)) ∧
         (∀ a : WholePlaneEdge W, ¬ wholePlaneEdgePresent W a ↔ ∃! k : ℤ, a = e k) ∧
         (∀ k : ℤ, IsLeast {t : ℤ | (wholePlaneWordIntegral W t).1 = k}
           (uibhbotBoundaryHitTime k W)) ∧
         StrictAnti (fun k : ℤ => uibhbotBoundaryHitTime k W) ∧
         uibhbotBoundaryHitTime 0 W = 0 ∧
         M.missing (Quotient.mk G.edgeSetoid (uibhbotRootEdge W, false)) ∧
         (wholePlaneEdgeWest W (uibhbotRootEdge W),
           wholePlaneEdgeEast W (uibhbotRootEdge W)) =
             ((uibhbotBusemannSource 0 W).id, (uibhbotBusemannSource 1 W).id) ∧
         wholePlaneWordIntegral W 0 = 0 ∧
         (∀ t : ℤ, t ≤ -1 → 1 ≤ (wholePlaneWordIntegral W t).1) ∧
         (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
           (fun V : ℤ → Fin 3 => fun n : ℕ => wholePlaneWordIntegral V n) =
             iidCodeMeasure.map (fun ω => fun n : ℕ => codeWalk ω n) ∧
         (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
           (fun V : ℤ → Fin 3 => fun t : ℤ => wholePlaneWordIntegral V t) =
             uibhbotWordFamilyLaw.map uibhbotConcatWalk) ∧
        ∃ (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
          (C₀ : UIBHBOTCertifiedRootCapture W 0)
          (planar : D39PlanarRootedMap),
          planar.toD39RootedMap =
              (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀).toD39RootedMap ∧
          (Quotient.mk D39PlanarRootedMap.setoid planar) =
            (Quotient.mk D39PlanarRootedMap.setoid
              (uibhbotRootedPlanarMapOfCode W).toD39PlanarRootedMap) := by
  filter_upwards [uibhbotRootedPlanarMapConullEvent_spec.2.1,
    def_uibhbot_provider_v2] with W hEvent hProvider
  obtain ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos, e, hClauses⟩ :=
    hProvider
  have hClausesCopy := hClauses
  rcases hClausesCopy with ⟨_, _, _, _, _, _, _, _, _, _, he, _⟩
  refine ⟨hEvent, H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos, e,
    hClauses, ?_⟩
  exact uibhbotProviderAssembly_d39PlanarClass_eq W hEvent H h0 hL hR hfin P hp ha F hf hFim
    hFa hRpos e he





































































































end DirectedDistances.PaperProofs.Section5
