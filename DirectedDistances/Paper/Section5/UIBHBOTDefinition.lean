 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.UIBHBOTDefinitionV2

/-!
# Definition 5.8 (`def-uihbot`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/





















public section
namespace DirectedDistances.Paper.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section5
open scoped Classical

 
theorem def_uihbot :
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
          h0 (H.1 0) ''
            ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
              (monotone_family_all _)).arc d).image)
        (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
        (e : ℤ → WholePlaneEdge W),
      let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
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
        uibhbotWordFamilyLaw.map uibhbotConcatWalk :=
 
by exact DirectedDistances.PaperProofs.SourceResults.def_uibhbot_provider_v2
 
 

end DirectedDistances.Paper.Section5
 
