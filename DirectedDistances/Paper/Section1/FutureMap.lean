 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.FutureMapDefinition

/-!
# Definition 1.3 (`defn-future-map`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/














public section
namespace DirectedDistances.Paper.Section1

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1
open scoped Classical

 
theorem defn_future_map :
    ∀ᵐ W ∂RandomWalk.wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      let D := m0CutData W H h hLL
      let P := monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))
      let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
      let f := seamFun (shiftedStream W 0) h (H.1 0)
      (D.betaR.vertex 0 = D.x 1) ∧
      (∀ n, wholePlaneRightmostOutgoingAt W H (D.betaR.vertex n) (D.betaR.edge n) ∧
        wholePlaneEdgeEast W (D.betaR.edge n) = D.betaR.vertex (n + 1)) ∧
      (D.betaL.vertex 0 = D.x 0) ∧
      (∀ n, wholePlaneLeftmostIncomingAt W H (D.betaL.vertex n) (D.betaL.edge n) ∧
        wholePlaneEdgeWest W (D.betaL.edge n) = D.betaL.vertex (n + 1)) ∧
      (D.rootDart.1 = m0CutLambdaZero W) ∧
      Function.Injective (futureMapInternalGluedFace W H h hp) ∧
      ((∀ e, D.seam e ↔ e = m0CutLambdaZero W ∨
        e ∈ Set.range D.betaR.edge ∨ e ∈ Set.range D.betaL.edge) ∧
      (m0CutLeftVertices W H D.seam = Set.range (wholePlaneVertexι W 0)) ∧
      Function.Injective (wholePlaneVertexι W 0) ∧
      D.edges = Set.range (wholePlaneEdgeι W 0) ∧
      Function.Injective (wholePlaneEdgeι W 0) ∧
      D.darts = Set.range (wholePlaneDartι W 0) ∧
      (∀ e, D.seam e → e ∈ D.edges) ∧
      (∀ e, e ∈ D.edges → (D.missing e ↔ e ∈ Set.range D.betaL.edge)) ∧
      (∀ e, e ∈ D.edges → wholePlaneEdgePresent W e) ∧
      (∀ e, (e ∈ D.edges ∧ ¬ D.missing e) ↔
        (e ∈ D.edges ∧ ¬ D.seam e) ∨ e = m0CutLambdaZero W ∨
          e ∈ Set.range D.betaR.edge) ∧
      (∀ d, d ∈ D.darts →
        (D.tail d ↔ wholePlaneDartTail W d ∧ d.1 ∉ Set.range D.betaL.edge)) ∧
      (∀ e, D.missing e → ¬ D.tail (e, false) ∧ ¬ D.tail (e, true)) ∧
      (D.rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
        wholePlaneEdgeWest W D.rootDart.1 = D.x 0 ∧
        wholePlaneEdgeEast W D.rootDart.1 = D.x 1 ∧
        wholePlaneEdgePresent W D.rootDart.1 ∧
        ¬ D.missing D.rootDart.1 ∧ D.tail D.rootDart) ∧
      Function.Injective D.x ∧
      (Set.range D.x = {v | ∃ e, D.seam e ∧
        (wholePlaneEdgeWest W e = v ∨ wholePlaneEdgeEast W e = v)}) ∧
      (∀ k, D.x k ∈ m0CutLeftVertices W H D.seam) ∧
      (∀ k, D.x k = wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h k)) ∧
      (∀ k, wholePlaneEdgeWest W
          (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) = D.x k ∧
        wholePlaneEdgeEast W
          (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) = D.x (k + 1)) ∧
      (∀ d, wholePlaneDartFlip W (wholePlaneDartι W 0 d) =
        wholePlaneDartι W 0 (futureMapEdgeInv d)) ∧
      (∀ d, wholePlaneDartVertex W (wholePlaneDartι W 0 d) =
        wholePlaneVertexι W 0 (kmswLimitDartVertex (shiftedStream W 0) d)) ∧
      (∀ d a, D.IsRot (wholePlaneDartι W 0 d) a ↔
        a = wholePlaneDartι W 0 ((kmswInfRot (shiftedStream W 0) (H.1 0)).symm d))) ∧
      ((∀ d a, D.IsRot (wholePlaneDartFlip W (wholePlaneDartι W 0 d)) a ↔
        a = wholePlaneDartι W 0 (kmswInfFaceSucc (shiftedStream W 0) (H.1 0) d)) ∧
      (∀ F : G.Face, (∃ q, futureMapInternalGluedFace W H h hp q = F) ↔
        F.val ⊆ {z : ℂ | f z.re < z.im}) ∧
      (∀ d q, G.dartBorders (wholePlaneDartι W 0 d)
        (futureMapInternalGluedFace W H h hp q) ↔ Quotient.mk _ d = q.val) ∧
      (∀ d, P.dartBorders d
        (futureMapFaceOrbitEquiv W H h (futureMapExteriorOrbit W H)) ↔
        d.2 = true ∧ D.seam (wholePlaneEdgeι W 0 d.1)) ∧
      (∀ q : FutureMapInternalFaceOrbit W H,
        ∃ j : TriangleCreationTime (shiftedStream W 0),
          {a | G.dartBorders a (futureMapInternalGluedFace W H h hp q)} =
            wholePlaneDartι W 0 '' {d | d ∈ stageTriangleDartList (shiftedStream W 0) j} ∧
          ((stageTriangleDartList (shiftedStream W 0) j).toFinset.image
            (wholePlaneDartι W 0)).card = 3) ∧
      (∀ v : RootedLocallyFiniteVertex (ℕ × Bool)
          (kmswInfRot (shiftedStream W 0) (H.1 0)),
        ¬ Relation.TransGen
          (rootedLocallyFiniteDirectedStep (kmswInfRot (shiftedStream W 0) (H.1 0))
            futureMapEdgeInv (fun d => D.missing (wholePlaneDartι W 0 d).1)
            (fun d => D.tail (wholePlaneDartι W 0 d))) v v) ∧
      (∀ e, e ∈ D.edges → (D.missing e ↔ e ∈ Set.range D.betaL.edge)) ∧
      ({z | ∃ a : WholePlaneDart W, D.seam a.1 ∧ z ∈ (G.arc a).image} =
        {z : ℂ | z.im = f z.re}) ∧
      (∀ v, v ∈ m0CutLeftVertices W H D.seam ↔ f (G.pos v).re ≤ (G.pos v).im) ∧
      (∀ e, e ∈ D.edges ↔ (G.arc (e, false)).image ⊆ {z : ℂ | f z.re ≤ z.im})) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.defn_future_map_provider
 
 

end DirectedDistances.Paper.Section1
 
