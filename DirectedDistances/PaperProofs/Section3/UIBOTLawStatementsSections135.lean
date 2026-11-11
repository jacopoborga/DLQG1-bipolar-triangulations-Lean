/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTQualifierSections135
public import DirectedDistances.PaperProofs.Section3.UIBOTSourceStatementPart2
















public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.Probability DirectedDistances.PaperProofs.Section1
open DirectedDistances.PaperProofs.Section5 DirectedDistances.PaperProofs.Section7
open DirectedDistances.Paper.Section4 DirectedDistances.PaperProofs.Section5.Xdp
open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Topology Classical

local instance uibotLawStatementsSections135MeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance uibotLawStatementsSections135BorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

local notation "μ₁₃₅" =>
  (uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved :
    Measure D39GeomRootedMapClass)

/-- Helper toward Proposition 3.9: the transported measure is exactly the
fixed UIBOT probability law used by the source-statement proof. -/
theorem uibotLaw135_measure_eq : μ₁₃₅ = uibotQualifier135Measure := by
  rfl

/-- Helper toward Proposition 3.9: the fixed UIBOT law is the pushforward
of the iid word law by the measurable source KMSW class map. -/
theorem uibotLaw135_source_pushforward :
    μ₁₃₅ = wholePlaneIIDCodeMeasure.map
      (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved) := by
  rfl

/-- Helper toward Proposition 3.9: every Borel class observable has the
pushforward law obtained by composing it with the source KMSW class map. -/
theorem uibotLaw135_observable_pushforward {α : Type*} [MeasurableSpace α]
    (Y : D39GeomRootedMapClass.{0} → α) (hY : Measurable Y) :
    (μ₁₃₅).map Y = wholePlaneIIDCodeMeasure.map
      (Y ∘ uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved) := by
  rw [uibotLaw135_source_pushforward]
  exact Measure.map_map hY
    (measurable_uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved)

/-- Helper toward Proposition 3.9: a Borel predicate holds almost surely
under the UIBOT law exactly when its source KMSW pullback does. -/
theorem uibotLaw135_ae_iff (P : D39GeomRootedMapClass.{0} → Prop)
    (hP : MeasurableSet {z | P z}) :
    (∀ᵐ z ∂μ₁₃₅, P z) ↔ ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      P (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W) := by
  rw [uibotLaw135_source_pushforward]
  exact ae_map_iff
    (measurable_uibotMeasurableWholePlaneClassMap
      uibotDeterministicComparison_proved).aemeasurable hP

/-- Helper toward Proposition 3.9: the full joint Busemann sequence and
rescaled-path observable has its transported code law under the UIBOT law. -/
theorem uibotLaw135_busemann_observables_law :
    (μ₁₃₅).map uibotGeomBusemannObservables =
      wholePlaneIIDCodeMeasure.map uibotCodeBusemannObservables := by
  rw [uibotLaw135_observable_pushforward _ measurable_uibotGeomBusemannObservables]
  exact Measure.map_congr uibotGeomBusemannObservables_ae.symm

/-- Helper toward Proposition 3.9: all future generating words at every
integer shift have their joint transported code law under the UIBOT law. -/
theorem uibotLaw135_future_observables_law :
    (μ₁₃₅).map uibotGeomFutureObservables =
      wholePlaneIIDCodeMeasure.map uibotCodeFutureObservables := by
  rw [uibotLaw135_observable_pushforward _ measurable_uibotGeomFutureObservables]
  exact Measure.map_congr uibotGeomFutureObservables_ae.symm

/-- Helper toward Proposition 3.9: both modes and all integer indices of
the side/slice observable have their joint transported code law. -/
theorem uibotLaw135_side_slice_observables_law :
    (μ₁₃₅).map uibotGeomSideSliceObservables =
      wholePlaneIIDCodeMeasure.map uibotCodeSideSliceObservables := by
  rw [uibotLaw135_observable_pushforward _ measurable_uibotGeomSideSliceObservables]
  exact Measure.map_congr uibotGeomSideSliceObservables_ae.symm

/-- Helper toward Proposition 3.9: the fixed Borel recovery observable
has the full iid code law under the UIBOT law. -/
theorem uibotLaw135_recoveredCode_law :
    (μ₁₃₅).map uibotRecoveredCode = wholePlaneIIDCodeMeasure := by
  rw [uibotLaw135_measure_eq]
  exact uibotQualifier135_recoveredCode_law

/-- Helper toward Proposition 3.9: the whole rescaled path law is the
pushforward of the UIBOT law by the installed Borel path observable. -/
@[expose] def uibotLaw135ScalingLaw (longest : Bool) (n : ℕ) :
    ProbabilityMeasure WholeLineCadlag :=
  ⟨(μ₁₃₅).map
    (fun z => if longest then ((uibotGeomBusemannObservables z).2 n).1
      else ((uibotGeomBusemannObservables z).2 n).2),
    (uibotQualifier135ScalingLaw longest n).property⟩

/-- Helper toward Proposition 3.9: Definition 1.3's complete transported
Borel predicate certificate under the fixed UIBOT law. -/
theorem uibotLaw135_future_map_predicate :
    ∃ S : Set D39GeomRootedMapClass.{0}, MeasurableSet S ∧
      (∀ᵐ z ∂μ₁₃₅, z ∈ S) ∧
      (∀ z, z ∈ S →
      let W := uibotRecoveredCode z
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
      (∀ e, e ∈ D.edges ↔ (G.arc (e, false)).image ⊆ {z : ℂ | f z.re ≤ z.im}))) ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        (∃ H : WholePlaneRotationHypothesis W,
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
      (∀ e, e ∈ D.edges ↔ (G.arc (e, false)).image ⊆ {z : ℂ | f z.re ≤ z.im}))) ↔
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W ∈ S) := by
  rw [uibotLaw135_measure_eq]
  exact uibotQualifier135_future_map_predicate

/-- Helper toward Proposition 3.9: Definition 1.3's full transported
predicate holds almost everywhere under the fixed UIBOT law. The witnesses
remain inside the single almost-sure statement. -/
theorem uibotLaw135_future_map_predicate_ae :
    ∀ᵐ z ∂μ₁₃₅,
      let W := uibotRecoveredCode z
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
      (∀ e, e ∈ D.edges ↔ (G.arc (e, false)).image ⊆ {z : ℂ | f z.re ≤ z.im})) := by
  obtain ⟨S, _, hS, hpred, _⟩ := uibotLaw135_future_map_predicate
  filter_upwards [hS] with z hz
  exact hpred z hz

/-- Helper toward Proposition 3.9: Theorem 1.4's complete transported
Borel predicate certificate under the fixed UIBOT law. -/
theorem uibotLaw135_busemann_cut_predicate :
    ∃ S : Set D39GeomRootedMapClass.{0}, MeasurableSet S ∧
      (∀ᵐ z ∂μ₁₃₅, z ∈ S) ∧
      (∀ z, z ∈ S →
      let W := uibotRecoveredCode z
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
        ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0
            (kmswLLCreatedEdge (shiftedStream W 0)
              (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        let w := shiftedStream W 0
        let V := wholePlaneVertexι W 0
        let E := wholePlaneEdgeι W 0
        let D := m0CutData W H h hLL
        (Function.Injective V ∧
        Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
        Function.Injective E ∧
        Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
        (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
        ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
          (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
          wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
          wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
          wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
        (∀ e, EdgePresent w e ↔
          (wholePlaneEdgePresent W (E e) ∧
            ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
        (∀ e, (D).missing (E e) ↔
          ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
        (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
          ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
        (∀ a b, (D).sdp (V a) (V b) =
          DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
        (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
        (∀ k k', (D).sdp ((D).x k) ((D).x k') =
          DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
        (∀ k k', (D).ldp ((D).x k) ((D).x k') =
          presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
        Function.Injective D.x ∧
        Set.range D.x = {v | ∃ e, m0CutSeamEdge W H e ∧
          (wholePlaneEdgeWest W e = v ∨ wholePlaneEdgeEast W e = v)} ∧
        (∀ k : ℤ,
          m0CutSeamEdge W H
              (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) ∧
          wholePlaneEdgeWest W
              (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) = D.x k ∧
          wholePlaneEdgeEast W
              (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) =
            D.x (k + 1)) ∧
        (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h 0) =
            m0CutLambdaZero W ∧
          m0CutSeamEdge W H (m0CutLambdaZero W) ∧
          wholePlaneEdgeWest W (m0CutLambdaZero W) = D.x 0 ∧
          wholePlaneEdgeEast W (m0CutLambdaZero W) = D.x 1) ∧
        (∀ a b : WholePlaneVertex W, m0CutReachable W H D.seam a b → D.sdp a b ≠ ⊤) ∧
        (∀ a b : WholePlaneVertex W, m0CutReachable W H D.seam a b →
          ∃ n : ℕ, D.ldp a b = ((n : ℕ∞) : WithBot ℕ∞)) ∧
        (∃! X : ℤ → ℤ, IsIdentifiedM0BusemannSDP D X) ∧
        (∃! X : ℤ → ℤ, IsIdentifiedM0BusemannLDP D X)) ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        (∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
        ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0
            (kmswLLCreatedEdge (shiftedStream W 0)
              (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        let w := shiftedStream W 0
        let V := wholePlaneVertexι W 0
        let E := wholePlaneEdgeι W 0
        let D := m0CutData W H h hLL
        (Function.Injective V ∧
        Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
        Function.Injective E ∧
        Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
        (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
        ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
          (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
          wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
          wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
          wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
        (∀ e, EdgePresent w e ↔
          (wholePlaneEdgePresent W (E e) ∧
            ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
        (∀ e, (D).missing (E e) ↔
          ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
        (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
          ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
        (∀ a b, (D).sdp (V a) (V b) =
          DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
        (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
        (∀ k k', (D).sdp ((D).x k) ((D).x k') =
          DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
        (∀ k k', (D).ldp ((D).x k) ((D).x k') =
          presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
        Function.Injective D.x ∧
        Set.range D.x = {v | ∃ e, m0CutSeamEdge W H e ∧
          (wholePlaneEdgeWest W e = v ∨ wholePlaneEdgeEast W e = v)} ∧
        (∀ k : ℤ,
          m0CutSeamEdge W H
              (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) ∧
          wholePlaneEdgeWest W
              (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) = D.x k ∧
          wholePlaneEdgeEast W
              (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) =
            D.x (k + 1)) ∧
        (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h 0) =
            m0CutLambdaZero W ∧
          m0CutSeamEdge W H (m0CutLambdaZero W) ∧
          wholePlaneEdgeWest W (m0CutLambdaZero W) = D.x 0 ∧
          wholePlaneEdgeEast W (m0CutLambdaZero W) = D.x 1) ∧
        (∀ a b : WholePlaneVertex W, m0CutReachable W H D.seam a b → D.sdp a b ≠ ⊤) ∧
        (∀ a b : WholePlaneVertex W, m0CutReachable W H D.seam a b →
          ∃ n : ℕ, D.ldp a b = ((n : ℕ∞) : WithBot ℕ∞)) ∧
        (∃! X : ℤ → ℤ, IsIdentifiedM0BusemannSDP D X) ∧
        (∃! X : ℤ → ℤ, IsIdentifiedM0BusemannLDP D X)) ↔
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W ∈ S) := by
  rw [uibotLaw135_measure_eq]
  exact uibotQualifier135_busemann_cut_predicate

/-- Helper toward Proposition 3.9: Theorem 1.4's full transported
predicate holds almost everywhere under the fixed UIBOT law. The witnesses
remain inside the single almost-sure statement. -/
theorem uibotLaw135_busemann_cut_predicate_ae :
    ∀ᵐ z ∂μ₁₃₅,
      let W := uibotRecoveredCode z
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
        ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0
            (kmswLLCreatedEdge (shiftedStream W 0)
              (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        let w := shiftedStream W 0
        let V := wholePlaneVertexι W 0
        let E := wholePlaneEdgeι W 0
        let D := m0CutData W H h hLL
        (Function.Injective V ∧
        Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
        Function.Injective E ∧
        Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
        (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
        ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
          (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
          wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
          wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
          wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
        (∀ e, EdgePresent w e ↔
          (wholePlaneEdgePresent W (E e) ∧
            ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
        (∀ e, (D).missing (E e) ↔
          ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
        (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
          ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
        (∀ a b, (D).sdp (V a) (V b) =
          DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
        (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
        (∀ k k', (D).sdp ((D).x k) ((D).x k') =
          DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
        (∀ k k', (D).ldp ((D).x k) ((D).x k') =
          presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
        Function.Injective D.x ∧
        Set.range D.x = {v | ∃ e, m0CutSeamEdge W H e ∧
          (wholePlaneEdgeWest W e = v ∨ wholePlaneEdgeEast W e = v)} ∧
        (∀ k : ℤ,
          m0CutSeamEdge W H
              (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) ∧
          wholePlaneEdgeWest W
              (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) = D.x k ∧
          wholePlaneEdgeEast W
              (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) =
            D.x (k + 1)) ∧
        (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h 0) =
            m0CutLambdaZero W ∧
          m0CutSeamEdge W H (m0CutLambdaZero W) ∧
          wholePlaneEdgeWest W (m0CutLambdaZero W) = D.x 0 ∧
          wholePlaneEdgeEast W (m0CutLambdaZero W) = D.x 1) ∧
        (∀ a b : WholePlaneVertex W, m0CutReachable W H D.seam a b → D.sdp a b ≠ ⊤) ∧
        (∀ a b : WholePlaneVertex W, m0CutReachable W H D.seam a b →
          ∃ n : ℕ, D.ldp a b = ((n : ℕ∞) : WithBot ℕ∞)) ∧
        (∃! X : ℤ → ℤ, IsIdentifiedM0BusemannSDP D X) ∧
        (∃! X : ℤ → ℤ, IsIdentifiedM0BusemannLDP D X) := by
  obtain ⟨S, _, hS, hpred, _⟩ := uibotLaw135_busemann_cut_predicate
  filter_upwards [hS] with z hz
  exact hpred z hz

/-- Helper toward Proposition 3.9: Theorems 1.4 and 1.6–1.8's transported statement
under the fixed UIBOT law, retaining its existing geometric qualifications. -/
theorem uibotLaw135_busemann_characterization :
    ∀ᵐ z ∂μ₁₃₅,
      let W := uibotRecoveredCode z
      ∃ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1))))),
        IsIdentifiedM0BusemannLDP (m0CutData W H h hLL)
          (uibotQualifier135Busemann true z) ∧
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL)
          (uibotQualifier135Busemann false z) ∧
        ∀ n : ℕ, (uibotGeomBusemannObservables z).2 n =
          (identifiedLDPScalingPath n W, identifiedSDPScalingPath n W) := by
  rw [uibotLaw135_measure_eq]
  exact uibotQualifier135_busemann_characterization

/-- Helper toward Proposition 3.9: Theorem 1.7's transported statement
under the fixed UIBOT law, retaining its existing geometric qualifications. -/
theorem uibotLaw135_busemann_property (longest : Bool) :
    iIndepFun (fun k z => uibotQualifier135Busemann longest z k -
      uibotQualifier135Busemann longest z (k - 1)) μ₁₃₅ ∧
    (∀ k : ℤ, 1 ≤ k → IdentDistrib
      (fun z => uibotQualifier135Busemann longest z k -
        uibotQualifier135Busemann longest z (k - 1))
      (fun z => uibotQualifier135Busemann longest z 1 -
        uibotQualifier135Busemann longest z (1 - 1))
      μ₁₃₅ μ₁₃₅) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun z => uibotQualifier135Busemann longest z k -
        uibotQualifier135Busemann longest z (k - 1))
      (fun z => uibotQualifier135Busemann longest z 0 -
        uibotQualifier135Busemann longest z (0 - 1))
      μ₁₃₅ μ₁₃₅) ∧
    (∀ᵐ z ∂μ₁₃₅, ∀ k : ℤ, 1 ≤ k →
      if longest then uibotQualifier135Busemann longest z k -
        uibotQualifier135Busemann longest z (k - 1) ≤ -1
      else -1 ≤ uibotQualifier135Busemann longest z k -
        uibotQualifier135Busemann longest z (k - 1)) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun z => uibotQualifier135Busemann longest z k -
        uibotQualifier135Busemann longest z (k - 1))
      (fun z => uibotQualifier135Busemann longest z (k - 1) -
        uibotQualifier135Busemann longest z k)
      μ₁₃₅ μ₁₃₅) := by
  rw [uibotLaw135_measure_eq]
  exact uibotQualifier135_busemann_property longest

/-- Helper toward Proposition 3.9: Theorem 1.8's transported statement
under the fixed UIBOT law, retaining its existing geometric qualifications. -/
theorem uibotLaw135_busemann_tail :
    (∃ c : ℝ, 0 < c ∧
      ((fun x : ℝ => (μ₁₃₅).real
        {z | ((uibotQualifier135Busemann true z 1 -
          uibotQualifier135Busemann true z 0 : ℤ) : ℝ) ≤ -x} -
          c * x ^ (-(2 / 3 : ℝ))) =o[atTop]
            (fun x : ℝ => x ^ (-(2 / 3 : ℝ)))) ∧
      ((fun x : ℝ => (μ₁₃₅).real
        {z | x ≤ |((uibotQualifier135Busemann true z 0 -
          uibotQualifier135Busemann true z (-1) : ℤ) : ℝ)|} -
          2 * c * x ^ (-(2 / 3 : ℝ))) =o[atTop]
            (fun x : ℝ => x ^ (-(2 / 3 : ℝ))))) ∧
    (∃ c : ℝ, 0 < c ∧
      ((fun x : ℝ => (μ₁₃₅).real
        {z | x ≤ ((uibotQualifier135Busemann false z 1 -
          uibotQualifier135Busemann false z 0 : ℤ) : ℝ)} -
          c * x ^ (-(4 / 3 : ℝ))) =o[atTop]
            (fun x : ℝ => x ^ (-(4 / 3 : ℝ)))) ∧
      ((fun x : ℝ => (μ₁₃₅).real
        {z | x ≤ |((uibotQualifier135Busemann false z 0 -
          uibotQualifier135Busemann false z (-1) : ℤ) : ℝ)|} -
          2 * c * x ^ (-(4 / 3 : ℝ))) =o[atTop]
            (fun x : ℝ => x ^ (-(4 / 3 : ℝ))))) := by
  rw [uibotLaw135_measure_eq]
  exact uibotQualifier135_busemann_tail

/-- Helper toward Proposition 3.9: Theorem 1.8's transported statement
under the fixed UIBOT law, retaining its existing geometric qualifications. -/
theorem uibotLaw135_sdp_mean (k : ℤ) :
    Integrable (fun z => ((uibotQualifier135Busemann false z k -
      uibotQualifier135Busemann false z (k - 1) : ℤ) : ℝ)) μ₁₃₅ ∧
    (∫ z, ((uibotQualifier135Busemann false z k -
      uibotQualifier135Busemann false z (k - 1) : ℤ) : ℝ) ∂μ₁₃₅) = 0 := by
  rw [uibotLaw135_measure_eq]
  exact uibotQualifier135_sdp_mean k

/-- Helper toward Proposition 3.9: Theorem 1.6's transported statement
under the fixed UIBOT law, retaining its existing geometric qualifications. -/
theorem uibotLaw135_busemann_convergence :
    ∃ (a b : ℝ) (μL νL μS νS : ProbabilityMeasure CadlagLocalZero),
      LdpStableHalfLaw a μL ∧ SymmetricStableProcessLaw (2 / 3) a νL ∧
      SdpStableHalfLaw b μS ∧ SymmetricStableProcessLaw (4 / 3) b νS ∧
      Tendsto (uibotLaw135ScalingLaw true) atTop
        (𝓝 ((probabilityProduct μL νL).map wholeLineGlueZero)) ∧
      Tendsto (uibotLaw135ScalingLaw false) atTop
        (𝓝 ((probabilityProduct μS νS).map wholeLineGlueZero)) := by
  exact uibotQualifier135_busemann_convergence

/-- Helper toward Proposition 3.9: Lemma 3.10's complete transported
Borel predicate certificate under the fixed UIBOT law. -/
theorem uibotLaw135_boundary_predicate :
    ∃ S : Set D39GeomRootedMapClass.{0}, MeasurableSet S ∧
      (∀ᵐ z ∂μ₁₃₅, z ∈ S) ∧
      (∀ z, z ∈ S →
      let W := uibotRecoveredCode z
      ∀ n : ℤ,
      (let V := shiftWordInt W n
      ∃ (H : WholePlaneRotationHypothesis V)
        (_h : BoundaryHitWitnesses (shiftedStream V 0)),
        let w := shiftedStream V 0
        let incl := wholePlaneEdgeι V 0
        let lam := m0CutLambdaZero V
        ∃ (P : WholePlaneRightmostRay V H)
          (Q : M0CutLeftmostChain V H (wholePlaneEdgeWest V lam)),
          lam = wholePlaneEdgeι V 0 0 ∧
          P.vertex 0 = wholePlaneEdgeEast V lam ∧
          (∀ P' : WholePlaneRightmostRay V H,
            P'.vertex 0 = wholePlaneEdgeEast V lam →
              P'.vertex = P.vertex ∧ P'.edge = P.edge) ∧
          (∀ Q' : M0CutLeftmostChain V H (wholePlaneEdgeWest V lam),
            Q'.vertex = Q.vertex ∧ Q'.edge = Q.edge) ∧
          incl '' kmswRunBoundaryEdges w =
            {lam} ∪ Set.range P.edge ∪ Set.range Q.edge ∧
          (∀ v : ℕ, RunBoundaryVertex w v ↔
            wholePlaneVertexι V 0 v ∈ Set.range P.vertex ∪ Set.range Q.vertex) ∧
          EdgePresent w 0 ∧
          (∀ e ∈ kmswRunBoundaryEdges w,
            (incl e ∈ ({lam} ∪ Set.range P.edge) → EdgePresent w e) ∧
            (incl e ∈ Set.range Q.edge → ¬ EdgePresent w e)) ∧
          (∀ j : ℕ, wholePlaneEdgePresent V (Q.edge j) ∧
            wholePlaneLeftmostIncomingAt V H (Q.vertex j) (Q.edge j) ∧
            wholePlaneEdgeEast V (Q.edge j) = Q.vertex j) ∧
          (∀ j : ℕ, wholePlaneEdgeWest V (Q.edge j) = Q.vertex (j + 1)) ∧
          (∀ v : ℕ,
            (∃ e, EdgePresent w e ∧ edgeWest w e = v) ∧
            ((∃ e, EdgePresent w e ∧ edgeEast w e = v) ↔
              wholePlaneVertexι V 0 v ∉ Set.range Q.vertex)) ∧
          (∀ v : ℕ, ∃ R : KMSWRunRightmostRay w (H.1 0), R.vertex 0 = v) ∧
          (∀ R R' : KMSWRunRightmostRay w (H.1 0),
            R.vertex 0 = R'.vertex 0 → R.vertex = R'.vertex ∧ R.edge = R'.edge) ∧
          (∀ R : KMSWRunRightmostRay w (H.1 0),
            wholePlaneVertexι V 0 (R.vertex 0) = P.vertex 0 →
              ∀ i, wholePlaneVertexι V 0 (R.vertex i) = P.vertex i ∧
                incl (R.edge i) = P.edge i) ∧
          (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
            ∀ R R' : KMSWRunRightmostRay w (H.1 0),
              R.vertex 0 = x → R'.vertex 0 = x' →
                ∃ s s' : ℕ, 0 < s ∧ 0 < s' ∧ ∀ t : ℕ,
                  R.vertex (s + t) = R'.vertex (s' + t) ∧
                  R.edge (s + t) = R'.edge (s' + t)) ∧
          (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
            ∀ e e' : ℕ, EdgePresent w e → EdgePresent w e' →
              edgeWest w e = x → edgeWest w e' = x' →
              ∀ R R' : KMSWRunRightmostRay w (H.1 0),
                R.vertex 0 = edgeEast w e → R'.vertex 0 = edgeEast w e' →
                  ∃ s s' : ℕ, 1 ≤ s ∧ 1 ≤ s' ∧ ∀ t : ℕ,
                    R.vertex (s - 1 + t) = R'.vertex (s' - 1 + t) ∧
                    R.edge (s - 1 + t) = R'.edge (s' - 1 + t)) ∧
          (∀ x : ℕ, RunBoundaryVertex w x →
            ∃ P1 : WholePlaneRightmostRay V H,
              P1.vertex 0 = wholePlaneVertexι V 0 x) ∧
          (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
            ∀ P1 P2 : WholePlaneRightmostRay V H,
              P1.vertex 0 = wholePlaneVertexι V 0 x →
              P2.vertex 0 = wholePlaneVertexι V 0 x' →
                ∃ s s' : ℕ, 0 < s ∧ 0 < s' ∧ ∀ t : ℕ,
                  P1.vertex (s + t) = P2.vertex (s' + t))) ∧
      Nonempty (WholePlaneStartIso W n)) ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        (∀ n : ℤ,
      (let V := shiftWordInt W n
      ∃ (H : WholePlaneRotationHypothesis V)
        (_h : BoundaryHitWitnesses (shiftedStream V 0)),
        let w := shiftedStream V 0
        let incl := wholePlaneEdgeι V 0
        let lam := m0CutLambdaZero V
        ∃ (P : WholePlaneRightmostRay V H)
          (Q : M0CutLeftmostChain V H (wholePlaneEdgeWest V lam)),
          lam = wholePlaneEdgeι V 0 0 ∧
          P.vertex 0 = wholePlaneEdgeEast V lam ∧
          (∀ P' : WholePlaneRightmostRay V H,
            P'.vertex 0 = wholePlaneEdgeEast V lam →
              P'.vertex = P.vertex ∧ P'.edge = P.edge) ∧
          (∀ Q' : M0CutLeftmostChain V H (wholePlaneEdgeWest V lam),
            Q'.vertex = Q.vertex ∧ Q'.edge = Q.edge) ∧
          incl '' kmswRunBoundaryEdges w =
            {lam} ∪ Set.range P.edge ∪ Set.range Q.edge ∧
          (∀ v : ℕ, RunBoundaryVertex w v ↔
            wholePlaneVertexι V 0 v ∈ Set.range P.vertex ∪ Set.range Q.vertex) ∧
          EdgePresent w 0 ∧
          (∀ e ∈ kmswRunBoundaryEdges w,
            (incl e ∈ ({lam} ∪ Set.range P.edge) → EdgePresent w e) ∧
            (incl e ∈ Set.range Q.edge → ¬ EdgePresent w e)) ∧
          (∀ j : ℕ, wholePlaneEdgePresent V (Q.edge j) ∧
            wholePlaneLeftmostIncomingAt V H (Q.vertex j) (Q.edge j) ∧
            wholePlaneEdgeEast V (Q.edge j) = Q.vertex j) ∧
          (∀ j : ℕ, wholePlaneEdgeWest V (Q.edge j) = Q.vertex (j + 1)) ∧
          (∀ v : ℕ,
            (∃ e, EdgePresent w e ∧ edgeWest w e = v) ∧
            ((∃ e, EdgePresent w e ∧ edgeEast w e = v) ↔
              wholePlaneVertexι V 0 v ∉ Set.range Q.vertex)) ∧
          (∀ v : ℕ, ∃ R : KMSWRunRightmostRay w (H.1 0), R.vertex 0 = v) ∧
          (∀ R R' : KMSWRunRightmostRay w (H.1 0),
            R.vertex 0 = R'.vertex 0 → R.vertex = R'.vertex ∧ R.edge = R'.edge) ∧
          (∀ R : KMSWRunRightmostRay w (H.1 0),
            wholePlaneVertexι V 0 (R.vertex 0) = P.vertex 0 →
              ∀ i, wholePlaneVertexι V 0 (R.vertex i) = P.vertex i ∧
                incl (R.edge i) = P.edge i) ∧
          (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
            ∀ R R' : KMSWRunRightmostRay w (H.1 0),
              R.vertex 0 = x → R'.vertex 0 = x' →
                ∃ s s' : ℕ, 0 < s ∧ 0 < s' ∧ ∀ t : ℕ,
                  R.vertex (s + t) = R'.vertex (s' + t) ∧
                  R.edge (s + t) = R'.edge (s' + t)) ∧
          (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
            ∀ e e' : ℕ, EdgePresent w e → EdgePresent w e' →
              edgeWest w e = x → edgeWest w e' = x' →
              ∀ R R' : KMSWRunRightmostRay w (H.1 0),
                R.vertex 0 = edgeEast w e → R'.vertex 0 = edgeEast w e' →
                  ∃ s s' : ℕ, 1 ≤ s ∧ 1 ≤ s' ∧ ∀ t : ℕ,
                    R.vertex (s - 1 + t) = R'.vertex (s' - 1 + t) ∧
                    R.edge (s - 1 + t) = R'.edge (s' - 1 + t)) ∧
          (∀ x : ℕ, RunBoundaryVertex w x →
            ∃ P1 : WholePlaneRightmostRay V H,
              P1.vertex 0 = wholePlaneVertexι V 0 x) ∧
          (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
            ∀ P1 P2 : WholePlaneRightmostRay V H,
              P1.vertex 0 = wholePlaneVertexι V 0 x →
              P2.vertex 0 = wholePlaneVertexι V 0 x' →
                ∃ s s' : ℕ, 0 < s ∧ 0 < s' ∧ ∀ t : ℕ,
                  P1.vertex (s + t) = P2.vertex (s' + t))) ∧
      Nonempty (WholePlaneStartIso W n)) ↔
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W ∈ S) := by
  rw [uibotLaw135_measure_eq]
  exact uibotQualifier135_boundary_predicate

/-- Helper toward Proposition 3.9: Lemma 3.10's full transported
predicate holds almost everywhere under the fixed UIBOT law. The witnesses
remain inside the single almost-sure statement. -/
theorem uibotLaw135_boundary_predicate_ae :
    ∀ᵐ z ∂μ₁₃₅,
      let W := uibotRecoveredCode z
      ∀ n : ℤ,
      (let V := shiftWordInt W n
      ∃ (H : WholePlaneRotationHypothesis V)
        (_h : BoundaryHitWitnesses (shiftedStream V 0)),
        let w := shiftedStream V 0
        let incl := wholePlaneEdgeι V 0
        let lam := m0CutLambdaZero V
        ∃ (P : WholePlaneRightmostRay V H)
          (Q : M0CutLeftmostChain V H (wholePlaneEdgeWest V lam)),
          lam = wholePlaneEdgeι V 0 0 ∧
          P.vertex 0 = wholePlaneEdgeEast V lam ∧
          (∀ P' : WholePlaneRightmostRay V H,
            P'.vertex 0 = wholePlaneEdgeEast V lam →
              P'.vertex = P.vertex ∧ P'.edge = P.edge) ∧
          (∀ Q' : M0CutLeftmostChain V H (wholePlaneEdgeWest V lam),
            Q'.vertex = Q.vertex ∧ Q'.edge = Q.edge) ∧
          incl '' kmswRunBoundaryEdges w =
            {lam} ∪ Set.range P.edge ∪ Set.range Q.edge ∧
          (∀ v : ℕ, RunBoundaryVertex w v ↔
            wholePlaneVertexι V 0 v ∈ Set.range P.vertex ∪ Set.range Q.vertex) ∧
          EdgePresent w 0 ∧
          (∀ e ∈ kmswRunBoundaryEdges w,
            (incl e ∈ ({lam} ∪ Set.range P.edge) → EdgePresent w e) ∧
            (incl e ∈ Set.range Q.edge → ¬ EdgePresent w e)) ∧
          (∀ j : ℕ, wholePlaneEdgePresent V (Q.edge j) ∧
            wholePlaneLeftmostIncomingAt V H (Q.vertex j) (Q.edge j) ∧
            wholePlaneEdgeEast V (Q.edge j) = Q.vertex j) ∧
          (∀ j : ℕ, wholePlaneEdgeWest V (Q.edge j) = Q.vertex (j + 1)) ∧
          (∀ v : ℕ,
            (∃ e, EdgePresent w e ∧ edgeWest w e = v) ∧
            ((∃ e, EdgePresent w e ∧ edgeEast w e = v) ↔
              wholePlaneVertexι V 0 v ∉ Set.range Q.vertex)) ∧
          (∀ v : ℕ, ∃ R : KMSWRunRightmostRay w (H.1 0), R.vertex 0 = v) ∧
          (∀ R R' : KMSWRunRightmostRay w (H.1 0),
            R.vertex 0 = R'.vertex 0 → R.vertex = R'.vertex ∧ R.edge = R'.edge) ∧
          (∀ R : KMSWRunRightmostRay w (H.1 0),
            wholePlaneVertexι V 0 (R.vertex 0) = P.vertex 0 →
              ∀ i, wholePlaneVertexι V 0 (R.vertex i) = P.vertex i ∧
                incl (R.edge i) = P.edge i) ∧
          (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
            ∀ R R' : KMSWRunRightmostRay w (H.1 0),
              R.vertex 0 = x → R'.vertex 0 = x' →
                ∃ s s' : ℕ, 0 < s ∧ 0 < s' ∧ ∀ t : ℕ,
                  R.vertex (s + t) = R'.vertex (s' + t) ∧
                  R.edge (s + t) = R'.edge (s' + t)) ∧
          (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
            ∀ e e' : ℕ, EdgePresent w e → EdgePresent w e' →
              edgeWest w e = x → edgeWest w e' = x' →
              ∀ R R' : KMSWRunRightmostRay w (H.1 0),
                R.vertex 0 = edgeEast w e → R'.vertex 0 = edgeEast w e' →
                  ∃ s s' : ℕ, 1 ≤ s ∧ 1 ≤ s' ∧ ∀ t : ℕ,
                    R.vertex (s - 1 + t) = R'.vertex (s' - 1 + t) ∧
                    R.edge (s - 1 + t) = R'.edge (s' - 1 + t)) ∧
          (∀ x : ℕ, RunBoundaryVertex w x →
            ∃ P1 : WholePlaneRightmostRay V H,
              P1.vertex 0 = wholePlaneVertexι V 0 x) ∧
          (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
            ∀ P1 P2 : WholePlaneRightmostRay V H,
              P1.vertex 0 = wholePlaneVertexι V 0 x →
              P2.vertex 0 = wholePlaneVertexι V 0 x' →
                ∃ s s' : ℕ, 0 < s ∧ 0 < s' ∧ ∀ t : ℕ,
                  P1.vertex (s + t) = P2.vertex (s' + t))) ∧
      Nonempty (WholePlaneStartIso W n) := by
  obtain ⟨S, _, hS, hpred, _⟩ := uibotLaw135_boundary_predicate
  filter_upwards [hS] with z hz
  exact hpred z hz

/-- Helper toward Proposition 3.9: Proposition 5.1's transported statement
under the fixed UIBOT law, retaining its existing geometric qualifications. -/
theorem uibotLaw135_future_map_law :
    (∀ n : ℤ, IndepFun
      (fun z => (uibotGeomFutureObservables z n).1.1)
      (fun z => (uibotGeomFutureObservables z n).1.2) μ₁₃₅) ∧
    (∀ n : ℤ, (μ₁₃₅).map
      (fun z => (uibotGeomFutureObservables z n).1.1) =
        iidCodeMeasure.map (fun w => pitmanCode (fun i => w (i + 1)))) := by
  rw [uibotLaw135_measure_eq]
  exact uibotQualifier135_future_map_law

/-- Helper toward Proposition 3.9: Proposition 5.1's transported statement
under the fixed UIBOT law, retaining its existing geometric qualifications. -/
theorem uibotLaw135_future_rooted_maps :
    ∀ᵐ z ∂μ₁₃₅, ∀ n : ℤ,
      let W := uibotRecoveredCode z
      let u := fun i => futureMapShiftedCodePath n W (i + 1)
      u = shiftedStream (fun k => W (k + n)) 0 ∧
        ∃ (h : HasFlowLineHits u) (hfin_hat : hatLimitFiniteIncidence u)
          (hfin_primed : primedLimitFiniteIncidence u) (hb : BoundaryHitWitnesses u),
          (uibotGeomFutureObservables z n).1.1 = hatCodes u h ∧
          (uibotGeomFutureObservables z n).1.2 = primedCode (primedSimInput u) h ∧
          hatRootedMapClause u h hfin_hat ∧ primedRootedMapClause u h hfin_primed hb := by
  rw [uibotLaw135_measure_eq]
  exact uibotQualifier135_future_rooted_maps

/-- Helper toward Proposition 3.9: Lemma 5.2's transported statement
under the fixed UIBOT law, retaining its existing geometric qualifications. -/
theorem uibotLaw135_stopped_laws (k : ℤ) :
    (μ₁₃₅).map (fun z => (uibotGeomFutureObservables z k).2) =
      (μ₁₃₅).map (fun z => (uibotGeomFutureObservables z 0).2) ∧
    (μ₁₃₅).map (uibotQualifier135StoppedHat k) =
      iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) := by
  rw [uibotLaw135_measure_eq]
  exact uibotQualifier135_stopped_laws k

/-- Helper toward Proposition 3.9: Lemma 5.2's transported statement
under the fixed UIBOT law, retaining its existing geometric qualifications. -/
theorem uibotLaw135_directed_contain :
    ∀ᵐ z ∂μ₁₃₅,
      let W := uibotRecoveredCode z
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∀ k : ℤ,
        uibotGeomBoundaryTimes z k = boundaryHitTime (shiftedStream W 0) h k ∧
        (fun i => (uibotGeomFutureObservables z k).2 (i + 1)) =
          (fun i => shiftedStream W 0 (uibotGeomBoundaryTimes z k + i)) ∧
        (∃ hτ : HasFlowLineHits
            (fun i => shiftedStream W 0 (uibotGeomBoundaryTimes z k + i)),
          uibotQualifier135StoppedHat k z =
            hatCodes (fun i => shiftedStream W 0 (uibotGeomBoundaryTimes z k + i)) hτ) ∧
        M0CutShiftContainment W H h hLL k ∧ boundaryFutureRootedMapClause W h k := by
  rw [uibotLaw135_measure_eq]
  exact uibotQualifier135_directed_contain

/-- Helper toward Proposition 3.9: Lemma 5.3's complete transported
Borel predicate certificate under the fixed UIBOT law. -/
theorem uibotLaw135_infty_cut_predicate :
    ∃ S : Set D39GeomRootedMapClass.{0}, MeasurableSet S ∧
      (∀ᵐ z ∂μ₁₃₅, z ∈ S) ∧
      (∀ z, z ∈ S →
      let W := uibotRecoveredCode z
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      let w := shiftedStream W 0
      let V := wholePlaneVertexι W 0
      let E := wholePlaneEdgeι W 0
      let D := m0CutData W H h hLL
      (Function.Injective V ∧
      Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
      Function.Injective E ∧
      Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
      (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
      ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
        (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
        wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
        wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
        wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
      (∀ e, EdgePresent w e ↔
        (wholePlaneEdgePresent W (E e) ∧
          ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
      (∀ e, (D).missing (E e) ↔
        ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
      (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
        ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
      (∀ a b, (D).sdp (V a) (V b) =
        DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ k k', (D).sdp ((D).x k) ((D).x k') =
        DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
      (∀ k k', (D).ldp ((D).x k) ((D).x k') =
        presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
      ∀ k k' : ℤ, k < k' →
        ∃ v : ℕ → WholePlaneVertex W,
          Function.Injective v ∧
          (∀ m, v m ∈ m0CutLeftVertices W H D.seam) ∧
          ∀ ell : ℤ, ell ∈ Set.Icc k k' →
            ∀ y : ℕ → WholePlaneVertex W,
              Function.Injective y →
              (∀ j, m0CutReachable W H D.seam (D.x ell) (y j)) →
              ∀ m, ∃ J, ∀ j, J ≤ j →
                ∀ n : ℕ, ∀ p : Fin (n + 1) → WholePlaneVertex W,
                  p 0 = D.x ell →
                  p (Fin.last n) = y j →
                  (∀ i : Fin n,
                    m0CutDirectedStep W H D.seam
                      (p i.castSucc) (p i.succ)) →
                  ∃ i, p i = v m) ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        (∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      let w := shiftedStream W 0
      let V := wholePlaneVertexι W 0
      let E := wholePlaneEdgeι W 0
      let D := m0CutData W H h hLL
      (Function.Injective V ∧
      Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
      Function.Injective E ∧
      Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
      (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
      ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
        (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
        wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
        wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
        wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
      (∀ e, EdgePresent w e ↔
        (wholePlaneEdgePresent W (E e) ∧
          ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
      (∀ e, (D).missing (E e) ↔
        ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
      (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
        ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
      (∀ a b, (D).sdp (V a) (V b) =
        DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ k k', (D).sdp ((D).x k) ((D).x k') =
        DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
      (∀ k k', (D).ldp ((D).x k) ((D).x k') =
        presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
      ∀ k k' : ℤ, k < k' →
        ∃ v : ℕ → WholePlaneVertex W,
          Function.Injective v ∧
          (∀ m, v m ∈ m0CutLeftVertices W H D.seam) ∧
          ∀ ell : ℤ, ell ∈ Set.Icc k k' →
            ∀ y : ℕ → WholePlaneVertex W,
              Function.Injective y →
              (∀ j, m0CutReachable W H D.seam (D.x ell) (y j)) →
              ∀ m, ∃ J, ∀ j, J ≤ j →
                ∀ n : ℕ, ∀ p : Fin (n + 1) → WholePlaneVertex W,
                  p 0 = D.x ell →
                  p (Fin.last n) = y j →
                  (∀ i : Fin n,
                    m0CutDirectedStep W H D.seam
                      (p i.castSucc) (p i.succ)) →
                  ∃ i, p i = v m) ↔
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W ∈ S) := by
  rw [uibotLaw135_measure_eq]
  exact uibotQualifier135_infty_cut_predicate

/-- Helper toward Proposition 3.9: Lemma 5.3's full transported
predicate holds almost everywhere under the fixed UIBOT law. The witnesses
remain inside the single almost-sure statement. -/
theorem uibotLaw135_infty_cut_predicate_ae :
    ∀ᵐ z ∂μ₁₃₅,
      let W := uibotRecoveredCode z
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      let w := shiftedStream W 0
      let V := wholePlaneVertexι W 0
      let E := wholePlaneEdgeι W 0
      let D := m0CutData W H h hLL
      (Function.Injective V ∧
      Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
      Function.Injective E ∧
      Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
      (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
      ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
        (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
        wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
        wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
        wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
      (∀ e, EdgePresent w e ↔
        (wholePlaneEdgePresent W (E e) ∧
          ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
      (∀ e, (D).missing (E e) ↔
        ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
      (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
        ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
      (∀ a b, (D).sdp (V a) (V b) =
        DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ k k', (D).sdp ((D).x k) ((D).x k') =
        DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
      (∀ k k', (D).ldp ((D).x k) ((D).x k') =
        presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
      ∀ k k' : ℤ, k < k' →
        ∃ v : ℕ → WholePlaneVertex W,
          Function.Injective v ∧
          (∀ m, v m ∈ m0CutLeftVertices W H D.seam) ∧
          ∀ ell : ℤ, ell ∈ Set.Icc k k' →
            ∀ y : ℕ → WholePlaneVertex W,
              Function.Injective y →
              (∀ j, m0CutReachable W H D.seam (D.x ell) (y j)) →
              ∀ m, ∃ J, ∀ j, J ≤ j →
                ∀ n : ℕ, ∀ p : Fin (n + 1) → WholePlaneVertex W,
                  p 0 = D.x ell →
                  p (Fin.last n) = y j →
                  (∀ i : Fin n,
                    m0CutDirectedStep W H D.seam
                      (p i.castSucc) (p i.succ)) →
                  ∃ i, p i = v m := by
  obtain ⟨S, _, hS, hpred, _⟩ := uibotLaw135_infty_cut_predicate
  filter_upwards [hS] with z hz
  exact hpred z hz

/-- Helper toward Proposition 3.9: Lemma 5.4's complete transported
Borel predicate certificate under the fixed UIBOT law. -/
theorem uibotLaw135_geo_infty_predicate :
    ∃ S : Set D39GeomRootedMapClass.{0}, MeasurableSet S ∧
      (∀ᵐ z ∂μ₁₃₅, z ∈ S) ∧
      (∀ z, z ∈ S →
      let W := uibotRecoveredCode z
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      let w := shiftedStream W 0
      let V := wholePlaneVertexι W 0
      let E := wholePlaneEdgeι W 0
      let D := m0CutData W H h hLL
      (Function.Injective V ∧
      Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
      Function.Injective E ∧
      Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
      (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
      ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
        (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
        wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
        wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
        wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
      (∀ e, EdgePresent w e ↔
        (wholePlaneEdgePresent W (E e) ∧
          ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
      (∀ e, (D).missing (E e) ↔
        ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
      (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
        ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
      (∀ a b, (D).sdp (V a) (V b) =
        DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ k k', (D).sdp ((D).x k) ((D).x k') =
        DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
      (∀ k k', (D).ldp ((D).x k) ((D).x k') =
        presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
      ∀ longest : Bool,
      ∃ R : ℤ → KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
        (∀ k, (R k).vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
          (T k).edge = (R k).edge ∧
          (∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
            ((T k).initial n).1.id ((T k).edge n))) ∧
        (∀ k, CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        (∀ k Q, CutLeftmostXdp W H h hp hLL longest k Q (T k) → Q = P k) ∧
        ∀ k k' : ℤ, ∃ i j : ℕ, ∀ n : ℕ,
          wholePlaneEdgeι W 0 ((P k).codePath.edge (i + n)) =
            wholePlaneEdgeι W 0 ((P k').codePath.edge (j + n))) ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        (∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      let w := shiftedStream W 0
      let V := wholePlaneVertexι W 0
      let E := wholePlaneEdgeι W 0
      let D := m0CutData W H h hLL
      (Function.Injective V ∧
      Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
      Function.Injective E ∧
      Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
      (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
      ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
        (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
        wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
        wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
        wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
      (∀ e, EdgePresent w e ↔
        (wholePlaneEdgePresent W (E e) ∧
          ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
      (∀ e, (D).missing (E e) ↔
        ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
      (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
        ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
      (∀ a b, (D).sdp (V a) (V b) =
        DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ k k', (D).sdp ((D).x k) ((D).x k') =
        DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
      (∀ k k', (D).ldp ((D).x k) ((D).x k') =
        presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
      ∀ longest : Bool,
      ∃ R : ℤ → KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
        (∀ k, (R k).vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
          (T k).edge = (R k).edge ∧
          (∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
            ((T k).initial n).1.id ((T k).edge n))) ∧
        (∀ k, CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        (∀ k Q, CutLeftmostXdp W H h hp hLL longest k Q (T k) → Q = P k) ∧
        ∀ k k' : ℤ, ∃ i j : ℕ, ∀ n : ℕ,
          wholePlaneEdgeι W 0 ((P k).codePath.edge (i + n)) =
            wholePlaneEdgeι W 0 ((P k').codePath.edge (j + n))) ↔
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W ∈ S) := by
  rw [uibotLaw135_measure_eq]
  exact uibotQualifier135_geo_infty_predicate

/-- Helper toward Proposition 3.9: Lemma 5.4's full transported
predicate holds almost everywhere under the fixed UIBOT law. The witnesses
remain inside the single almost-sure statement. -/
theorem uibotLaw135_geo_infty_predicate_ae :
    ∀ᵐ z ∂μ₁₃₅,
      let W := uibotRecoveredCode z
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      let w := shiftedStream W 0
      let V := wholePlaneVertexι W 0
      let E := wholePlaneEdgeι W 0
      let D := m0CutData W H h hLL
      (Function.Injective V ∧
      Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
      Function.Injective E ∧
      Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
      (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
      ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
        (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
        wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
        wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
        wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
      (∀ e, EdgePresent w e ↔
        (wholePlaneEdgePresent W (E e) ∧
          ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
      (∀ e, (D).missing (E e) ↔
        ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
      (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
        ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
      (∀ a b, (D).sdp (V a) (V b) =
        DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ k k', (D).sdp ((D).x k) ((D).x k') =
        DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
      (∀ k k', (D).ldp ((D).x k) ((D).x k') =
        presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
      ∀ longest : Bool,
      ∃ R : ℤ → KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
        (∀ k, (R k).vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
          (T k).edge = (R k).edge ∧
          (∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
            ((T k).initial n).1.id ((T k).edge n))) ∧
        (∀ k, CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        (∀ k Q, CutLeftmostXdp W H h hp hLL longest k Q (T k) → Q = P k) ∧
        ∀ k k' : ℤ, ∃ i j : ℕ, ∀ n : ℕ,
          wholePlaneEdgeι W 0 ((P k).codePath.edge (i + n)) =
            wholePlaneEdgeι W 0 ((P k').codePath.edge (j + n)) := by
  obtain ⟨S, _, hS, hpred, _⟩ := uibotLaw135_geo_infty_predicate
  filter_upwards [hS] with z hz
  exact hpred z hz

/-- Helper toward Proposition 3.9: Lemma 5.5's transported statement
under the fixed UIBOT law, retaining its existing geometric qualifications. -/
theorem uibotLaw135_geo_infty_ind (default : GeometricSideClass)
    (x : XDP) (k : ℤ) :
    ((fun z => (uibotGeomSideSliceObservables z x k).1.1) =ᵐ[μ₁₃₅]
      fun z => some (lemma55OptionClassValue default
        (uibotGeomSideSliceObservables z x k).1.1)) ∧
    ((fun z => (uibotGeomSideSliceObservables z x k).1.2) =ᵐ[μ₁₃₅]
      fun z => some (lemma55OptionClassValue default
        (uibotGeomSideSliceObservables z x k).1.2)) ∧
    IndepFun
      (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).1.1)
      (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).1.2)
      μ₁₃₅ ∧
    (0 ≤ k → (μ₁₃₅).map
      (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).1.2) =
      (μ₁₃₅).map
        (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x 0).1.2)) ∧
    (k ≤ 0 → (μ₁₃₅).map
      (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).1.1) =
      (μ₁₃₅).map
        (fun z => forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x 0).1.1)) := by
  rw [uibotLaw135_measure_eq]
  exact uibotQualifier135_geo_infty_ind default x k

/-- Helper toward Proposition 3.9: Lemma 5.6's transported statement
under the fixed UIBOT law, retaining its existing geometric qualifications. -/
theorem uibotLaw135_geo_slice (default : GeometricSideClass) (x : XDP) :
    ∃ Phi : ℤ → D39GeomRootedMapClass.{0} → Option GeometricSideClass,
      (∀ k, Measurable (Phi k)) ∧
      (∀ k, ∀ᵐ z ∂μ₁₃₅, (Phi k z).isSome) ∧
      (∀ᵐ z ∂μ₁₃₅,
        let W := uibotRecoveredCode z
        ∃ H : WholePlaneRotationHypothesis W,
        ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
        ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
        ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
          (boundaryPresentVertex (shiftedStream W 0) h k),
        ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k
          (if x = XDP.ldp then true else false),
        (∀ k, Xdp.CutLeftmostXdp W H h hp hLL
          (if x = XDP.ldp then true else false) k (P k) (T k)) ∧
        (∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL
          (if x = XDP.ldp then true else false) k Q (T k) → Q = P k) ∧
        ∀ k : ℤ, ∃ a b : ℕ,
          ∃ hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b,
          Phi k z = some (geometricSideClass
            (m0CutGeodesicSlice (hp := hp) P k a b hab))) ∧
      iIndepFun (fun k => forgetMarksOptionClassValue default ∘ Phi k)
        μ₁₃₅ ∧
      (∀ k : ℤ, 1 ≤ k → (μ₁₃₅).map
        (forgetMarksOptionClassValue default ∘ Phi k) =
        (μ₁₃₅).map (forgetMarksOptionClassValue default ∘ Phi 1)) ∧
      (∀ k : ℤ, k ≤ 0 → (μ₁₃₅).map
        (forgetMarksOptionClassValue default ∘ Phi k) =
        (μ₁₃₅).map (forgetMarksOptionClassValue default ∘ Phi 0)) := by
  rw [uibotLaw135_measure_eq]
  exact uibotQualifier135_geo_slice default x

/-- Helper toward Proposition 3.9: Lemma 5.7's complete transported
Borel predicate certificate under the fixed UIBOT law. -/
theorem uibotLaw135_busemann_coalescence_predicate :
    ∃ S : Set D39GeomRootedMapClass.{0}, MeasurableSet S ∧
      (∀ᵐ z ∂μ₁₃₅, z ∈ S) ∧
      (∀ z, z ∈ S →
      let W := uibotRecoveredCode z
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      let w := shiftedStream W 0
      let V := wholePlaneVertexι W 0
      let E := wholePlaneEdgeι W 0
      let D := m0CutData W H h hLL
      (Function.Injective V ∧
      Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
      Function.Injective E ∧
      Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
      (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
      ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
        (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
        wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
        wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
        wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
      (∀ e, EdgePresent w e ↔
        (wholePlaneEdgePresent W (E e) ∧
          ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
      (∀ e, (D).missing (E e) ↔
        ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
      (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
        ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
      (∀ a b, (D).sdp (V a) (V b) =
        DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ k k', (D).sdp ((D).x k) ((D).x k') =
        DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
      (∀ k k', (D).ldp ((D).x k) ((D).x k') =
        presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
      ∀ longest : Bool,
      ∃ R : ℤ → KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
        (∀ k, (R k).vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
          (T k).edge = (R k).edge ∧
          (∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
            ((T k).initial n).1.id ((T k).edge n))) ∧
        (∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        (∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL longest k Q (T k) → Q = P k) ∧
        (∃! X : ℤ → ℤ, if longest then
          IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X else
          IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X) ∧
        (∀ k : ℤ, ∃! q : ℕ × ℕ,
          M0CutLeastEdgeCoalescence (P k) (P (k - 1)) q.1 q.2) ∧
        ∀ X : ℤ → ℤ,
          (if longest then IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X
            else IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X) →
          ∀ (k : ℤ) (theta theta' : ℕ),
            M0CutLeastEdgeCoalescence (P k) (P (k - 1)) theta theta' →
            X k - X (k - 1) = (theta : ℤ) - (theta' : ℤ)) ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        (∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      let w := shiftedStream W 0
      let V := wholePlaneVertexι W 0
      let E := wholePlaneEdgeι W 0
      let D := m0CutData W H h hLL
      (Function.Injective V ∧
      Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
      Function.Injective E ∧
      Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
      (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
      ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
        (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
        wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
        wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
        wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
      (∀ e, EdgePresent w e ↔
        (wholePlaneEdgePresent W (E e) ∧
          ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
      (∀ e, (D).missing (E e) ↔
        ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
      (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
        ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
      (∀ a b, (D).sdp (V a) (V b) =
        DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ k k', (D).sdp ((D).x k) ((D).x k') =
        DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
      (∀ k k', (D).ldp ((D).x k) ((D).x k') =
        presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
      ∀ longest : Bool,
      ∃ R : ℤ → KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
        (∀ k, (R k).vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
          (T k).edge = (R k).edge ∧
          (∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
            ((T k).initial n).1.id ((T k).edge n))) ∧
        (∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        (∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL longest k Q (T k) → Q = P k) ∧
        (∃! X : ℤ → ℤ, if longest then
          IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X else
          IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X) ∧
        (∀ k : ℤ, ∃! q : ℕ × ℕ,
          M0CutLeastEdgeCoalescence (P k) (P (k - 1)) q.1 q.2) ∧
        ∀ X : ℤ → ℤ,
          (if longest then IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X
            else IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X) →
          ∀ (k : ℤ) (theta theta' : ℕ),
            M0CutLeastEdgeCoalescence (P k) (P (k - 1)) theta theta' →
            X k - X (k - 1) = (theta : ℤ) - (theta' : ℤ)) ↔
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W ∈ S) := by
  rw [uibotLaw135_measure_eq]
  exact uibotQualifier135_busemann_coalescence_predicate

/-- Helper toward Proposition 3.9: Lemma 5.7's full transported
predicate holds almost everywhere under the fixed UIBOT law. The witnesses
remain inside the single almost-sure statement. -/
theorem uibotLaw135_busemann_coalescence_predicate_ae :
    ∀ᵐ z ∂μ₁₃₅,
      let W := uibotRecoveredCode z
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      let w := shiftedStream W 0
      let V := wholePlaneVertexι W 0
      let E := wholePlaneEdgeι W 0
      let D := m0CutData W H h hLL
      (Function.Injective V ∧
      Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
      Function.Injective E ∧
      Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
      (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
      ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
        (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
        wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
        wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
        wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
      (∀ e, EdgePresent w e ↔
        (wholePlaneEdgePresent W (E e) ∧
          ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
      (∀ e, (D).missing (E e) ↔
        ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
      (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
        ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
      (∀ a b, (D).sdp (V a) (V b) =
        DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ k k', (D).sdp ((D).x k) ((D).x k') =
        DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
      (∀ k k', (D).ldp ((D).x k) ((D).x k') =
        presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
      ∀ longest : Bool,
      ∃ R : ℤ → KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
        (∀ k, (R k).vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
          (T k).edge = (R k).edge ∧
          (∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
            ((T k).initial n).1.id ((T k).edge n))) ∧
        (∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        (∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL longest k Q (T k) → Q = P k) ∧
        (∃! X : ℤ → ℤ, if longest then
          IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X else
          IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X) ∧
        (∀ k : ℤ, ∃! q : ℕ × ℕ,
          M0CutLeastEdgeCoalescence (P k) (P (k - 1)) q.1 q.2) ∧
        ∀ X : ℤ → ℤ,
          (if longest then IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X
            else IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X) →
          ∀ (k : ℤ) (theta theta' : ℕ),
            M0CutLeastEdgeCoalescence (P k) (P (k - 1)) theta theta' →
            X k - X (k - 1) = (theta : ℤ) - (theta' : ℤ) := by
  obtain ⟨S, _, hS, hpred, _⟩ := uibotLaw135_busemann_coalescence_predicate
  filter_upwards [hS] with z hz
  exact hpred z hz

/- Remaining consumer qualifications (law transport alone does not discharge them):
1.3: intrinsic cut inclusion, boundary order, orientations and actual faces.
1.4: intrinsic labeled cut distances and the complete Busemann characterization.
1.6: equality of both entire intrinsic sequences and their rescaled path laws.
1.7: joint identification of the full intrinsic increment sequences.
1.8: the same sequence identification, with shared tail constants and means.
3.8: compose source realization with the simultaneous boundary/start isomorphisms.
5.1: compose source realization with the retained rooted-map clauses.
5.2: intrinsic labels, first active-edge times and stopped submap inclusions.
5.3: intrinsic cut directed paths with the existing vertex-first quantifier order.
5.4: intrinsic leftmost geodesics, actual edges and coalescence.
5.5: actual side submaps, retained boundary/faces and mark-forgetting convention.
5.6: actual slice geometry, least offsets, included segments and faces.
5.7: joint intrinsic sequence, geodesic and least-offset identification. -/

end DirectedDistances.PaperProofs.Section3
end

