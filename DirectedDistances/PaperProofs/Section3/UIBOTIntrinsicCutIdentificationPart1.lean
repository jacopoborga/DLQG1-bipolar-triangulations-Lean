/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTCodeRecoveryPart7
public import DirectedDistances.PaperProofs.Section3.UIBOTWholePlaneSourcePart4
public import DirectedDistances.PaperProofs.Section3.UIBOTQualifierPart2
public import DirectedDistances.Paper.Section1.FutureMap










public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1
open MeasureTheory Filter
open scoped Classical

/-- Consumer helper for Definition 1.3 and Proposition 3.9: on one iid
conull event the recovered ambient construction represents the sampled class,
with the complete characterized cut and the original walk normalization.
Every representative of that same class admits an actual rooted geometric
isomorphism from this recovered construction. -/
theorem uibotIntrinsicCut_sample_realization :
    ∀ᵐ U ∂wholePlaneIIDCodeMeasure,
      let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved U
      let W := uibotRecoveredCode z
      wholePlaneWordIntegral W 0 = (0, 0) ∧
      (∀ t : ℤ, wholePlaneWordIntegral W (t + 1) - wholePlaneWordIntegral W t =
        lazyTwoDimensionalStep (W t)) ∧
      ∃ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
      let hLL := fun (k : ℤ) (_hk : k ≤ 0) => hp
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))
      let D := m0CutData W H h hLL
      let P := monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))
      let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
      let f := seamFun (shiftedStream W 0) h (H.1 0)
      z = Quotient.mk d39DomainSetoid (uibotWholePlaneSourceDomain W H G hp) ∧
      (∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
        Nonempty (D39GeomRootedMapIsoV2
          (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
          A.map A.root)) ∧
      (D.betaR.vertex 0 = D.x 1) ∧
      (∀ n, wholePlaneRightmostOutgoingAt W H (D.betaR.vertex n) (D.betaR.edge n) ∧
        wholePlaneEdgeEast W (D.betaR.edge n) = D.betaR.vertex (n + 1)) ∧
      (D.betaL.vertex 0 = D.x 0) ∧
      (∀ n, wholePlaneLeftmostIncomingAt W H (D.betaL.vertex n) (D.betaL.edge n) ∧
        wholePlaneEdgeWest W (D.betaL.edge n) = D.betaL.vertex (n + 1)) ∧
      (D.rootDart.1 = m0CutLambdaZero W) ∧
      Function.Injective (futureMapInternalGluedFace W H h hpast) ∧
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
      (∀ F : G.Face, (∃ q, futureMapInternalGluedFace W H h hpast q = F) ↔
        F.val ⊆ {z : ℂ | f z.re < z.im}) ∧
      (∀ d q, G.dartBorders (wholePlaneDartι W 0 d)
        (futureMapInternalGluedFace W H h hpast q) ↔ Quotient.mk _ d = q.val) ∧
      (∀ d, P.dartBorders d
        (futureMapFaceOrbitEquiv W H h (futureMapExteriorOrbit W H)) ↔
        d.2 = true ∧ D.seam (wholePlaneEdgeι W 0 d.1)) ∧
      (∀ q : FutureMapInternalFaceOrbit W H,
        ∃ j : TriangleCreationTime (shiftedStream W 0),
          {a | G.dartBorders a (futureMapInternalGluedFace W H h hpast q)} =
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
  filter_upwards [uibotRecoveredCode_ae,
    uibotMeasurableWholePlaneClassMap_ae_normalized_source,
    DirectedDistances.Paper.Section1.defn_future_map] with U hcode hsource hcut
  dsimp only
  rw [hcode]
  obtain ⟨hz, hi, H, h, hpast, hp, hclass, _⟩ := hsource
  obtain ⟨Hc, hc, hLLc, hpastc, hcut⟩ := hcut
  refine ⟨hz, hi, H, h, hpast, hp, hclass, ?_, hcut⟩
  intro A hA
  exact Quotient.exact (hclass.symm.trans hA.symm)

/-- Consumer helper for Definition 1.3: an actual isomorphism between two
source realizations transports all cut marks, edge identities, incidence,
missing tags, rotation and open internal-face regions. Recurrence in earlier
runs is derived from the supplied boundary witnesses. -/
theorem uibotIntrinsicCut_geometric_transport
    (W W' : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (H' : WholePlaneRotationHypothesis W')
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (h' : BoundaryHitWitnesses (shiftedStream W' 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hpast' : BoundaryHitWitnesses (kmswPastCode W'))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (hp' : ∀ e : WholePlaneEdge W', wholePlaneEdgePresent W' e)
    (D : M0CutData W H) (D' : M0CutData W' H') :
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let G' := WholePlanePastGlueDrawing.glueDrawing W' h' hpast' H'
    ∀ I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G'),
    ((∀ k : ℤ, I.vertexEquiv (D.x k) = D'.x k) ∧
    (∀ n : ℕ, I.vertexEquiv (D.betaR.vertex n) = D'.betaR.vertex n ∧
      I.edgeEquiv (D.betaR.edge n) = D'.betaR.edge n ∧
      I.vertexEquiv (D.betaL.vertex n) = D'.betaL.vertex n ∧
      I.edgeEquiv (D.betaL.edge n) = D'.betaL.edge n) ∧
    uibotCutGeomDartEquiv I D.rootDart = D'.rootDart ∧
    (∀ v : WholePlaneVertex W,
      v ∈ m0CutLeftVertices W H D.seam ↔
        I.vertexEquiv v ∈ m0CutLeftVertices W' H' D'.seam) ∧
    (∀ a : WholePlaneEdge W,
      (a ∈ D.edges ↔ I.edgeEquiv a ∈ D'.edges) ∧
      (D.seam a ↔ D'.seam (I.edgeEquiv a)) ∧
      (D.missing a ↔ D'.missing (I.edgeEquiv a))) ∧
    (∀ d : WholePlaneDart W,
      (d ∈ D.darts ↔ uibotCutGeomDartEquiv I d ∈ D'.darts) ∧
      (D.tail d ↔ D'.tail (uibotCutGeomDartEquiv I d))) ∧
    (∀ d a : WholePlaneDart W,
      D.IsRot d a ↔ D'.IsRot (uibotCutGeomDartEquiv I d)
        (uibotCutGeomDartEquiv I a))) ∧
    (∀ e : WholePlaneEdge W,
      I.vertexEquiv (wholePlaneEdgeWest W e) = wholePlaneEdgeWest W' (I.edgeEquiv e) ∧
      I.vertexEquiv (wholePlaneEdgeEast W e) = wholePlaneEdgeEast W' (I.edgeEquiv e)) ∧
    ∃ f : FutureMapInternalFaceOrbit W H ≃ FutureMapInternalFaceOrbit W' H',
      ∀ q : FutureMapInternalFaceOrbit W H,
        I.h '' (futureMapInternalGluedFace W H h hpast q).val =
          (futureMapInternalGluedFace W' H' h' hpast' (f q)).val := by
  intro G G' I
  have hh (N : ℕ) := boundaryHitWitnesses_of_le W (Nat.zero_le N) h
  have hh' (N : ℕ) := boundaryHitWitnesses_of_le W' (Nat.zero_le N) h'
  refine ⟨uibotCut_geometric_iso_marks hh hh' I D D', ?_, ?_⟩
  · intro e
    exact ⟨uibotCutGeomDartEquiv_vertex I (e, false),
      uibotCutGeomDartEquiv_vertex I (e, true)⟩
  · let J := ((uibotWholePlaneSourceIso W H G hp).symm.trans I).trans
      (uibotWholePlaneSourceIso W' H' G' hp')
    exact uibotCut_geometric_internal_face_transport W W' H H' h h' hpast hpast' hp hp' J

/- The complete sample statement was separately elaborated by the prescribed
and fresh native replay remain mandatory; this file provides neither.

The class-law reconstruction still needed, with no additional premise, is
  ∀ᵐ z ∂(uibotWholePlaneGeometricProbabilityLaw
    uibotDeterministicComparison_proved : Measure D39GeomRootedMapClass.{0}),
    uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved
      (uibotRecoveredCode z) = z.
The inspected D39GeometricClassMetric, D39GeometricClassBorel and
D39GeometricZeroDistanceEvents supply a pseudo-emetric and Borel-event
transport, but no MeasurableEq instance or finite-ball-to-global-class
equality theorem. Therefore ae_map_iff cannot yet transfer this equality event.
The theorem above instead states its precise, proved iid-sample version.

The exact missing intrinsic type interface is
  IntrinsicFutureCut (A : D39DomainRootedMap.{0}) : Type
with data on A itself (no W, recoveredCode or chosen isomorphism binder):
  vertices : Set A.V
  edges : Set A.E
  faces : Set A.map.toPlaneGraphDrawing.Face
  seam : A.E → Prop
  missing : A.E → Prop
  tail : A.E × Bool → Prop
  rotation : (A.E × Bool) → (A.E × Bool) → Prop
  x : ℤ → A.V
  betaRVertex betaLVertex : ℕ → A.V
  betaREdge betaLEdge : ℕ → A.E.
These data need the FULL Definition 1.3 geometric characterization and proved
existence/uniqueness on the source domain before any choice construction.
This interface is a missing type, not a definition, axiom or assumed package.
The inspected M0CutData instead takes
  (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
and has vertices WholePlaneVertex W and edges WholePlaneEdge W; it cannot
be instantiated at arbitrary A. GeometricSideSubmap is indexed by natural
numbers and supplies no internal open-face carrier. PlanarPathCutData uses
finite bipolar boundary maps and finite paths. Neither supplies this type.

The outstanding comparison must retain all binders
  (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (A : D39DomainRootedMap.{0})
  (I : D39GeomRootedMapIsoV2
    (uibotWholePlaneSourceMap W H
      (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
    (uibotWholePlaneSourceRoot W H
      (WholePlanePastGlueDrawing.glueDrawing W h hpast H)) A.map A.root).
It must identify the image cut with the independently characterized
IntrinsicFutureCut A and transport its actual edge-list paths and distances.
The theorem above PRODUCES I for every A representing the sampled class on
it does not fill the missing arbitrary-A intrinsic cut interface.

Copied anchor SHA256:
014bce5afb490ec66fda743f458e5602624ec7535cfd7b6544fe40498f51a1f2
  DirectedDistances/Paper/Section1/FutureMap.lean
Unedited intro.tex SHA256:
749b5a9ead9f6e02312aad4f9cec7d0ddc59f9b7f33bb9c07f37c807ff9c622f -/

end DirectedDistances.PaperProofs.Section3
end
