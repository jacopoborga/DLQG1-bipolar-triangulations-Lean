/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Carriers1
public import DirectedDistances.PaperProofs.Section1.FutureMapFaces














public section
namespace DirectedDistances.PlanarMap

open MeasureTheory DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section1

universe uV uE uUL uUR uLR uLL

/-- Helper toward Definition 3.2: the complete M_{0,infinity} obligation
in the faithful run-zero edge/vertex coordinates established below. The
probability-one quantifier is outside the full presentation package. -/
@[expose] def M0CutBoundEdges32Source : Prop :=
  ∀ᵐ W ∂RandomWalk.wholePlaneIIDCodeMeasure,
    OneSidedKMSWBoundEdges32At (shiftedStream W 0)




@[expose] def ExtendedBoundEdges32Source : Prop :=
  UIQBOTBoundEdges32Source ∧ UIBHBOTBoundEdges32Source ∧
  KMSWStageBoundEdges32Source ∧ BoundaryChanneledBoundEdges32Source ∧
  OneSidedKMSWBoundEdges32Source ∧ BiInfiniteKMSWBoundEdges32Source ∧
  M0CutBoundEdges32Source



theorem not_extendedBoundEdges32Source_carriers2 : ¬ ExtendedBoundEdges32Source := by
  intro h
  exact not_oneSidedKMSWBoundEdges32Source_carriers1 h.2.2.2.2.1

/-- Helper toward Definition 3.2: the boundaryless case cannot be represented
by an empty supplied presentation together with a face of an incident PL
drawing. This exposes a second limitation of the current package; it does
not assert that a boundaryless source map has an external face. -/
theorem no_sourceClauses_with_empty_presentation_carriers2
    {V : Type uV} {E : Type uE} (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M))
    (hincident : Function.Surjective (boundaryDartInitial M))
    (d₀ : E × Bool) (U : G.Face) (S : E × Bool → E × Bool)
    (hempty : IsEmpty (InfiniteBoundaryDartIndex B.presentation)) :
    ¬ BoundEdges32SourceClauses M B G U S := by
  intro h
  obtain ⟨d, hd⟩ := G.face_has_bordering_dart hincident d₀ U
  have hcoverage := (bound_edges_provider_of_isBoundEdges32 M B G U S h.1).1
  obtain ⟨i, _⟩ := (hcoverage d).mp hd
  exact hempty.false i





theorem ae_m0Cut_boundary_carrier_data_carriers2 :
    ∀ᵐ W ∂RandomWalk.wholePlaneIIDCodeMeasure,
      ∃ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1))))),
      let D := m0CutData W H h hLL
      let w := shiftedStream W 0
      let P := monotoneFamilyDrawing w (H.1 0) (monotone_family_all w)
      D.edges = Set.range (wholePlaneEdgeι W 0) ∧
      D.darts = Set.range (wholePlaneDartι W 0) ∧
      Function.Injective (wholePlaneEdgeι W 0) ∧
      Function.Injective (wholePlaneVertexι W 0) ∧
      (∀ e, D.missing (wholePlaneEdgeι W 0 e) ↔ ¬ EdgePresent w e) ∧
      (∀ k, D.x k = wholePlaneVertexι W 0 (boundaryVertex w h k)) ∧
      (∀ (rot : Equiv.Perm (ℕ × Bool))
        (G : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2)) rot
          (kmswLimitDartVertex w)), LocallyFiniteVertexImage G) ∧
      ∃ U : P.Face,
        P.IsUnbounded U ∧
        (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
        (∀ d, P.dartBorders d U ↔ ∃ k : ℤ, d = futureMapBoundaryDart w h k) ∧
        (∀ k : ℤ, kmswInfFaceSucc w (H.1 0) (futureMapBoundaryDart w h k) =
          futureMapBoundaryDart w h (k - 1)) ∧
        (∀ k : ℤ,
          edgeWest w (boundaryOuterEdge w h k) = boundaryVertex w h k ∧
          edgeEast w (boundaryOuterEdge w h k) = boundaryVertex w h (k + 1) ∧
          (EdgePresent w (boundaryOuterEdge w h k) ↔ 0 ≤ k)) := by
  filter_upwards [futureMap_combinatorial_characterization_ae] with W hW
  obtain ⟨H, h, hLL, _⟩ := hW
  let D := m0CutData W H h hLL
  let w := shiftedStream W 0
  refine ⟨H, h, hLL, D.edges_eq h hLL, D.darts_eq h hLL,
    wholePlaneEdgeι_injective W 0, wholePlaneVertexι_injective W 0,
    D.missing_eq h hLL, D.x_eq h hLL, ?_, ?_⟩
  · intro rot G
    exact kmsw_raw_locallyFiniteVertexImage_carriers1 w (H.1 0) G
  · obtain ⟨U, hU, huniq, _, hborder, _, hsucc⟩ :=
      monotoneFamilyDrawing_realized_boundary_twoSided w (H.1 0) h
    refine ⟨U, hU, huniq, hborder, hsucc, ?_⟩
    intro k
    have hk := boundaryOuterEdge_endpoints w h k
    refine ⟨hk.1, hk.2.1, ?_, hk.2.2.1⟩
    intro hp
    by_contra hn
    exact hk.2.2.2 (by omega) hp





















end DirectedDistances.PlanarMap

