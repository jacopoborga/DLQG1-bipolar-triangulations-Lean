/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTDefinition32Presentation8
public import DirectedDistances.PlanarMap.ExternalFaceIntervalOrder7

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults

noncomputable section

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
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

local notation "G" => uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
local notation "M" => uibhbotAssemblyDirectedPlaneMapWithMissing
  W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos

include hRpos in
/-- Helper toward Definition 3.2: on the canonical whole-plane assembly
darts, the unique unbounded face is bordered exactly by east darts of missing
edges, and whole-plane face succession stays on that face. -/
theorem uibhbotAssembly_wholePlaneExternalFaceGeometry :
    ∃ U : (G).Face, (G).IsUnbounded U ∧
      (∀ d : WholePlaneDart W,
        (G).dartBorders d U ↔ d.2 = true ∧ ¬ wholePlaneEdgePresent W d.1) ∧
      IsGeometricExternalFaceSucc (G) U (wholePlaneFaceSucc W H) := by
  obtain ⟨U, hU, _⟩ := uibhbot_assembly_unbounded_face_existsUnique
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  refine ⟨U, hU, ?_, ?_⟩
  · intro d
    exact uibhbot_assembly_unbounded_dartBorders_iff
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos U hU d
  · refine ⟨hU, ?_⟩
    intro d hd
    constructor
    · change (wholePlaneRotation W H).symm (wholePlaneDartFlip W d) = _
      rfl
    · exact uibhbot_assembly_faceSucc_dartBorders
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos d U hd

/-- Helper toward Definition 3.2: the UIBHBOT presentation's endpoint-label
clauses are vacuous because its four optional endpoint fields are absent. -/
theorem uibhbotDefinition32Presentation_endpointLabels
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e) :
    BoundarySideEndpointLabels M
      (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa
        hRpos e hinj).upperLeft ∧
    BoundarySideEndpointLabels M
      (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa
        hRpos e hinj).upperRight ∧
    BoundarySideEndpointLabels M
      (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa
        hRpos e hinj).lowerRight ∧
    BoundarySideEndpointLabels M
      (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa
        hRpos e hinj).lowerLeft := by
  rw [uibhbotDefinition32Presentation_eq W H h0 hL hR hfin P hp ha F hf hFim hFa
    hRpos e hinj]
  simp [BoundarySideEndpointLabels]

/-- Helper toward Definition 3.2: the same presentation has no side-change
join to label, since its only nonempty side is bi-infinite. -/
theorem uibhbotDefinition32Presentation_joinEndpointLabels
    (e : ℤ → WholePlaneEdge W) (hinj : Function.Injective e)
    (S : ((G).GeometricEdge × Bool) → ((G).GeometricEdge × Bool)) :
    BoundaryJoinEndpointLabels
      (uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf hFim hFa
        hRpos e hinj) S := by
  rw [uibhbotDefinition32Presentation_eq W H h0 hL hR hfin P hp ha F hf hFim hFa
    hRpos e hinj]
  intro i j _ hnext
  cases i with
  | upperLeft i => cases i
  | upperRight i => cases i
  | lowerRight i => cases i
  | lowerLeft i => simp [sideNext] at hnext

/-- Helper toward Definition 3.2: almost surely, the presentation already
has its source-certified external-frontier and multiplicity clauses, and all
four v7 endpoint-label clauses. This does not yet identify the PL-drawing
dart carrier's external face with the presentation darts. -/
theorem ae_uibhbotDefinition32Presentation_boundaryAndEndpointClauses :
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
        let P' := uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf
          hFim hFa hRpos e hinj
        let M' := uibhbotAssemblyDirectedPlaneMapWithMissing
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
        IsBoundaryOrderOfInf M' P' ∧
        ULOkInf P' ∧ UROkInf P' ∧ LROkInf P' ∧ LLOkInf P' ∧
        BoundarySideEndpointLabels M' P'.upperLeft ∧
        BoundarySideEndpointLabels M' P'.upperRight ∧
        BoundarySideEndpointLabels M' P'.lowerRight ∧
        BoundarySideEndpointLabels M' P'.lowerLeft := by
  filter_upwards [ae_uibhbotDefinition32Presentation_isBoundaryOrderOfInf] with W hW
  obtain ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos,
    e, hinj, hwest_east_missing, hboundary⟩ := hW
  let P' := uibhbotDefinition32Presentation W H h0 hL hR hfin P hp ha F hf
    hFim hFa hRpos e hinj
  let M' := uibhbotAssemblyDirectedPlaneMapWithMissing
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  have hsource (k : ℤ) :
      wholePlaneEdgeWest W (e k) = (uibhbotBusemannSource k W).id ∧
      wholePlaneEdgeEast W (e k) = (uibhbotBusemannSource (k + 1) W).id ∧
      ¬ wholePlaneEdgePresent W (e k) := hwest_east_missing k
  have hempty := uibhbotDefinition32Presentation_emptySides
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj
  have hll := uibhbotDefinition32Presentation_lowerLeft_ok
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj
    (fun k => (hsource k).1) (fun k => (hsource k).2.1)
    (fun k => (hsource k).2.2)
  have hend := uibhbotDefinition32Presentation_endpointLabels
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e hinj
  exact ⟨H, h0, hL, hR, hfin, P, hp, ha, F, hf, hFim, hFa, hRpos, e, hinj,
    hboundary, hempty.1, hempty.2.1, hempty.2.2, hll,
    hend.1, hend.2.1, hend.2.2.1, hend.2.2.2⟩















































/- The remaining obstruction is the presentation-carrier PLDrawing transport and
the resulting exact equation `G'.dartBorders d U ↔ ∃ i,
InfiniteBoundaryDartIndex.dart P' i = d`. The already proved assembly
classification is on `WholePlaneDart W`; the selected lower-left darts use
the complement of the quotient representative bit, while the assembly's
unbounded-face characterization is stated for darts with bit `true`. A direct
reuse of `PLDrawing.toPlaneGraphDrawing` only gives a `PlaneGraphDrawing`,
while the UIQBOT `plDrawing_transport` pattern requires a checked dart
equivalence with the correct boundary-vertex, reversal, rotation, and
external-dart equations. No such equation is asserted here. -/

end
end DirectedDistances.PaperProofs.Section5

end
