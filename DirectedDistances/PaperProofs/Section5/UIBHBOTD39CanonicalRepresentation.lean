/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516Def58LawIdentification
public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalClass12
public import DirectedDistances.PaperProofs.Section5.Prop59ProviderRootedMapIso













































public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open MeasureTheory

noncomputable section

/-- Helper toward Proposition 5.16. For a code in the source conull event and
a canonical geometric-domain witness, the fixed canonical past/future
assembly has the provider's whole-plane combinatorial identification, its
counterclockwise rotation agreement, its face-orbit/bordering correspondence,
and its present-edge orientation and missing-edge side conditions. The
geometric domain is retained as part of the certificate. -/
theorem uibhbotD39CanonicalAssembly_representationCertificate
    (W : ℤ → Fin 3) (hW : W ∈ uibhbotRootedPlanarMapConullEvent)
    (D : UIBHBOTD39CanonicalDomainWitness W) :
    let P := uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence
    let hp := uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence
    let ha := uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence
    let F := uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary
    let hf := uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary
    let hFim := uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary
    let hFa := uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary
    let G := uibhbotCcw_assemblyDrawing W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa
    let M := uibhbotAssemblyDirectedPlaneMapWithMissing W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa D.pastRightPositive
    ∃ (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
      (C₀ : UIBHBOTCertifiedRootCapture W 0),
      (Nonempty (D39RootedMapIso
        ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap)
        ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap)) ∧
      (∀ d : WholePlaneDart W,
        CcwSuccessor
          {E | wholePlaneDartVertex W E = wholePlaneDartVertex W d}
          (fun E => (G.arc E).initialDirection) d (wholePlaneRotation W D.rotation d)) ∧
      (∀ d : WholePlaneDart W,
        M.missing (Quotient.mk G.edgeSetoid d) ↔
          ¬ wholePlaneEdgePresent W d.1) ∧
      (∀ a : {a : G.GeometricEdge // ¬ M.missing a},
        M.forward a = !a.val.out.2) ∧
      (∀ d : WholePlaneDart W, ∀ K : G.Face,
        uibhbot_assembly_faceOrbitEquiv W D.rotation D.boundary
          D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
          P hp ha F hf hFim hFa D.pastRightPositive (Quotient.mk _ d) = K ↔
            G.dartBorders d K) ∧
      uibhbotWholePlaneFrameEdgeDart W = (uibhbotRootEdge W, false)) ∧
      D39GeomDomain
        (uibhbotD39CanonicalAssemblyMap W D.rotation D.boundary
          D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
          D.pastRightPositive)
        (uibhbotD39CanonicalAssemblyRoot W D.rotation D.boundary
          D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence) := by
  let P := uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let hp := uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let ha := uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let F := uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary
  let hf := uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary
  let hFim := uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary
  let hFa := uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary
  obtain ⟨hhit, C₀, hidentification⟩ :=
    uibhbotProviderAssemblyD39_identification W hW D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa D.pastRightPositive
      (fun _ => uibhbotRootEdge W) rfl
  exact ⟨hhit, C₀, hidentification, D.domain⟩

/-- Helper toward Proposition 5.16. Almost surely, the source conull event and
the canonical assembly-domain event hold together, so the explicit
rotation/face/side certificate above is available with its full binders. -/
theorem uibhbotCodeLawRel_ae_uibhbotD39CanonicalAssembly_representationCertificate :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ D : UIBHBOTD39CanonicalDomainWitness W,
          let P := uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
            D.pastRightNonnegative D.pastFiniteIncidence
          let hp := uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
            D.pastRightNonnegative D.pastFiniteIncidence
          let ha := uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
            D.pastRightNonnegative D.pastFiniteIncidence
          let F := uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary
          let hf := uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary
          let hFim := uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary
          let hFa := uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary
          let G := uibhbotCcw_assemblyDrawing W D.rotation D.boundary
            D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
            P hp ha F hf hFim hFa
          let M := uibhbotAssemblyDirectedPlaneMapWithMissing W D.rotation D.boundary
            D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
            P hp ha F hf hFim hFa D.pastRightPositive
          ∃ (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
            (C₀ : UIBHBOTCertifiedRootCapture W 0),
            (Nonempty (D39RootedMapIso
              ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap)
              ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap)) ∧
            (∀ d : WholePlaneDart W,
              CcwSuccessor
                {E | wholePlaneDartVertex W E = wholePlaneDartVertex W d}
                (fun E => (G.arc E).initialDirection) d
                (wholePlaneRotation W D.rotation d)) ∧
            (∀ d : WholePlaneDart W,
              M.missing (Quotient.mk G.edgeSetoid d) ↔
                ¬ wholePlaneEdgePresent W d.1) ∧
            (∀ a : {a : G.GeometricEdge // ¬ M.missing a},
              M.forward a = !a.val.out.2) ∧
            (∀ d : WholePlaneDart W, ∀ K : G.Face,
              uibhbot_assembly_faceOrbitEquiv W D.rotation D.boundary
                D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
                P hp ha F hf hFim hFa D.pastRightPositive (Quotient.mk _ d) = K ↔
                  G.dartBorders d K) ∧
            uibhbotWholePlaneFrameEdgeDart W = (uibhbotRootEdge W, false)) ∧
            D39GeomDomain
              (uibhbotD39CanonicalAssemblyMap W D.rotation D.boundary
                D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
                D.pastRightPositive)
              (uibhbotD39CanonicalAssemblyRoot W D.rotation D.boundary
                D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence) := by
  filter_upwards [uibhbotRootedPlanarMapConullEvent_spec.2.1,
    uibhbotCodeLawRel_ae_d39CanonicalGeomDomain] with W hW hD
  rcases hD with ⟨H, h0, hL, hR, hfin, hRpos, e, he, hdomain⟩
  let D : UIBHBOTD39CanonicalDomainWitness W :=
    ⟨H, h0, hL, hR, hfin, hRpos, hdomain⟩
  exact ⟨D, uibhbotD39CanonicalAssembly_representationCertificate W hW D⟩

end

end DirectedDistances.PaperProofs.Section5

end
