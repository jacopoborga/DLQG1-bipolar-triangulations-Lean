/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation
public import DirectedDistances.PaperProofs.Section5.UIBHBOTBoundaryPresentationGeometry2

/-! Helper toward Proposition 5.16.

This module derives the global dart-to-geometric-edge identity equivalence
for the canonical UIBHBOT assembly from the representation certificate. It
makes no paper-completion claim. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open MeasureTheory

noncomputable section

/-- Helper toward Proposition 5.16. The representation certificate gives a
bijection from the code-selected map's darts to the canonical assembly's
geometric edge identities together with the assembly's Boolean coordinate.
The quotient edge coordinate retains parallel-edge identity. The separate
endpoint-direction compatibility fields of drawing representation data are
not asserted by this carrier equivalence. -/
theorem uibhbotD39CanonicalAssembly_dartEdgeEquiv
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
    ∃ (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
      (C₀ : UIBHBOTCertifiedRootCapture W 0),
      Nonempty
        (((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.D ≃
          G.GeometricEdge × Bool) := by
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
  obtain ⟨hhit, C₀, hdata, _hdomain⟩ :=
    uibhbotD39CanonicalAssembly_representationCertificate W hW D
  rcases hdata with ⟨hiso, _hrotation, _hmissing, _hforward,
    _hfaceOrbit, _hroot⟩
  refine ⟨hhit, C₀, ?_⟩
  let iso := Classical.choice hiso
  exact ⟨iso.toEquiv.symm.trans
    (uibhbotAssemblyBoundaryDartEquiv W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa)⟩

/-- Helper toward Proposition 5.16. Under the dart-to-edge identity
equivalence, reversing a combinatorial dart preserves its geometric edge
identity and complements the stored traversal bit. -/
theorem uibhbotD39CanonicalAssembly_dartEdgeEquiv_edgeInv
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0)
    (iso : D39RootedMapIso
      ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap)
      ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap))
    (d : ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.D) :
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
    let equiv := iso.toEquiv.symm.trans
      (uibhbotAssemblyBoundaryDartEquiv W D.rotation D.boundary
        D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
        P hp ha F hf hFim hFa)
    equiv (((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.edgeInv d) =
      ((equiv d).1, !(equiv d).2) := by
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
  let dartEquiv := uibhbotAssemblyBoundaryDartEquiv W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P hp ha F hf hFim hFa
  let equiv := iso.toEquiv.symm.trans dartEquiv
  have hflip := uibhbotAssemblyBoundaryDartEquiv_flip W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P hp ha F hf hFim hFa (iso.toEquiv.symm d)
  have hcomm :
      iso.toEquiv.symm
          (((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.edgeInv d) =
        (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap.core.edgeInv
          (iso.toEquiv.symm d) := by
    simpa using (congrArg iso.toEquiv.symm
      (iso.edgeInv_comm (iso.toEquiv.symm d))).symm
  calc
    equiv (((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.edgeInv d) =
        dartEquiv
          ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap.core.edgeInv
            (iso.toEquiv.symm d)) := congrArg dartEquiv hcomm
    _ = ((equiv d).1, !(equiv d).2) := by
      change dartEquiv (wholePlaneDartFlip W (iso.toEquiv.symm d)) = _
      exact hflip

/-- Helper toward Proposition 5.16. The same dart-to-edge equivalence
preserves the missing-edge tag between the code-selected map and the
canonical geometric assembly. -/
theorem uibhbotD39CanonicalAssembly_dartMissing
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0)
    (iso : D39RootedMapIso
      ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap)
      ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap))
    (d : ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.D) :
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
    let N := (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
    let equiv := iso.toEquiv.symm.trans
      (uibhbotAssemblyBoundaryDartEquiv W D.rotation D.boundary
        D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
        P hp ha F hf hFim hFa)
    M.missing (equiv d).1 ↔ N.core.missing d := by
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
  let N := (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
  let dartEquiv := uibhbotAssemblyBoundaryDartEquiv W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P hp ha F hf hFim hFa
  let equiv := iso.toEquiv.symm.trans dartEquiv
  let provider := (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
  have hmissingIso := iso.missing_iff (iso.toEquiv.symm d)
  have hcode : N.core.missing d ↔ ¬ wholePlaneEdgePresent W (iso.toEquiv.symm d).1 := by
    change N.core.missing (iso.toEquiv (iso.toEquiv.symm d)) ↔
      provider.core.missing (iso.toEquiv.symm d) at hmissingIso
    rw [iso.toEquiv.apply_symm_apply] at hmissingIso
    simpa [provider, RootedLocallyFiniteMap.toD39RootedMap,
      uibhbotWholePlaneRootedLocallyFiniteMap] using hmissingIso
  change M.missing (Quotient.mk G.edgeSetoid (iso.toEquiv.symm d)) ↔ N.core.missing d
  rw [uibhbotAssemblyDirectedPlaneMapWithMissing_missing_mk
    W D.rotation D.boundary D.pastLeftUnbounded D.pastRightNonnegative
    D.pastFiniteIncidence P hp ha F hf hFim hFa D.pastRightPositive
    (iso.toEquiv.symm d)]
  exact hcode.symm






























































































end

end DirectedDistances.PaperProofs.Section5

end
