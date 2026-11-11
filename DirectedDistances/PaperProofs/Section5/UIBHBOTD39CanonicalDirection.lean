/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation3
public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation4

/-! Helper toward Proposition 5.16.

This module removes the standalone present-edge orientation premise from the
canonical assembly direction lemma by obtaining that clause from the assembly
representation certificate. The existing root-mark correspondence in
Representation3 has no dependency on the orientation premise. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open MeasureTheory

noncomputable section

/-- Helper toward Proposition 5.16. The certificate's present-edge
orientation clause implies that the representative-adjusted Boolean coordinate
records the whole-plane dart's tail condition, without a separate orientation
premise. -/
theorem uibhbotD39CanonicalAssembly_wholePlaneOrientation_ofCertificate
    (W : ℤ → Fin 3) (hW : W ∈ uibhbotRootedPlanarMapConullEvent)
    (D : UIBHBOTD39CanonicalDomainWitness W)
    (e : WholePlaneDart W) (he : wholePlaneEdgePresent W e.1) :
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
    let A := uibhbotD39CanonicalAssemblyMap W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      D.pastRightPositive
    let E := uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa
    let a : {a : G.GeometricEdge // ¬ A.missing a} :=
      ⟨(E e).1, by
        have hmiss := uibhbotAssemblyDirectedPlaneMapWithMissing_missing_mk
          W D.rotation D.boundary D.pastLeftUnbounded D.pastRightNonnegative
          D.pastFiniteIncidence P hp ha F hf hFim hFa D.pastRightPositive e
        have hq : (E e).1 = Quotient.mk G.edgeSetoid e := rfl
        change A.missing (Quotient.mk G.edgeSetoid e) ↔ _ at hmiss
        rw [hq, hmiss]
        simpa using he⟩
    wholePlaneDartTail W e ↔ A.forward a = (E e).2 := by
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
  let A := uibhbotD39CanonicalAssemblyMap W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    D.pastRightPositive
  let E := uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P hp ha F hf hFim hFa
  obtain ⟨_hhit, _C₀, hcertificate, _hdomain⟩ :=
    uibhbotD39CanonicalAssembly_representationCertificate W hW D
  rcases hcertificate with
    ⟨_hiso, _hrotation, _hmissing, hforward, _hfaceOrbit, _hroot⟩
  let a : {a : G.GeometricEdge // ¬ A.missing a} :=
    ⟨(E e).1, by
      have hmiss := uibhbotAssemblyDirectedPlaneMapWithMissing_missing_mk
        W D.rotation D.boundary D.pastLeftUnbounded D.pastRightNonnegative
        D.pastFiniteIncidence P hp ha F hf hFim hFa D.pastRightPositive e
      have hq : (E e).1 = Quotient.mk G.edgeSetoid e := rfl
      change A.missing (Quotient.mk G.edgeSetoid e) ↔ _ at hmiss
      rw [hq, hmiss]
      simpa using he⟩
  have hdir := hforward a
  change A.forward a = !a.val.out.2 at hdir
  rcases e with ⟨edge, b⟩
  let q : G.GeometricEdge := Quotient.mk G.edgeSetoid (edge, b)
  have hq : a.val = q := rfl
  have hbit : (E (edge, b)).2 = decide (q.out.2 = b) := by
    change (uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa (edge, b)).2 = decide (q.out.2 = b)
    simp only [uibhbotAssemblyBoundaryDartEquiv3,
      uibhbotAssemblyBoundaryDartAdjust, uibhbotAssemblyBoundaryDartEquiv]
    change (if q.out.2 then !!b else !b) = decide (q.out.2 = b)
    cases hqo : q.out.2 <;> cases b <;> simp
  change wholePlaneDartTail W (edge, b) ↔
    A.forward a = (E (edge, b)).2
  rw [hdir, hq]
  rw [hbit]
  cases hqo : q.out.2 <;> cases b <;>
    simp [wholePlaneDartTail, he]

end

end DirectedDistances.PaperProofs.Section5

end
