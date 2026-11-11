/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation5

/-! Helper toward Proposition 5.16.

This module identifies the selected quotient-edge arc with the transported
whole-plane dart arc. The side and complete drawing-representation fields are
recorded below if the existing side API does not close them. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.KMSW

/-- Helper toward Proposition 5.16. The assembly edge selected by the
representative-adjusted dart equivalence traces the transported whole-plane
dart arc, with reversal exactly when the adjusted Boolean is false. -/
theorem uibhbotD39CanonicalAssembly_arcIdentification
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
    let dartEquiv := iso.toEquiv.symm.trans
      (uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
        D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
        P hp ha F hf hFim hFa)
    (if (dartEquiv d).2 then G.arc (dartEquiv d).1.out
      else (G.arc (dartEquiv d).1.out).reverse) =
        G.arc (iso.toEquiv.symm d) := by
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
  let E := uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P hp ha F hf hFim hFa
  have hbit (e : WholePlaneDart W) :
      (E e).2 = decide ((E e).1.out.2 = e.2) := by
    rcases e with ⟨a, b⟩
    let q : G.GeometricEdge := Quotient.mk G.edgeSetoid (a, b)
    change (uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa (a, b)).2 = decide (q.out.2 = b)
    simp only [uibhbotAssemblyBoundaryDartEquiv3,
      uibhbotAssemblyBoundaryDartAdjust, uibhbotAssemblyBoundaryDartEquiv]
    change (if q.out.2 then !!b else !b) = decide (q.out.2 = b)
    cases q.out.2 <;> cases b <;> rfl
  have hFor (e : WholePlaneDart W) :
      (if (E e).2 then G.arc (E e).1.out
        else (G.arc (E e).1.out).reverse) = G.arc e := by
    let q : G.GeometricEdge := (E e).1
    let b' := (E e).2
    have hq : q = Quotient.mk G.edgeSetoid e := rfl
    have hrep0 := G.geometricEdge_out_mk e
    have hrep : q.out = e ∨ q.out = wholePlaneDartFlip W e := by
      rw [hq]
      exact hrep0
    have hb : b' = decide (q.out.2 = e.2) := hbit e
    change (if b' then G.arc q.out else (G.arc q.out).reverse) = G.arc e
    rcases hrep with hrep | hrep
    · have hb' : b' = true := by rw [hb, hrep]; simp
      rw [hb', hrep]
      simp
    · have hb' : b' = false := by
        rw [hb, hrep]
        rcases e with ⟨a, b⟩
        cases b <;> rfl
      rw [hb', hrep, G.arc_flip e]
      simp
  change (if (E (iso.toEquiv.symm d)).2 then
      G.arc (E (iso.toEquiv.symm d)).1.out
    else (G.arc (E (iso.toEquiv.symm d)).1.out).reverse) =
      G.arc (iso.toEquiv.symm d)
  exact hFor (iso.toEquiv.symm d)






























































end DirectedDistances.PaperProofs.Section5

end
