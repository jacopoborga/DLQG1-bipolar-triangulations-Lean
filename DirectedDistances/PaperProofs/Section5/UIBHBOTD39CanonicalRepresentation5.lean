/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation4
public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalDirection

/-! Helper toward Proposition 5.16.

This module transports the assembly face-cycle representation to the code map. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.KMSW

/-- Helper toward Proposition 5.16. The code map's face-cycle quotient is
bijective with the face carrier of its canonical assembly, by transporting
cycles along the rooted-map isomorphism and then using the assembly's proved
face-orbit equivalence. -/
noncomputable def uibhbotD39CanonicalAssembly_faceOrbitEquiv
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0)
    (iso : D39RootedMapIso
      ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap)
      ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap)) :
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
    let M := (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
    Quotient (Equiv.Perm.SameCycle.setoid (M.core.rot.symm * M.core.edgeInv)) ≃
      G.Face := by
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
  let M := (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
  let N := (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
  let E := iso.toEquiv.symm
  let A := uibhbot_assembly_faceOrbitEquiv W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P hp ha F hf hFim hFa D.pastRightPositive
  let f : Quotient (Equiv.Perm.SameCycle.setoid (M.core.rot.symm * M.core.edgeInv)) →
      G.Face :=
    Quotient.lift (fun d => A (Quotient.mk _ (E d))) (by
      intro d e h
      change Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e at h
      have hcode : Equiv.Perm.SameCycle
          (((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.rot.symm *
            ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.edgeInv)
          (iso.toEquiv (E d)) (iso.toEquiv (E e)) := by
        simpa [M, E] using h
      have hcycle : (wholePlaneFaceSucc W D.rotation).SameCycle (E d) (E e) := by
        have hcompat := (iso.faceSameCycle_iff (E d) (E e)).mpr hcode
        change (wholePlaneFaceSucc W D.rotation).SameCycle (E d) (E e) at hcompat
        exact hcompat
      exact congrArg A (Quotient.sound hcycle))
  have hf_inj : Function.Injective f := by
    intro q r h
    revert h
    refine Quotient.inductionOn₂ q r ?_
    intro d e h
    apply Quotient.sound
    have hA : A (Quotient.mk _ (E d)) = A (Quotient.mk _ (E e)) := h
    have hq : Quotient.mk
        (Equiv.Perm.SameCycle.setoid (wholePlaneFaceSucc W D.rotation)) (E d) =
        Quotient.mk
          (Equiv.Perm.SameCycle.setoid (wholePlaneFaceSucc W D.rotation)) (E e) :=
      A.injective hA
    have hcycle : (wholePlaneFaceSucc W D.rotation).SameCycle (E d) (E e) :=
      Quotient.exact hq
    have hprovider : (wholePlaneFaceSucc W D.rotation).SameCycle (E d) (E e) := hcycle
    change Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e
    exact (iso.symm.faceSameCycle_iff d e).mpr hprovider
  have hf_surj : Function.Surjective f := by
    intro K
    obtain ⟨q, hq⟩ := A.surjective K
    revert hq
    refine Quotient.inductionOn q ?_
    intro d hq
    refine ⟨Quotient.mk _ (iso.toEquiv d), ?_⟩
    change A (Quotient.mk _ (E (iso.toEquiv d))) = K
    have hcomp : E (iso.toEquiv d) = d := by
      change iso.toEquiv.symm (iso.toEquiv d) = d
      exact Equiv.symm_apply_apply _ _
    have hquot : Quotient.mk
        (Equiv.Perm.SameCycle.setoid (wholePlaneFaceSucc W D.rotation))
        (E (iso.toEquiv d)) = Quotient.mk _ d := by
      exact congrArg (Quotient.mk _) hcomp
    calc
      A (Quotient.mk _ (E (iso.toEquiv d))) = A (Quotient.mk _ d) := by
        exact congrArg A hquot
      _ = K := hq
  exact Equiv.ofBijective f ⟨hf_inj, hf_surj⟩




end DirectedDistances.PaperProofs.Section5

end

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.KMSW

/-- Helper toward Proposition 5.16. Every face of the canonical assembly is
in the image of the code-map dart face assignment induced by the cycle equivalence. -/
theorem uibhbotD39CanonicalAssembly_faceSurjective
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0)
    (iso : D39RootedMapIso
      ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap)
      ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap)) :
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
    let M := (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
    let faceEquiv : Quotient
        (Equiv.Perm.SameCycle.setoid (M.core.rot.symm * M.core.edgeInv)) ≃ G.Face :=
      uibhbotD39CanonicalAssembly_faceOrbitEquiv W D hhit C₀ iso
    let faceOfDart : M.core.D → G.toPlaneGraphDrawing.Face :=
      fun d => G.toPlaneGraphDrawingFaceEquiv.symm (faceEquiv (Quotient.mk _ d))
    Function.Surjective faceOfDart := by
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
  let M := (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
  let faceEquiv : Quotient
      (Equiv.Perm.SameCycle.setoid (M.core.rot.symm * M.core.edgeInv)) ≃ G.Face :=
    uibhbotD39CanonicalAssembly_faceOrbitEquiv W D hhit C₀ iso
  let faceOfDart : M.core.D → G.toPlaneGraphDrawing.Face :=
    fun d => G.toPlaneGraphDrawingFaceEquiv.symm (faceEquiv (Quotient.mk _ d))
  change ∀ K : G.toPlaneGraphDrawing.Face, ∃ d : M.core.D, faceOfDart d = K
  intro K
  obtain ⟨q, hq⟩ := faceEquiv.surjective (G.toPlaneGraphDrawingFaceEquiv K)
  revert hq
  refine Quotient.inductionOn q ?_
  intro d hq
  refine ⟨d, ?_⟩
  have hq' := congrArg G.toPlaneGraphDrawingFaceEquiv.symm hq
  simpa [faceOfDart] using hq'

end DirectedDistances.PaperProofs.Section5

end



















































