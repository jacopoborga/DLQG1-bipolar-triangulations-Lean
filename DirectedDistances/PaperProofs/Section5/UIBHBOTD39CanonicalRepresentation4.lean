/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation3
public import DirectedDistances.PlanarMap.D39DrawingRepresentation
public import DirectedDistances.PaperProofs.SourceResults.D39GeometricSourceProviderV2

/-! Helper toward Proposition 5.16.

This module isolates assembly of the base drawing-representation structure
from its face assignment, orbit, coverage, and side obligations. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.KMSW

/-- Helper toward Proposition 5.16. Assemble `D39DrawingRepresentationData`
from its named vertex, dart, orientation, root, and face fields. The final
four arguments are exactly the face obligations left after the non-face
representation fields have been supplied. -/
def d39DrawingRepresentationData_of_fields
    {M : D39RootedMap} {B : DirectedDistances.PaperProofs.SourceResults.D39DomainRootedMapV2}
    (vertexEquiv : RootedLocallyFiniteVertex M.core.D M.core.rot ≃ B.V)
    (positions_injective : Function.Injective B.map.toPlaneMapWithMissing.pos)
    (dartEquiv : M.core.D ≃ B.E × Bool)
    (dart_tail_vertex : ∀ d,
      vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot d) =
        if (dartEquiv d).2 then B.map.toPlaneMapWithMissing.src (dartEquiv d).1
        else B.map.toPlaneMapWithMissing.tgt (dartEquiv d).1)
    (dart_head_vertex : ∀ d,
      vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot (M.core.edgeInv d)) =
        if (dartEquiv d).2 then B.map.toPlaneMapWithMissing.tgt (dartEquiv d).1
        else B.map.toPlaneMapWithMissing.src (dartEquiv d).1)
    (dart_edgeInv : ∀ d,
      dartEquiv (M.core.edgeInv d) = ((dartEquiv d).1, !(dartEquiv d).2))
    (dart_missing : ∀ d,
      B.map.toPlaneMapWithMissing.missing (dartEquiv d).1 ↔ M.core.missing d)
    (dart_orientation : ∀ d (hd : ¬ M.core.missing d),
      M.core.tail d ↔
        B.map.forward ⟨(dartEquiv d).1, (dart_missing d).not.mpr hd⟩ =
          (dartEquiv d).2)
    (root_mark : dartEquiv M.rootMark.dart = B.root)
    (faceOfDart : M.core.D → B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
    (faceOrbit_iff : ∀ d e,
      faceOfDart d = faceOfDart e ↔
        Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e)
    (face_surjective : Function.Surjective faceOfDart)
    (face_left_of_dart : ∀ d,
      if (dartEquiv d).2 then
        B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf
          (faceOfDart d) (dartEquiv d).1
      else
        B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf
          (faceOfDart d) (dartEquiv d).1) :
    D39DrawingRepresentationData M B := by
  exact
    { vertexEquiv := vertexEquiv
      positions_injective := positions_injective
      dartEquiv := dartEquiv
      dart_tail_vertex := dart_tail_vertex
      dart_head_vertex := dart_head_vertex
      dart_edgeInv := dart_edgeInv
      dart_missing := dart_missing
      dart_orientation := dart_orientation
      root_mark := root_mark
      faceOfDart := faceOfDart
      faceOrbit_iff := faceOrbit_iff
      face_surjective := face_surjective
      face_left_of_dart := face_left_of_dart }

 
/- - Helper toward Proposition 5.16. The code map's face-cycle quotient is
equivalent to the face carrier of its canonical assembly: first transport
cycles along the rooted-map isomorphism, then use the assembly's proved
face-orbit equivalence. 
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
        simpa [E, wholePlaneFaceSucc, RootedLocallyFiniteMap.toD39RootedMap,
          uibhbotWholePlaneRootedLocallyFiniteMap] using hcompat
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
    have hprovider : Equiv.Perm.SameCycle (N.core.rot.symm * N.core.edgeInv) (E d) (E e) := by
      simpa [RootedLocallyFiniteMap.toD39RootedMap,
        uibhbotWholePlaneRootedLocallyFiniteMap, wholePlaneFaceSucc] using hcycle
    have hcompat := (iso.faceSameCycle_iff (E d) (E e)).mp hprovider
    simpa [M, E] using hcompat
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
  exact Equiv.ofBijective f ⟨hf_inj, hf_surj⟩ -/































































































end DirectedDistances.PaperProofs.Section5

end
