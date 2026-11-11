/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation7

/-! Helper toward Proposition 5.16.

This module exposes the pointwise face-orbit transport needed for the
canonical drawing-representation side field. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.KMSW

/-- Helper toward Proposition 5.16. The code-map face-cycle quotient is
equivalent to the face carrier of its canonical assembly, with its exposed
value determined by the transported whole-plane dart. -/
@[expose] noncomputable def uibhbotD39CanonicalAssembly_faceOrbitEquiv'
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
    change Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e
    exact (iso.symm.faceSameCycle_iff d e).mpr hcycle
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
      A (Quotient.mk _ (E (iso.toEquiv d))) = A (Quotient.mk _ d) :=
        congrArg A hquot
      _ = K := hq
  exact Equiv.ofBijective f ⟨hf_inj, hf_surj⟩

/-- Helper toward Proposition 5.16. The exposed code-map face equivalence
evaluates at a dart class to the assembly face bordered by its transported
whole-plane dart. -/
theorem uibhbotD39CanonicalAssembly_faceOrbitEquiv'_mk
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
    let A := uibhbot_assembly_faceOrbitEquiv W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa D.pastRightPositive
    uibhbotD39CanonicalAssembly_faceOrbitEquiv' W D hhit C₀ iso
      (Quotient.mk _ d) = A (Quotient.mk _ (iso.toEquiv.symm d)) := by
  rfl



theorem uibhbotD39CanonicalAssembly_sideOfDart
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
    let M := (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
    let faceEquiv := uibhbotD39CanonicalAssembly_faceOrbitEquiv' W D hhit C₀ iso
    let faceOfDart (d : M.core.D) := G.toPlaneGraphDrawingFaceEquiv.symm
      (faceEquiv (Quotient.mk _ d))
    let E := uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa
    let dartEquiv := iso.toEquiv.symm.trans E
    if (dartEquiv d).2 then
      G.toPlaneGraphDrawing.SideLeftOf (faceOfDart d) (dartEquiv d).1
    else
      G.toPlaneGraphDrawing.SideRightOf (faceOfDart d) (dartEquiv d).1 := by
  let P := uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let hp := uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let ha := uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let Fdraw := uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary
  let hf := uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary
  let hFim := uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary
  let hFa := uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary
  let G := uibhbotCcw_assemblyDrawing W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P hp ha Fdraw hf hFim hFa
  let M := (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
  let faceEquiv := uibhbotD39CanonicalAssembly_faceOrbitEquiv' W D hhit C₀ iso
  let faceOfDart (d : M.core.D) := G.toPlaneGraphDrawingFaceEquiv.symm
    (faceEquiv (Quotient.mk _ d))
  let Bdry := uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P hp ha Fdraw hf hFim hFa
  let dartEquiv := iso.toEquiv.symm.trans Bdry
  let e : WholePlaneDart W := iso.toEquiv.symm d
  let q := (Bdry e).1
  let A := uibhbot_assembly_faceOrbitEquiv W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P hp ha Fdraw hf hFim hFa D.pastRightPositive
  let face := A (Quotient.mk _ e)
  have hface : G.toPlaneGraphDrawingFaceEquiv (faceOfDart d) = face := by
    dsimp [faceOfDart, faceEquiv, face]
    rw [uibhbotD39CanonicalAssembly_faceOrbitEquiv'_mk]
    exact Equiv.apply_symm_apply _ _
  have hborder : G.dartBorders e face := by
    dsimp [face]
    exact uibhbotD39Assembly_faceOrbitEquiv_dartBorders W D e
  have hvert := uibhbot_faceOrbit_dartVertex_surjective W D.rotation
  have hbit : (Bdry e).2 = decide (q.out.2 = e.2) := by
    rcases e with ⟨a, b⟩
    change (uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha Fdraw hf hFim hFa (a, b)).2 = decide (q.out.2 = b)
    simp only [uibhbotAssemblyBoundaryDartEquiv3,
      uibhbotAssemblyBoundaryDartAdjust, uibhbotAssemblyBoundaryDartEquiv]
    change (if q.out.2 then !!b else !b) = decide (q.out.2 = b)
    cases q.out.2 <;> cases b <;> rfl
  have hrep : q.out = e ∨ q.out = wholePlaneDartFlip W e := by
    have hq : q = Quotient.mk G.edgeSetoid e := rfl
    rw [hq]
    exact G.geometricEdge_out_mk e
  have hselected : (Bdry e).2 = true → q.out = e := by
    intro hb
    rcases hrep with hrep | hrep
    · exact hrep
    · have hb' : (Bdry e).2 = false := by
        rw [hbit, hrep]
        rcases e with ⟨a, b⟩
        cases b <;> rfl
      rw [hb] at hb'
      cases hb'
  have hselectedFlip : (Bdry e).2 = false → q.out = wholePlaneDartFlip W e := by
    intro hb
    rcases hrep with hrep | hrep
    · have hb' : (Bdry e).2 = true := by rw [hbit, hrep]; simp
      rw [hb] at hb'
      cases hb'
    · exact hrep
  have harc := uibhbotD39CanonicalAssembly_arcIdentification W D hhit C₀ iso d
  change (if (Bdry e).2 then G.arc q.out
    else (G.arc q.out).reverse) = G.arc e at harc
  change if (Bdry e).2 then
      G.toPlaneGraphDrawing.SideLeftOf (faceOfDart d) q
    else G.toPlaneGraphDrawing.SideRightOf (faceOfDart d) q
  cases hb : (Bdry e).2
  · have hout := hselectedFlip hb
    have harc' : (G.arc q.out).reverse = G.arc e := by simpa [hb] using harc
    have hreverse := congrArg (fun γ => γ.reverse) harc'
    simp only [Polyline.reverse_reverse] at hreverse
    have hflipArc := G.arc_flip e
    have hselectedArc : G.arc (wholePlaneDartFlip W e) = G.arc q.out := by
      calc
        G.arc (wholePlaneDartFlip W e) = (G.arc e).reverse := hflipArc
        _ = G.arc q.out := hreverse.symm
    have hborderFlip : G.dartBorders
        (wholePlaneDartFlip W (wholePlaneDartFlip W e)) face := by
      rw [wholePlaneDartFlip_involutive W e]
      exact hborder
    intro s
    have hr := G.dartBorders_flip_toPath_rightAtOn hvert
      (wholePlaneDartFlip W e) face hborderFlip s
    have hr' : RightAtOn face.val (G.arc q.out).toPath s := by
      rw [← hselectedArc]
      exact hr
    have hr'' : RightAtOn (G.toPlaneGraphDrawingFaceEquiv
        (faceOfDart d)).val (G.arc q.out).toPath s := by
      exact hface.symm ▸ hr'
    exact (G.toPlaneGraphDrawing_rightAtOn_iff q (faceOfDart d) s).mpr hr''
  · have hout := hselected hb
    have harc' : G.arc q.out = G.arc e := by simpa [hb] using harc
    intro s
    have hl := G.dartBorders_toPath_leftAtOn hvert e face hborder s
    have hl' : LeftAtOn face.val (G.arc q.out).toPath s := by
      rw [← harc'] at hl
      exact hl
    have hl'' : LeftAtOn (G.toPlaneGraphDrawingFaceEquiv
        (faceOfDart d)).val (G.arc q.out).toPath s := by
      exact hface.symm ▸ hl'
    exact (G.toPlaneGraphDrawing_leftAtOn_iff q (faceOfDart d) s).mpr hl''

/-- Helper toward Proposition 5.16. The canonical assembly fields give the
code map a complete drawing-representation record. -/
theorem uibhbotD39CanonicalAssembly_drawingRepresentationData
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
    let B : D39DomainRootedMapV2 :=
      ⟨WholePlaneVertex W, G.GeometricEdge,
        uibhbotD39CanonicalAssemblyMap W D.rotation D.boundary
          D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
          D.pastRightPositive,
        uibhbotD39CanonicalAssemblyRoot W D.rotation D.boundary
          D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence,
        D.domain⟩
    ∃ (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
      (C₀ : UIBHBOTCertifiedRootCapture W 0)
      (iso : D39RootedMapIso
        ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap)
        ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap)),
      Nonempty (D39DrawingRepresentationData
        ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap) B) := by
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
  let B : D39DomainRootedMapV2 :=
    ⟨WholePlaneVertex W, G.GeometricEdge,
      uibhbotD39CanonicalAssemblyMap W D.rotation D.boundary
        D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
        D.pastRightPositive,
      uibhbotD39CanonicalAssemblyRoot W D.rotation D.boundary
        D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence,
      D.domain⟩
  obtain ⟨hhit, C₀, hcert, _hdomain⟩ :=
    uibhbotD39CanonicalAssembly_representationCertificate W hW D
  rcases hcert with ⟨⟨iso⟩, _hrotation, _hmissingCert, hforward,
    _hfaceOrbitCert, _hrootCert⟩
  let M := (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
  let V := uibhbotD39CanonicalAssemblyVertexEquiv W D hhit C₀ iso
  let E := iso.toEquiv.symm.trans
    (uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa)
  let faceEquiv := uibhbotD39CanonicalAssembly_faceOrbitEquiv' W D hhit C₀ iso
  let faceOfDart : M.core.D → B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face :=
    fun d => G.toPlaneGraphDrawingFaceEquiv.symm (faceEquiv (Quotient.mk _ d))
  have hpos : Function.Injective B.map.toPlaneMapWithMissing.pos := by
    change Function.Injective G.pos
    exact G.pos_injective
  have htail : ∀ d,
      V (rootedLocallyFiniteVertexClass M.core.rot d) =
        if (E d).2 then B.map.toPlaneMapWithMissing.src (E d).1
        else B.map.toPlaneMapWithMissing.tgt (E d).1 := by
    intro d
    simpa [E, B] using uibhbotD39CanonicalAssembly_endpoint W D hhit C₀ iso d
  have hflip : ∀ d, E (M.core.edgeInv d) = ((E d).1, !(E d).2) := by
    intro d
    have hcomm : iso.toEquiv.symm (M.core.edgeInv d) =
        (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap.core.edgeInv
          (iso.toEquiv.symm d) := by
      simpa using (congrArg iso.toEquiv.symm
        (iso.edgeInv_comm (iso.toEquiv.symm d))).symm
    change uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa (iso.toEquiv.symm (M.core.edgeInv d)) = _
    rw [hcomm]
    exact uibhbotAssemblyBoundaryDartEquiv3_flip W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa (iso.toEquiv.symm d)
  have hhead : ∀ d,
      V (rootedLocallyFiniteVertexClass M.core.rot (M.core.edgeInv d)) =
        if (E d).2 then B.map.toPlaneMapWithMissing.tgt (E d).1
        else B.map.toPlaneMapWithMissing.src (E d).1 := by
    intro d
    have h := uibhbotD39CanonicalAssembly_endpoint W D hhit C₀ iso (M.core.edgeInv d)
    change V (rootedLocallyFiniteVertexClass M.core.rot (M.core.edgeInv d)) =
      if (E (M.core.edgeInv d)).2 then B.map.toPlaneMapWithMissing.src
        (E (M.core.edgeInv d)).1 else B.map.toPlaneMapWithMissing.tgt
        (E (M.core.edgeInv d)).1 at h
    rw [hflip d] at h
    cases hb : (E d).2 <;> simpa [hb] using h
  have hmissing : ∀ d,
      B.map.toPlaneMapWithMissing.missing (E d).1 ↔ M.core.missing d := by
    intro d
    let Eold := iso.toEquiv.symm.trans
      (uibhbotAssemblyBoundaryDartEquiv W D.rotation D.boundary
        D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
        P hp ha F hf hFim hFa)
    have hfirst : (E d).1 = (Eold d).1 := rfl
    change (uibhbotAssemblyDirectedPlaneMapWithMissing W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa D.pastRightPositive).missing (E d).1 ↔ M.core.missing d
    rw [hfirst]
    exact uibhbotD39CanonicalAssembly_dartMissing W D hhit C₀ iso d
  have horientation : ∀ d (hd : ¬ M.core.missing d),
      M.core.tail d ↔
        B.map.forward ⟨(E d).1, (hmissing d).not.mpr hd⟩ = (E d).2 := by
    intro d hd
    let e : WholePlaneDart W := iso.toEquiv.symm d
    have hpresent : ¬ (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap.core.missing e := by
      intro hm
      have hmcode : M.core.missing d := by
        simpa [M, e] using (iso.missing_iff e).mpr hm
      exact hd hmcode
    have htailIso : M.core.tail d ↔ wholePlaneDartTail W e := by
      have ht := iso.tail_iff e hpresent
      change M.core.tail (iso.toEquiv e) ↔ wholePlaneDartTail W e at ht
      simpa [e] using ht
    have hpresentEdge : wholePlaneEdgePresent W e.1 := by
      change ¬¬ wholePlaneEdgePresent W e.1 at hpresent
      exact Classical.not_not.mp hpresent
    have hdir := uibhbotD39CanonicalAssembly_wholePlaneOrientation
      W D hforward e hpresentEdge
    have hdir' : wholePlaneDartTail W e ↔
        B.map.forward ⟨(E d).1, (hmissing d).not.mpr hd⟩ = (E d).2 := by
      convert hdir using 1 <;> rfl
    exact htailIso.trans hdir'
  have hroot : E M.rootMark.dart = B.root := by
    simpa [E, B] using uibhbotD39CanonicalAssembly_rootMark W D hhit C₀ iso
  have hfaceOrbit : ∀ d e : M.core.D,
      faceOfDart d = faceOfDart e ↔
        Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e := by
    intro d e
    constructor
    · intro h
      have h' : faceEquiv (Quotient.mk _ d) = faceEquiv (Quotient.mk _ e) := by
        have := congrArg G.toPlaneGraphDrawingFaceEquiv h
        simpa [faceOfDart] using this
      exact Quotient.exact (faceEquiv.injective h')
    · intro h
      have hq : Quotient.mk
          (Equiv.Perm.SameCycle.setoid (M.core.rot.symm * M.core.edgeInv)) d =
          Quotient.mk _ e := Quotient.sound h
      exact congrArg (fun q => G.toPlaneGraphDrawingFaceEquiv.symm (faceEquiv q)) hq
  have hfaceSurj : Function.Surjective faceOfDart := by
    intro F0
    obtain ⟨q, hq⟩ := faceEquiv.surjective (G.toPlaneGraphDrawingFaceEquiv F0)
    revert hq
    refine Quotient.inductionOn q ?_
    intro d hq
    refine ⟨d, ?_⟩
    have hq' := congrArg G.toPlaneGraphDrawingFaceEquiv.symm hq
    change G.toPlaneGraphDrawingFaceEquiv.symm
      (faceEquiv (Quotient.mk _ d)) = F0
    exact hq'
  refine ⟨hhit, C₀, iso, ⟨d39DrawingRepresentationData_of_fields
    V hpos E htail hhead hflip hmissing horientation hroot faceOfDart
    hfaceOrbit hfaceSurj ?_⟩⟩
  intro d
  exact uibhbotD39CanonicalAssembly_sideOfDart W D hhit C₀ iso d

end DirectedDistances.PaperProofs.Section5

end
