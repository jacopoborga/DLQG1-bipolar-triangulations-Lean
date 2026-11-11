/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation13
public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation11
public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation12
public import DirectedDistances.PlanarMap.D39DrawingRepresentation3

/-! Helper toward Proposition 5.16.

This module strengthens the constructed canonical representation with its
explicit assembly-face identification, then uses that identification to
transfer the locally finite frontier/incidence theorem. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap DirectedDistances.KMSW
open DirectedDistances.PaperProofs.SourceResults
open unitInterval

/-- Helper toward Proposition 5.16. The explicitly constructed canonical
representation retains its assembly face assignment as well as the prescribed
dart equivalence and topological rotation field. -/
theorem uibhbotD39CanonicalAssembly_rotation_topological_successor_with_face
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
      ∃ base : D39DrawingRepresentationData
        ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap) B,
        base.dartEquiv = iso.toEquiv.symm.trans
          (uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
            D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
            P hp ha F hf hFim hFa) ∧
        (∀ d,
          (base.faceOfDart d).val =
            (G.toPlaneGraphDrawingFaceEquiv.symm
              ((uibhbotD39CanonicalAssembly_faceOrbitEquiv' W D hhit C₀ iso)
                (Quotient.mk _ d))).val) ∧
        ∀ d, D39TopologicalCcwSuccessor
          {e | rootedLocallyFiniteVertexClass
              ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.rot e =
            rootedLocallyFiniteVertexClass
              ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.rot d}
          (d39DrawingDartArc B base) d
          (((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.rot d) := by
  classical
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
      exact hdir
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
  let base : D39DrawingRepresentationData M B :=
    { vertexEquiv := V
      positions_injective := hpos
      dartEquiv := E
      dart_tail_vertex := htail
      dart_head_vertex := hhead
      dart_edgeInv := hflip
      dart_missing := hmissing
      dart_orientation := horientation
      root_mark := hroot
      faceOfDart := faceOfDart
      faceOrbit_iff := hfaceOrbit
      face_surjective := hfaceSurj
      face_left_of_dart := fun d =>
        uibhbotD39CanonicalAssembly_sideOfDart W D hhit C₀ iso d }
  have hbase : base.dartEquiv = E := rfl
  have hface : ∀ d,
      (base.faceOfDart d).val =
        (G.toPlaneGraphDrawingFaceEquiv.symm
          (faceEquiv (Quotient.mk _ d))).val := by
    intro d
    rfl
  have hparams (x : M.core.D) :
      ∃ φ : I ≃ₜ I, φ 0 = 0 ∧ φ 1 = 1 ∧
        ∀ t, d39DrawingDartArc B base x t =
          (G.arc (iso.toEquiv.symm x)).toPath (φ t) := by
    have hdraw := uibhbotD39CanonicalAssembly_drawingDartArc_eq W D base x
    have hdart : base.dartEquiv x = E x := congrArg (fun f => f x) hbase
    change d39DrawingDartArc B base x =
      (if (base.dartEquiv x).2 then
        (fun t => (G.arc (base.dartEquiv x).1.out).toPath t)
      else (fun t => (G.arc (base.dartEquiv x).1.out).toPath.symm t)) at hdraw
    rw [hdart] at hdraw
    have hpoly := uibhbotD39CanonicalAssembly_arcIdentification W D hhit C₀ iso x
    change (if (E x).2 then G.arc (E x).1.out
      else (G.arc (E x).1.out).reverse) = G.arc (iso.toEquiv.symm x) at hpoly
    cases hb : (E x).2
    · have hp : (G.arc (E x).1.out).reverse = G.arc (iso.toEquiv.symm x) := by
        simpa only [hb, Bool.false_eq_true, ↓reduceIte] using hpoly
      obtain ⟨φ, h0, h1, hφ⟩ := polyline_reverse_toPath_exists_reparam
        (G.arc (E x).1.out) (G.arc_length _) (G.arc_simple _)
      refine ⟨φ, h0, h1, ?_⟩
      intro t
      have ht := congrFun hdraw t
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at ht
      exact ht.trans ((hφ t).trans (congrArg (fun p : Polyline => p.toPath (φ t)) hp))
    · have hp : G.arc (E x).1.out = G.arc (iso.toEquiv.symm x) := by
        simpa only [hb, ↓reduceIte] using hpoly
      refine ⟨Homeomorph.refl I, rfl, rfl, ?_⟩
      intro t
      have ht := congrFun hdraw t
      simp only [hb, ↓reduceIte] at ht
      exact ht.trans (congrArg (fun p : Polyline => p.toPath t) hp)
  let param : M.core.D → I ≃ₜ I := fun x => Classical.choose (hparams x)
  have hparam0 (x : M.core.D) : param x 0 = 0 :=
    (Classical.choose_spec (hparams x)).1
  have hparam1 (x : M.core.D) : param x 1 = 1 :=
    (Classical.choose_spec (hparams x)).2.1
  have hpaths : d39DrawingDartArc B base =
      fun x t => (G.arc (iso.toEquiv.symm x)).toPath (param x t) := by
    funext x t
    exact (Classical.choose_spec (hparams x)).2.2 t
  refine ⟨hhit, C₀, iso, base, hbase, hface, ?_⟩
  intro d
  rw [hpaths]
  exact d39TopologicalCcwSuccessor_comp_intervalHomeomorph
    {e | rootedLocallyFiniteVertexClass M.core.rot e =
      rootedLocallyFiniteVertexClass M.core.rot d}
    (fun e t => (G.arc (iso.toEquiv.symm e)).toPath t) param hparam0 hparam1
    (uibhbotD39CanonicalAssembly_pl_rotation_topological_successor W D hhit C₀ iso d)

/-- Helper toward Proposition 5.16. The selected canonical representation
also has the frontier/incidence field after identifying its face with the
assembly face. -/
theorem uibhbotD39CanonicalRepresentation14_data3
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
    let M := (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
    Nonempty (D39DrawingRepresentationData3 M B) := by
  classical
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
  let M := (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
  obtain ⟨hhit, C₀, iso, base, hbase, hface, hsuccessor⟩ :=
    uibhbotD39CanonicalAssembly_rotation_topological_successor_with_face W hW D
  let faceEquiv := uibhbotD39CanonicalAssembly_faceOrbitEquiv' W D hhit C₀ iso
  let E := iso.toEquiv.symm.trans
    (uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa)
  have hvertex (d : M.core.D) :
      base.vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot d) =
        wholePlaneDartVertex W (iso.toEquiv.symm d) := by
    have htail := base.dart_tail_vertex d
    rw [congrArg (fun f => f d) hbase] at htail
    calc
      base.vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot d) =
          if (E d).2 then B.map.toPlaneMapWithMissing.src (E d).1
          else B.map.toPlaneMapWithMissing.tgt (E d).1 := htail
      _ = boundaryDartInitial B.map (E d) :=
        (boundaryDartInitial_eq (M := B.map) (E d)).symm
      _ = wholePlaneDartVertex W (iso.toEquiv.symm d) := by
        change boundaryDartInitial
            (uibhbotAssemblyDirectedPlaneMapWithMissing W D.rotation D.boundary
              D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
              P hp ha F hf hFim hFa D.pastRightPositive)
            (uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
              D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
              P hp ha F hf hFim hFa (iso.toEquiv.symm d)) = _
        exact uibhbotAssemblyBoundaryDartEquiv3_initialVertex
          W D.rotation D.boundary D.pastLeftUnbounded D.pastRightNonnegative
          D.pastFiniteIncidence P hp ha F hf hFim hFa D.pastRightPositive
          (iso.toEquiv.symm d)
  have hcycles (d : M.core.D)
      (v : RootedLocallyFiniteVertex M.core.D M.core.rot) :
      (∃ e : M.core.D,
        Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e ∧
          rootedLocallyFiniteVertexClass M.core.rot e = v) ↔
      (∃ e : WholePlaneDart W,
        (wholePlaneFaceSucc W D.rotation).SameCycle (iso.toEquiv.symm d) e ∧
          wholePlaneDartVertex W e = base.vertexEquiv v) := by
    constructor
    · rintro ⟨e, hcycle, hvertex'⟩
      refine ⟨iso.toEquiv.symm e, ?_, ?_⟩
      · have hcode : Equiv.Perm.SameCycle
            (((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.rot.symm *
              ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.edgeInv)
            (iso.toEquiv (iso.toEquiv.symm d)) (iso.toEquiv (iso.toEquiv.symm e)) := by
          simpa [M] using hcycle
        have hwhole := (iso.faceSameCycle_iff (iso.toEquiv.symm d)
          (iso.toEquiv.symm e)).mpr hcode
        change (wholePlaneFaceSucc W D.rotation).SameCycle
          (iso.toEquiv.symm d) (iso.toEquiv.symm e) at hwhole
        exact hwhole
      · calc
          wholePlaneDartVertex W (iso.toEquiv.symm e) =
              base.vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot e) :=
                (hvertex e).symm
          _ = base.vertexEquiv v := congrArg base.vertexEquiv hvertex'
    · rintro ⟨e, hcycle, hvertex'⟩
      refine ⟨iso.toEquiv e, ?_, ?_⟩
      · have hwhole : Equiv.Perm.SameCycle
            (((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap).core.rot.symm *
              ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap).core.edgeInv)
            (iso.toEquiv.symm d) e := by
          change (wholePlaneFaceSucc W D.rotation).SameCycle
            (iso.toEquiv.symm d) e
          exact hcycle
        have hcode := (iso.faceSameCycle_iff (iso.toEquiv.symm d) e).mp hwhole
        simpa only [Equiv.apply_symm_apply, M] using hcode
      · apply base.vertexEquiv.injective
        calc
          base.vertexEquiv
              (rootedLocallyFiniteVertexClass M.core.rot (iso.toEquiv e)) =
              wholePlaneDartVertex W e := by
                have hv := hvertex (iso.toEquiv e)
                exact hv.trans (congrArg (wholePlaneDartVertex W)
                  (Equiv.symm_apply_apply iso.toEquiv e))
          _ = base.vertexEquiv v := hvertex'
  have hfrontier : ∀ (d : M.core.D)
      (v : RootedLocallyFiniteVertex M.core.D M.core.rot),
      B.map.toPlaneMapWithMissing.pos (base.vertexEquiv v) ∈
          frontier (base.faceOfDart d).val ↔
        ∃ e : M.core.D,
          Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e ∧
            rootedLocallyFiniteVertexClass M.core.rot e = v := by
    intro d v
    have hassembly := uibhbotD39Assembly_vertex_frontier_iff_faceCycle W D
      (iso.toEquiv.symm d) (base.vertexEquiv v)
    have hfrontier' : B.map.toPlaneMapWithMissing.pos (base.vertexEquiv v) ∈
        frontier (base.faceOfDart d).val ↔
      ∃ e : WholePlaneDart W,
        (wholePlaneFaceSucc W D.rotation).SameCycle (iso.toEquiv.symm d) e ∧
          wholePlaneDartVertex W e = base.vertexEquiv v := by
      change G.pos (base.vertexEquiv v) ∈
        frontier (base.faceOfDart d).val ↔ _
      rw [hface d, uibhbotD39CanonicalAssembly_faceOrbitEquiv'_mk
        W D hhit C₀ iso d]
      exact hassembly
    exact hfrontier'.trans (hcycles d v).symm
  let data : D39DrawingRepresentationData3 M B :=
    { toD39DrawingRepresentationData := base
      rotation_topological_successor := hsuccessor
      vertex_frontier_incidence := hfrontier }
  exact ⟨data⟩

/-- Helper toward Proposition 5.16. The canonical code map is represented by
the v3 candidate drawing data for each admitted witness. -/
theorem uibhbotD39CanonicalRepresentation14_represents3
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
    let M := (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
    D39DrawingRepresents3 M B := by
  classical
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
  let M := (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
  rcases uibhbotD39CanonicalRepresentation14_data3 W hW D with ⟨data⟩
  exact ⟨data⟩

end DirectedDistances.PaperProofs.Section5

end
