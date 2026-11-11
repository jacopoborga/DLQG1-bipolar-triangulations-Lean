/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation2
public import DirectedDistances.PaperProofs.Section5.UIBHBOTBoundaryPresentationGeometry3

/-! Helper toward Proposition 5.16.

This module records the representative-adjusted endpoint transport needed to
relate the code map's rotation classes to the canonical geometric assembly.
It makes no paper-completion claim. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

noncomputable section

/-- Helper toward Proposition 5.16. The whole-plane rotation quotient is
bijectionally identified with the colimit vertex carrier by the dart's
incident vertex. -/
def uibhbotD39WholePlaneVertexEquiv (W : ℤ → Fin 3)
    (D : UIBHBOTD39CanonicalDomainWitness W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0) :
    RootedLocallyFiniteVertex
      ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap).core.D
      ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap).core.rot ≃
      WholePlaneVertex W := by
  classical
  let f : RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W D.rotation) →
      WholePlaneVertex W :=
    Quotient.lift (wholePlaneDartVertex W) (fun d e h =>
      (wholePlaneRotation_sameCycle_dartVertex W D.rotation d e h).symm)
  have hf : Function.Bijective f := by
    constructor
    · intro v w hvw
      revert hvw
      refine Quotient.inductionOn₂ v w ?_
      intro d e hvw
      change wholePlaneDartVertex W d = wholePlaneDartVertex W e at hvw
      change Quotient.mk _ d = Quotient.mk _ e
      exact Quotient.sound
        (wholePlaneRotation_sameVertex_sameCycle_proof W D.rotation d e hvw)
    · intro v
      obtain ⟨d, hd⟩ := WholePlanePastGlueData.vertex_incident W v
      refine ⟨rootedLocallyFiniteVertexClass (wholePlaneRotation W D.rotation) d, ?_⟩
      change wholePlaneDartVertex W d = v
      exact hd
  exact Equiv.ofBijective f hf

/-- Helper toward Proposition 5.16. The isomorphism in the canonical
representation certificate induces the vertex correspondence from code-map
rotation classes to whole-plane vertices. -/
def uibhbotD39CanonicalAssemblyVertexEquiv
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0)
    (iso : D39RootedMapIso
      ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap)
      ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap)) :
    RootedLocallyFiniteVertex
      ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.D
      ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.rot ≃
      WholePlaneVertex W :=
  iso.symm.vertexEquiv.trans (uibhbotD39WholePlaneVertexEquiv W D hhit C₀)

/-- Helper toward Proposition 5.16. The code-map dart's incident vertex is
the assembly endpoint selected by the representative-adjusted Boolean dart
coordinate. This unfolds the assembly source and target endpoint definitions
and retains both Boolean cases. -/
theorem uibhbotD39CanonicalAssembly_endpoint
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
    let A := uibhbotD39CanonicalAssemblyMap W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      D.pastRightPositive
    let dartEquiv := iso.toEquiv.symm.trans
      (uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
        D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
        P hp ha F hf hFim hFa)
    (uibhbotD39CanonicalAssemblyVertexEquiv W D hhit C₀ iso)
        (rootedLocallyFiniteVertexClass
          ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.rot d) =
      if (dartEquiv d).2 then A.toPlaneMapWithMissing.src (dartEquiv d).1
      else A.toPlaneMapWithMissing.tgt (dartEquiv d).1 := by
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
  let e := iso.toEquiv.symm d
  have hv : (uibhbotD39CanonicalAssemblyVertexEquiv W D hhit C₀ iso)
      (rootedLocallyFiniteVertexClass
        ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.rot d) =
      wholePlaneDartVertex W e := by
    change (uibhbotD39WholePlaneVertexEquiv W D hhit C₀)
        (iso.symm.vertexMap
          (d39VertexClass
            ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap) d)) = _
    rw [iso.symm.vertexMap_dart]
    rfl
  have hinit := uibhbotAssemblyBoundaryDartEquiv3_initialVertex
    W D.rotation D.boundary D.pastLeftUnbounded D.pastRightNonnegative
    D.pastFiniteIncidence P hp ha F hf hFim hFa D.pastRightPositive e
  change (uibhbotD39CanonicalAssemblyVertexEquiv W D hhit C₀ iso)
      (rootedLocallyFiniteVertexClass
        ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.rot d) =
    if (E e).2 then A.toPlaneMapWithMissing.src (E e).1
    else A.toPlaneMapWithMissing.tgt (E e).1
  calc
    _ = wholePlaneDartVertex W e := hv
    _ = boundaryDartInitial A (E e) := hinit.symm
    _ = if (E e).2 then A.toPlaneMapWithMissing.src (E e).1
        else A.toPlaneMapWithMissing.tgt (E e).1 :=
      boundaryDartInitial_eq (M := A) (E e)

/-- Helper toward Proposition 5.16. On present whole-plane edges, the
representative-adjusted Boolean coordinate agrees with the assembly's stored
forward direction exactly when the dart is the combinatorial tail. -/
theorem uibhbotD39CanonicalAssembly_wholePlaneOrientation
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (hforward : ∀ a : {a : (uibhbotCcw_assemblyDrawing W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      (uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
        D.pastRightNonnegative D.pastFiniteIncidence)
      (uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
        D.pastRightNonnegative D.pastFiniteIncidence)
      (uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
        D.pastRightNonnegative D.pastFiniteIncidence)
      (uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary)
      (uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary)
      (uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary)
      (uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary)).GeometricEdge //
      ¬ (uibhbotD39CanonicalAssemblyMap W D.rotation D.boundary
        D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
        D.pastRightPositive).missing a},
      (uibhbotD39CanonicalAssemblyMap W D.rotation D.boundary
        D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
        D.pastRightPositive).forward a = !a.val.out.2)
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

/-- Helper toward Proposition 5.16. The composed dart equivalence sends the
code map's ordered root mark to the ordered root mark of the canonical
assembly, including its representative-adjusted Boolean coordinate. -/
theorem uibhbotD39CanonicalAssembly_rootMark
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
    let E := uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa
    let M := (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
    (iso.toEquiv.symm.trans E) M.rootMark.dart =
      uibhbotD39CanonicalAssemblyRoot W D.rotation D.boundary
        D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence := by
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
  let M := (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
  let N := (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
  have hroot : iso.toEquiv.symm M.rootMark.dart = N.rootMark.dart := by
    calc
      iso.toEquiv.symm M.rootMark.dart =
          iso.toEquiv.symm (iso.toEquiv N.rootMark.dart) := by
        rw [← iso.root_dart_comm]
      _ = N.rootMark.dart := iso.toEquiv.symm_apply_apply _
  change E (iso.toEquiv.symm M.rootMark.dart) = _
  rw [hroot]
  change E (uibhbotWholePlaneRootDart W) =
    uibhbotD39CanonicalAssemblyRoot W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
  let d : WholePlaneDart W := (uibhbotRootEdge W, false)
  let q : G.GeometricEdge := Quotient.mk G.edgeSetoid d
  classical
  have hrep := G.geometricEdge_out_mk d
  change uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa d =
    uibhbotAssemblyD39RootMark W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa
  rw [uibhbotAssemblyD39RootMark_eq W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P hp ha F hf hFim hFa]
  simp only [uibhbotAssemblyBoundaryDartEquiv3,
    uibhbotAssemblyBoundaryDartAdjust, uibhbotAssemblyBoundaryDartEquiv]
  change (q, if q.out.2 then !!false else !false) =
    (q, decide (q.out = d))
  rcases hrep with hrep | hrep
  · have hout : q.out = d := by simpa [q] using hrep
    simp [hout]
  · have hout : q.out = wholePlaneDartFlip W d := by simpa [q] using hrep
    have hne : wholePlaneDartFlip W d ≠ d := wholePlaneDartFlip_ne W d
    simp [hout, hne]
    change true = true
    rfl





































end


end DirectedDistances.PaperProofs.Section5

end
