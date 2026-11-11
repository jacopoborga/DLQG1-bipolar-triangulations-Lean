/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation10
public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleRotationField

/-! Helper toward Proposition 5.16.

This module transports vertex stars and the topological successor of the
canonical assembly's PL paths along the whole-plane/code-map isomorphism.
The exact selected-representative path formula retains its direction bit.
Endpoint-fixing reparameterizations bridge path reversal and polyline reversal.
The Rep8 field assembly is reconstructed with its dart equivalence exposed,
giving a constructed representation with the topological rotation field. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap DirectedDistances.KMSW
open DirectedDistances.PaperProofs.SourceResults
open unitInterval

/-- Helper toward Proposition 5.16. Reindexing a family of arcs by a dart
equivalence preserves and reflects its topological successor relation. -/
theorem d39TopologicalCcwSuccessor_map_equiv_iff {A C : Type*}
    (ι : A ≃ C) (star : Set A) (arc : A → I → ℂ) (d e : A) :
    D39TopologicalCcwSuccessor (ι '' star)
        (fun x t => arc (ι.symm x) t) (ι d) (ι e) ↔
      D39TopologicalCcwSuccessor star arc d e := by
  constructor
  · intro h
    have hback := d39TopologicalCcwSuccessor_map_equiv ι.symm h
    simpa only [Equiv.symm_symm, Equiv.symm_apply_apply,
      Set.image_image, Function.comp_def, Set.image_id'] using hback
  · exact d39TopologicalCcwSuccessor_map_equiv ι

/-- Helper toward Proposition 5.16. Endpoint-fixing interval
homeomorphisms preserve initial subarc images and hence the topological
successor relation, independently for every dart of the star. -/
theorem d39TopologicalCcwSuccessor_comp_intervalHomeomorph {A : Type*}
    (star : Set A) (arc : A → I → ℂ) (param : A → I ≃ₜ I)
    (h0 : ∀ x, param x 0 = 0) (h1 : ∀ x, param x 1 = 1)
    {d e : A} (h : D39TopologicalCcwSuccessor star arc d e) :
    D39TopologicalCcwSuccessor star
      (fun x t => arc x (param x t)) d e := by
  rcases h with ⟨H, hH, dir, hdir, harg, hsucc, hstraight⟩
  refine ⟨H, hH, dir, hdir, harg, hsucc, ?_⟩
  intro x hx
  obtain ⟨t, ht0, ht1, him⟩ := hstraight x hx
  let φ := param x
  have hφ : StrictMono φ := by
    apply φ.continuous.strictMono_of_inj_boundedOrder ?_ φ.injective
    change φ 0 ≤ φ 1
    rw [h0 x, h1 x]
    exact zero_le_one
  have hi0 : φ.symm 0 = 0 := by
    apply φ.injective
    rw [φ.apply_symm_apply, h0 x]
  have hi1 : φ.symm 1 = 1 := by
    apply φ.injective
    rw [φ.apply_symm_apply, h1 x]
  have hi : StrictMono φ.symm := by
    apply φ.symm.continuous.strictMono_of_inj_boundedOrder ?_ φ.symm.injective
    change φ.symm 0 ≤ φ.symm 1
    rw [hi0, hi1]
    exact zero_le_one
  refine ⟨φ.symm t, ?_, ?_, ?_⟩
  · have ht : (0 : I) < t := ht0
    have hi' := hi ht
    rw [hi0] at hi'
    exact hi'
  · have ht : t < (1 : I) := ht1
    have hi' := hi ht
    rw [hi1] at hi'
    exact hi'
  · have him' :
        (fun s => arc x (φ s)) '' Set.Icc (0 : I) (φ.symm t) =
          arc x '' Set.Icc (0 : I) t := by
      ext z
      constructor
      · rintro ⟨s, hs, rfl⟩
        refine ⟨φ s, ⟨?_, ?_⟩, rfl⟩
        · rw [← h0 x]
          exact hφ.monotone hs.1
        · simpa only [φ.apply_symm_apply] using hφ.monotone hs.2
      · rintro ⟨s, hs, rfl⟩
        refine ⟨φ.symm s, ⟨?_, hi.monotone hs.2⟩, ?_⟩
        · rw [← hi0]
          exact hi.monotone hs.1
        · exact congrArg (arc x) (φ.apply_symm_apply s)
    change H '' ((fun s => arc x (φ s)) '' Set.Icc (0 : I) (φ.symm t)) = _
    rw [him']
    exact him

/-- Helper toward Proposition 5.16. The path of any representation on
the canonical assembly is exactly the selected representative's PL path,
with path reversal precisely in the false-bit case. This does not replace
path reversal by reversal of the polyline's point list. -/
theorem uibhbotD39CanonicalAssembly_drawingDartArc_eq
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W) :
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
    ∀ (base : D39DrawingRepresentationData M B) (d : M.core.D),
      d39DrawingDartArc B base d =
        if (base.dartEquiv d).2 then
          (fun t => (G.arc (base.dartEquiv d).1.out).toPath t)
        else
          (fun t => (G.arc (base.dartEquiv d).1.out).toPath.symm t) := by
  dsimp only
  intro base d
  funext t
  cases hb : (base.dartEquiv d).2 <;>
    simp only [d39DrawingDartArc, hb, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

/-- Helper toward Proposition 5.16. Reversing a simple polyline and
reversing its path have the same oriented traversal up to an endpoint-fixing
interval homeomorphism; their actual parameter schedules are retained. -/
theorem polyline_reverse_toPath_exists_reparam
    (p : Polyline) (hlen : 2 ≤ p.points.length) (hp : p.IsSimple) :
    ∃ φ : I ≃ₜ I, φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ t, p.toPath.symm t = p.reverse.toPath (φ t) := by
  let γ : Path p.finish p.start := p.reverse.toPath.cast
    (Polyline.start_reverse p).symm (Polyline.finish_reverse p).symm
  have hγ : Function.Injective γ :=
    p.reverse.toPath_injective
      (by simpa only [Polyline.reverse, List.length_reverse] using hlen)
      (p.isSimple_reverse_transfer hp)
  have hδ : Function.Injective p.toPath.symm :=
    (p.toPath_injective hlen hp).comp unitInterval.symm_bijective.injective
  have hrange : Set.range p.toPath.symm = Set.range γ := by
    change Set.range p.toPath.symm = Set.range p.reverse.toPath
    rw [Path.symm_range, Polyline.range_toPath, Polyline.range_toPath,
      Polyline.image_reverse_transfer]
  obtain ⟨φ, h0, h1, heq⟩ :=
    exists_path_reparam_of_injective_range_eq γ p.toPath.symm hγ hδ hrange
  refine ⟨φ, h0, h1, ?_⟩
  intro t
  exact congrArg (fun q : Path p.finish p.start => q t) heq

/-- Helper toward Proposition 5.16. Whole-plane geometric vertices are
exactly the rotation classes, retaining each individual dart in the star. -/
theorem uibhbotD39WholePlane_vertexClass_eq_iff
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (d e : WholePlaneDart W) :
    rootedLocallyFiniteVertexClass (wholePlaneRotation W D.rotation) d =
        rootedLocallyFiniteVertexClass (wholePlaneRotation W D.rotation) e ↔
      wholePlaneDartVertex W d = wholePlaneDartVertex W e := by
  constructor
  · intro h
    exact (wholePlaneRotation_sameCycle_dartVertex W D.rotation d e
      (Quotient.exact h)).symm
  · intro h
    exact Quotient.sound
      (wholePlaneRotation_sameVertex_sameCycle_proof W D.rotation d e h)

section CanonicalTransport

variable (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0)
    (iso : D39RootedMapIso
      ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap)
      ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap))

/-- Helper toward Proposition 5.16. The inverse code-map isomorphism
intertwines the code-map rotation with the canonical assembly rotation. -/
theorem uibhbotD39CanonicalAssembly_dart_rotation
    (d : ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.D) :
    iso.toEquiv.symm
        (((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.rot d) =
      wholePlaneRotation W D.rotation (iso.toEquiv.symm d) := by
  exact iso.symm.rot_comm d

/-- Helper toward Proposition 5.16. The inverse code-map dart equivalence
sends its entire rotation-class star onto the whole-plane geometric star. -/
theorem uibhbotD39CanonicalAssembly_dart_star
    (d : ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.D) :
    let M := (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
    iso.toEquiv.symm ''
        {e | rootedLocallyFiniteVertexClass M.core.rot e =
          rootedLocallyFiniteVertexClass M.core.rot d} =
      {e | wholePlaneDartVertex W e = wholePlaneDartVertex W (iso.toEquiv.symm d)} := by
  let M := (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
  have hclass (e : M.core.D) :
      rootedLocallyFiniteVertexClass M.core.rot e =
          rootedLocallyFiniteVertexClass M.core.rot d ↔
        wholePlaneDartVertex W (iso.toEquiv.symm e) =
          wholePlaneDartVertex W (iso.toEquiv.symm d) := by
    have hm (x : M.core.D) : iso.symm.vertexEquiv
        (rootedLocallyFiniteVertexClass M.core.rot x) =
          rootedLocallyFiniteVertexClass (wholePlaneRotation W D.rotation)
            (iso.toEquiv.symm x) := iso.symm.vertexMap_dart x
    constructor
    · intro he
      have he' := congrArg iso.symm.vertexEquiv he
      rw [hm e, hm d] at he'
      exact (uibhbotD39WholePlane_vertexClass_eq_iff W D
        (iso.toEquiv.symm e) (iso.toEquiv.symm d)).mp he'
    · intro he
      apply iso.symm.vertexEquiv.injective
      rw [hm e, hm d]
      exact (uibhbotD39WholePlane_vertexClass_eq_iff W D
        (iso.toEquiv.symm e) (iso.toEquiv.symm d)).mpr he
  ext e
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hclass x).mp hx
  · intro he
    change wholePlaneDartVertex W e = wholePlaneDartVertex W (iso.toEquiv.symm d) at he
    refine ⟨iso.toEquiv e, ?_, iso.toEquiv.symm_apply_apply e⟩
    apply (hclass _).mpr
    exact (congrArg (wholePlaneDartVertex W) (iso.toEquiv.symm_apply_apply e)).trans he

/-- Helper toward Proposition 5.16. The code-map rotation is the
topological successor for the canonical assembly's PL paths pulled back by
the dart isomorphism. No identification with a chosen representation record
is asserted here. -/
theorem uibhbotD39CanonicalAssembly_pl_rotation_topological_successor
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
    D39TopologicalCcwSuccessor
      {e | rootedLocallyFiniteVertexClass M.core.rot e =
        rootedLocallyFiniteVertexClass M.core.rot d}
      (fun e t => (G.arc (iso.toEquiv.symm e)).toPath t) d (M.core.rot d) := by
  let G := uibhbotCcw_assemblyDrawing W D.rotation D.boundary
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
    (uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary)
  change D39TopologicalCcwSuccessor _
    (fun e t => (G.arc (iso.toEquiv.symm e)).toPath t) d _
  rw [← d39TopologicalCcwSuccessor_map_equiv_iff iso.toEquiv.symm]
  rw [uibhbotD39CanonicalAssembly_dart_star W D hhit C₀ iso d,
    uibhbotD39CanonicalAssembly_dart_rotation W D hhit C₀ iso d]
  have harcs :
      (fun (x : WholePlaneDart W) (t : I) =>
        (G.arc (iso.toEquiv.symm (iso.toEquiv x))).toPath t) =
      (fun (x : WholePlaneDart W) (t : I) => (G.arc x).toPath t) := by
    funext x t
    exact congrArg (fun e => (G.arc e).toPath t) (iso.toEquiv.symm_apply_apply x)
  change D39TopologicalCcwSuccessor _
    (fun (x : WholePlaneDart W) (t : I) =>
      (G.arc (iso.toEquiv.symm (iso.toEquiv x))).toPath t) _ _
  rw [harcs]
  exact plDrawing_toPath_rotation_topological_ccwSuccessor G (iso.toEquiv.symm d)

end CanonicalTransport

/-- Helper toward Proposition 5.16. The canonical assembly fields give the
code map a drawing-representation record with its exact dart equivalence exposed.
This repeats Rep8's field assembly with a structure literal: its exported
existence theorem and the opaque field assembler do not expose this equation. -/
theorem uibhbotD39CanonicalAssembly_drawingRepresentationData_with_dartEquiv
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
            P hp ha F hf hFim hFa) := by
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
  exact ⟨hhit, C₀, iso, base, rfl⟩

/-- Helper toward Proposition 5.16. The canonical assembly admits a
record with the prescribed dart equivalence and topological rotation field.
This is an existence statement for the constructed record, not for arbitrary
base representations. -/
theorem uibhbotD39CanonicalAssembly_rotation_topological_successor
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
        ∀ d, D39TopologicalCcwSuccessor
          {e | rootedLocallyFiniteVertexClass
              ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.rot e =
            rootedLocallyFiniteVertexClass
              ((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.rot d}
          (d39DrawingDartArc B base) d
          (((uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap).core.rot d) := by
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
  obtain ⟨hhit, C₀, iso, base, hbase⟩ :=
    uibhbotD39CanonicalAssembly_drawingRepresentationData_with_dartEquiv W hW D
  let E := iso.toEquiv.symm.trans
    (uibhbotAssemblyBoundaryDartEquiv3 W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa)
  change base.dartEquiv = E at hbase
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
  refine ⟨hhit, C₀, iso, base, hbase, ?_⟩
  intro d
  rw [hpaths]
  exact d39TopologicalCcwSuccessor_comp_intervalHomeomorph
    {e | rootedLocallyFiniteVertexClass M.core.rot e =
      rootedLocallyFiniteVertexClass M.core.rot d}
    (fun e t => (G.arc (iso.toEquiv.symm e)).toPath t) param hparam0 hparam1
    (uibhbotD39CanonicalAssembly_pl_rotation_topological_successor W D hhit C₀ iso d)

















































end DirectedDistances.PaperProofs.Section5

end
