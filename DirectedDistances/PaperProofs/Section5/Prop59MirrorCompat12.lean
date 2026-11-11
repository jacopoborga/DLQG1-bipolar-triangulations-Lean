/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59MirrorCompat11
public import DirectedDistances.PaperProofs.Section5.Prop59RootAbsentAE
import DirectedDistances.PlanarMap.D39DrawingRepresentation3
import DirectedDistances.PaperProofs.Section3.D39GeomMirror

/-! Helpers toward Proposition 5.9 (`prop-uihbot-sym`). -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open scoped ComplexConjugate

/-- Helper toward Proposition 5.9. The dart carriers of a locally finite
map and its combinatorial mirror are identified by the identity map. -/
@[expose] def prop59_mirrorDartCarrierEquiv (M : RootedLocallyFiniteMap) :
    (mirrorRootedLocallyFiniteMap M).toD39RootedMap.core.D ≃
      M.toD39RootedMap.core.D := Equiv.refl _

/-- Helper toward Proposition 5.9. The dart-carrier equivalence acts as the
identity on representatives in either direction. -/
@[simp] theorem prop59_mirrorDartCarrierEquiv_apply
    (M : RootedLocallyFiniteMap)
    (d : (mirrorRootedLocallyFiniteMap M).toD39RootedMap.core.D) :
    prop59_mirrorDartCarrierEquiv M d = d := rfl

/-- Helper toward Proposition 5.9. The inverse dart-carrier equivalence acts
as the identity on representatives. -/
@[simp] theorem prop59_mirrorDartCarrierEquiv_symm_apply
    (M : RootedLocallyFiniteMap)
    (d : M.toD39RootedMap.core.D) :
    (prop59_mirrorDartCarrierEquiv M).symm d = d := rfl

/-- Helper toward Proposition 5.9. A mapped path evaluates pointwise as the
conjugate of the original path. -/
theorem prop59_conjMapPath_apply {z w : ℂ} (γ : Path z w) (t : unitInterval) :
    (γ.map Complex.continuous_conj) t = conj (γ t) := by
  exact congrFun (Path.map_coe γ Complex.continuous_conj) t


/- OPEN (B), exact full binders and target:
For every `M : RootedLocallyFiniteMap`, `B :
DirectedDistances.PaperProofs.SourceResults.D39DomainRootedMapV2`,
`x : D39DrawingRepresentationData3 M.toD39RootedMap B`, and
`hmirrorDomain : D39GeomDomain B.map.geomMirror (d39GeomMirrorRoot B.root)`,
construct
`D39DrawingRepresentationData3
  (mirrorRootedLocallyFiniteMap M).toD39RootedMap
  ⟨B.V, B.E, B.map.geomMirror, d39GeomMirrorRoot B.root, hmirrorDomain⟩`.
transport obligations; it is retained only as an inactive work record. -/
/- noncomputable def prop59_mirrorRepresentationData3
    (M : RootedLocallyFiniteMap)
    (B : DirectedDistances.PaperProofs.SourceResults.D39DomainRootedMapV2)
    (x : D39DrawingRepresentationData3 M.toD39RootedMap B)
    (hmirrorDomain : D39GeomDomain B.map.geomMirror
      (d39GeomMirrorRoot B.root)) :
    D39DrawingRepresentationData3
      (mirrorRootedLocallyFiniteMap M).toD39RootedMap
      ⟨B.V, B.E, B.map.geomMirror, d39GeomMirrorRoot B.root,
        hmirrorDomain⟩ := by
  classical
  let V := prop59_mirrorRotationVertexEquiv M.toD39RootedMap.core.rot
  let B' : DirectedDistances.PaperProofs.SourceResults.D39DomainRootedMapV2 :=
    ⟨B.V, B.E, B.map.geomMirror, d39GeomMirrorRoot B.root, hmirrorDomain⟩
  let base : D39DrawingRepresentationData
      (mirrorRootedLocallyFiniteMap M).toD39RootedMap B' := {
    vertexEquiv := V.symm.trans x.vertexEquiv
    positions_injective := by
      change Function.Injective (B.map.geomMirror.toPlaneMapWithMissing.pos)
      intro u v huv
      apply x.positions_injective
      change conj (B.map.toPlaneMapWithMissing.pos u) =
        conj (B.map.toPlaneMapWithMissing.pos v) at huv
      exact geomConj.injective huv
    dartEquiv := x.dartEquiv
    dart_tail_vertex := by
      intro d
      exact prop59_mirrorRepresentation_dart_endpoints M B x d
    dart_head_vertex := by
      intro d
      exact prop59_mirrorRepresentation_dart_headEndpoint M B x d
    dart_edgeInv := by
      intro d
      exact prop59_mirrorRepresentation_dart_edgeInv M B x d
    dart_missing := by
      intro d
      exact (prop59_mirrorRepresentation_edge_fields M B x d).1
    dart_orientation := by
      intro d hd
      have hfields := prop59_mirrorRepresentation_edge_fields M B x d
      have hdB : ¬ B.map.geomMirror.toPlaneMapWithMissing.missing
          (x.dartEquiv d).1 := by
        intro hm
        exact hd (hfields.1.mp hm)
      exact hfields.2 hdB
    root_mark := prop59_mirrorRepresentation_rootMark M B x
    faceOfDart := fun d => B.map.geomMirrorEquiv.faceMap
      (x.faceOfDart (M.toD39RootedMap.core.edgeInv d))
    faceOrbit_iff := by
      intro d e
      constructor
      · intro h
        have hbase : x.faceOfDart (M.toD39RootedMap.core.edgeInv d) =
            x.faceOfDart (M.toD39RootedMap.core.edgeInv e) := by
          apply B.map.geomMirrorEquiv.faceEquiv.injective
          change B.map.geomMirrorEquiv.faceEquiv _ =
            B.map.geomMirrorEquiv.faceEquiv _
          exact h
        have hcycle := (x.faceOrbit_iff _ _).mp hbase
        have hmirror :=
          (prop59_mirrorFaceCycle M (M.edgeInv d) (M.edgeInv e)).mpr hcycle
        rw [M.edgeInv_invol d, M.edgeInv_invol e] at hmirror
        change Equiv.Perm.SameCycle ((M.rot.symm).symm * M.edgeInv) d e
        rw [Equiv.symm_symm]
        exact hmirror
      · intro hcycle
        change Equiv.Perm.SameCycle ((M.rot.symm).symm * M.edgeInv) d e at hcycle
        rw [Equiv.symm_symm] at hcycle
        have hnewInv : Equiv.Perm.SameCycle (M.rot * M.edgeInv)
            (M.edgeInv (M.edgeInv d)) (M.edgeInv (M.edgeInv e)) := by
          rw [M.edgeInv_invol d, M.edgeInv_invol e]
          exact hcycle
        have hbase : Equiv.Perm.SameCycle
            (M.toD39RootedMap.core.rot.symm * M.toD39RootedMap.core.edgeInv)
            (M.toD39RootedMap.core.edgeInv d)
            (M.toD39RootedMap.core.edgeInv e) := by
          exact (prop59_mirrorFaceCycle M (M.edgeInv d) (M.edgeInv e)).mp hnewInv
        have hfaces := (x.faceOrbit_iff _ _).mpr hbase
        change B.map.geomMirrorEquiv.faceEquiv _ =
          B.map.geomMirrorEquiv.faceEquiv _
        exact congrArg B.map.geomMirrorEquiv.faceEquiv hfaces
    face_surjective := by
      intro F
      let F₀ := B.map.geomMirrorEquiv.faceEquiv.symm F
      obtain ⟨d, hd⟩ := x.face_surjective F₀
      refine ⟨M.toD39RootedMap.core.edgeInv d, ?_⟩
      change B.map.geomMirrorEquiv.faceMap
        (x.faceOfDart (M.toD39RootedMap.core.edgeInv
          (M.toD39RootedMap.core.edgeInv d))) = F
      rw [M.toD39RootedMap.core.edgeInv_invol, hd]
      exact B.map.geomMirrorEquiv.faceEquiv.apply_symm_apply F
    face_left_of_dart := by
      intro d
      have hside := x.face_left_of_dart
        (M.toD39RootedMap.core.edgeInv d)
      have hpairInv :
          x.dartEquiv (M.toD39RootedMap.core.edgeInv d) =
            ((x.dartEquiv d).1, !(x.dartEquiv d).2) := x.dart_edgeInv d
      rw [hpairInv] at hside
      cases hbit : (x.dartEquiv d).2
      · have hside' : B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf
            (x.faceOfDart (M.toD39RootedMap.core.edgeInv d)) (x.dartEquiv d).1 := by
          simpa [hbit] using hside
        have htransport := (prop59_SideRightOf_geomMirror_iff_SideLeftOf
            B.map.toPlaneMapWithMissing.toPlaneGraphDrawing
            (x.faceOfDart (M.toD39RootedMap.core.edgeInv d))
            (x.dartEquiv d).1).mpr hside'
        change @PlaneGraphDrawing.SideRightOf B.V B.E
          B.map.geomMirror.toPlaneMapWithMissing.toPlaneGraphDrawing
          (B.map.geomMirrorEquiv.faceMap
            (x.faceOfDart (M.toD39RootedMap.core.edgeInv d)))
          (x.dartEquiv d).1
        simpa [DirectedPlaneMapWithMissing.geomMirror] using htransport
      · have hside' : B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf
            (x.faceOfDart (M.toD39RootedMap.core.edgeInv d)) (x.dartEquiv d).1 := by
          simpa [hbit] using hside
        have htransport := (prop59_SideLeftOf_geomMirror_iff_SideRightOf
            B.map.toPlaneMapWithMissing.toPlaneGraphDrawing
            (x.faceOfDart (M.toD39RootedMap.core.edgeInv d))
            (x.dartEquiv d).1).mpr hside'
        change @PlaneGraphDrawing.SideLeftOf B.V B.E
          B.map.geomMirror.toPlaneMapWithMissing.toPlaneGraphDrawing
          (B.map.geomMirrorEquiv.faceMap
            (x.faceOfDart (M.toD39RootedMap.core.edgeInv d)))
          (x.dartEquiv d).1
        simpa [DirectedPlaneMapWithMissing.geomMirror] using htransport
  }
  refine {
    toD39DrawingRepresentationData := base
    rotation_topological_successor := ?_
    vertex_frontier_incidence := ?_
  }
  · intro d
    have harc : d39DrawingDartArc B' base =
        (fun e t => conj (d39DrawingDartArc B
          x.toD39DrawingRepresentationData
          (prop59_mirrorDartCarrierEquiv M e) t)) := by
      funext (e : (mirrorRootedLocallyFiniteMap M).toD39RootedMap.core.D) t
      simp only [d39DrawingDartArc, base, B',
        DirectedPlaneMapWithMissing.geomMirror, PlaneGraphDrawing.geomMirror,
        Path.map_symm, prop59_mirrorDartCarrierEquiv_apply]
      by_cases hbit : (x.dartEquiv e).2 = true
      · rw [if_pos hbit]
        exact prop59_conjMapPath_apply (B.map.arc (x.dartEquiv e).1) t
      · rw [if_neg hbit]
        exact prop59_conjMapPath_apply (B.map.arc (x.dartEquiv e).1).symm t
    rw [harc]
    let toMirror := (prop59_mirrorDartCarrierEquiv M).symm
    let ι := prop59_mirrorDartCarrierEquiv M
    have hstar : toMirror ''
        {e : M.toD39RootedMap.core.D |
          rootedLocallyFiniteVertexClass M.rot.symm e =
            rootedLocallyFiniteVertexClass M.rot.symm (ι d)} =
        {e : (mirrorRootedLocallyFiniteMap M).toD39RootedMap.core.D |
          rootedLocallyFiniteVertexClass
              (mirrorRootedLocallyFiniteMap M).toD39RootedMap.core.rot e =
            rootedLocallyFiniteVertexClass
              (mirrorRootedLocallyFiniteMap M).toD39RootedMap.core.rot d} := by
      ext e
      constructor
      · rintro ⟨e₀, he₀, rfl⟩
        simpa [mirrorRootedLocallyFiniteMap] using he₀
      · intro he
        refine ⟨ι e, ?_, ?_⟩
        · simpa [mirrorRootedLocallyFiniteMap] using he
        · simp [toMirror, Equiv.apply_symm_apply]
    have hrot := prop59_mirrorRepresentation_rotation_field M.toD39RootedMap B x
      (ι d)
    have hmap := d39TopologicalCcwSuccessor_map_equiv toMirror hrot
    have hleft : toMirror (ι d) = d := by
      exact Equiv.apply_symm_apply (prop59_mirrorDartCarrierEquiv M) d
    have hright : toMirror (M.rot.symm (ι d)) =
        (mirrorRootedLocallyFiniteMap M).toD39RootedMap.core.rot d := rfl
    rw [hstar, hleft, hright] at hmap
    simpa only [toMirror, Equiv.symm_symm] using hmap
  · intro d v
    change (B.map.geomMirror.toPlaneMapWithMissing.pos
        ((prop59_mirrorRotationVertexEquiv M.rot).symm.trans x.vertexEquiv v)) ∈
      frontier ((B.map.geomMirrorEquiv.faceMap
        (x.faceOfDart (M.edgeInv d))).val) ↔
      ∃ e, Equiv.Perm.SameCycle (M.rot * M.edgeInv) d e ∧
        rootedLocallyFiniteVertexClass M.rot.symm e = v
    exact prop59_mirrorRepresentation_frontier_field M B x d v -/

end DirectedDistances.PaperProofs.Section5

end
