/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59MirrorCompat12

/-! Reflection of the underlying drawing representation preserves individual edges,
missing tags and present-edge orientations, reverses the ordered root and
rotation, and conjugates the face on the opposite side of each original dart. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open scoped ComplexConjugate

/-- Helper toward Proposition 5.9. Assemble every underlying drawing field
of the reflected representation, including the reflected face-side convention.
The geometric domain is exactly the supplied reflected domain. -/
@[expose] def prop59_mirrorRep_base
    (M : RootedLocallyFiniteMap) (B : D39DomainRootedMapV2)
    (x : D39DrawingRepresentationData3 M.toD39RootedMap B)
    (hmirrorDomain : D39GeomDomain B.map.geomMirror (d39GeomMirrorRoot B.root)) :
    D39DrawingRepresentationData (mirrorRootedLocallyFiniteMap M).toD39RootedMap
      ⟨B.V, B.E, B.map.geomMirror, d39GeomMirrorRoot B.root, hmirrorDomain⟩ := by
  let V := prop59_mirrorRotationVertexEquiv M.toD39RootedMap.core.rot
  exact {
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

/-- Helper toward Proposition 5.9. Each dart arc in the reflected
representation is the pointwise complex conjugate of its original dart arc. -/
theorem prop59_mirrorRep_dartArc
    (M : RootedLocallyFiniteMap) (B : D39DomainRootedMapV2)
    (x : D39DrawingRepresentationData3 M.toD39RootedMap B)
    (hmirrorDomain : D39GeomDomain B.map.geomMirror (d39GeomMirrorRoot B.root))
    (d : M.D) (t : unitInterval) :
    d39DrawingDartArc
        ⟨B.V, B.E, B.map.geomMirror, d39GeomMirrorRoot B.root, hmirrorDomain⟩
        (prop59_mirrorRep_base M B x hmirrorDomain) d t =
      conj (d39DrawingDartArc B x.toD39DrawingRepresentationData d t) := by
  change (if (x.dartEquiv d).2 then
      (fun s => conj (B.map.arc (x.dartEquiv d).1 s))
    else (fun s => conj ((B.map.arc (x.dartEquiv d).1).symm s))) t =
      conj ((if (x.dartEquiv d).2 then
        ⇑(B.map.arc (x.dartEquiv d).1)
      else ⇑(B.map.arc (x.dartEquiv d).1).symm) t)
  cases hb : (x.dartEquiv d).2 <;> rfl

/-- Helper toward Proposition 5.9. Reflect every field of a v3 drawing
representation: positions and arcs are conjugated, the rotation is inverted,
faces are reflected after edge inversion, and the ordered root is reversed.
Present-edge orientations and missing-edge identities are preserved. -/
@[expose] def prop59_mirrorRep_data3
    (M : RootedLocallyFiniteMap) (B : D39DomainRootedMapV2)
    (x : D39DrawingRepresentationData3 M.toD39RootedMap B)
    (hmirrorDomain : D39GeomDomain B.map.geomMirror (d39GeomMirrorRoot B.root)) :
    D39DrawingRepresentationData3 (mirrorRootedLocallyFiniteMap M).toD39RootedMap
      ⟨B.V, B.E, B.map.geomMirror, d39GeomMirrorRoot B.root, hmirrorDomain⟩ := by
  refine {
    toD39DrawingRepresentationData := prop59_mirrorRep_base M B x hmirrorDomain
    rotation_topological_successor := ?_
    vertex_frontier_incidence := ?_
  }
  · intro d
    have harc : d39DrawingDartArc
        ⟨B.V, B.E, B.map.geomMirror, d39GeomMirrorRoot B.root, hmirrorDomain⟩
        (prop59_mirrorRep_base M B x hmirrorDomain) =
        (fun (e : M.D) t => conj
          (d39DrawingDartArc B x.toD39DrawingRepresentationData e t)) := by
      funext e t
      exact prop59_mirrorRep_dartArc M B x hmirrorDomain e t
    rw [harc]
    exact prop59_mirrorRepresentation_rotation_field M.toD39RootedMap B x d
  · intro d v
    change (B.map.geomMirror.toPlaneMapWithMissing.pos
        ((prop59_mirrorRotationVertexEquiv M.rot).symm.trans x.vertexEquiv v)) ∈
      frontier ((B.map.geomMirrorEquiv.faceMap
        (x.faceOfDart (M.edgeInv d))).val) ↔
      ∃ e, Equiv.Perm.SameCycle (M.rot * M.edgeInv) d e ∧
        rootedLocallyFiniteVertexClass M.rot.symm e = v
    exact prop59_mirrorRepresentation_frontier_field M B x d v

end DirectedDistances.PaperProofs.Section5

end
