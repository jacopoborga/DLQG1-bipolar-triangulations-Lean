/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59RootAbsentAE
public import DirectedDistances.PaperProofs.Section5.Prop59CanonicalMirrorCompat6

/-! Helpers toward Proposition 5.9 (`prop-uihbot-sym`). This file records the
reflection fields that follow directly from the geometric and combinatorial
mirror conventions. It does not close OPEN 1 or claim paper completion. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.9. Reversing a finite-map rotation does not
change its rotation-orbit vertex carrier; this equivalence is the identity on
dart representatives. -/
@[expose] def prop59_mirrorRotationVertexEquiv {D : Type}
    (rot : Equiv.Perm D) :
    RootedLocallyFiniteVertex D rot ≃ RootedLocallyFiniteVertex D rot.symm where
  toFun := Quotient.map id (fun _ _ h => Equiv.Perm.sameCycle_inv.mpr h)
  invFun := Quotient.map id (fun _ _ h => Equiv.Perm.sameCycle_inv.mp h)
  left_inv := by
    intro v
    induction v using Quotient.inductionOn
    rfl
  right_inv := by
    intro v
    induction v using Quotient.inductionOn
    rfl

/-- Helper toward Proposition 5.9. The mirrored local topology root dart is the edge
inverse of the original missing frame dart, matching reversal of the
geometric root endpoint bit. -/
theorem prop59_mirrorRepresentation_rootMark
    (M : RootedLocallyFiniteMap)
    (B : DirectedDistances.PaperProofs.SourceResults.D39DomainRootedMapV2)
    (x : D39DrawingRepresentationData3 M.toD39RootedMap B) :
    x.dartEquiv
        ((mirrorRootedLocallyFiniteMap M).toD39RootedMap.rootMark.dart) =
      d39GeomMirrorRoot B.root := by
  have hroot :
      (mirrorRootedLocallyFiniteMap M).toD39RootedMap.rootMark.dart =
        M.toD39RootedMap.core.edgeInv M.toD39RootedMap.rootMark.dart := rfl
  rw [hroot, x.dart_edgeInv, x.root_mark]
  rfl

/-- Helper toward Proposition 5.9. The represented reversal of each dart is
unchanged by the combinatorial mirror and still records the same geometric
edge with the opposite endpoint bit. -/
theorem prop59_mirrorRepresentation_dart_edgeInv
    (M : RootedLocallyFiniteMap)
    (B : DirectedDistances.PaperProofs.SourceResults.D39DomainRootedMapV2)
    (x : D39DrawingRepresentationData3 M.toD39RootedMap B)
    (d : M.toD39RootedMap.core.D) :
    x.dartEquiv
        ((mirrorRootedLocallyFiniteMap M).toD39RootedMap.core.edgeInv d) =
      ((x.dartEquiv d).1, !(x.dartEquiv d).2) := by
  change x.dartEquiv (M.toD39RootedMap.core.edgeInv d) = _
  exact x.dart_edgeInv d

/-- Helper toward Proposition 5.9. The representation dart endpoints remain
the same geometric edge endpoints under reflection, while rotation-orbit
vertices are identified through `prop59_mirrorRotationVertexEquiv`. -/
theorem prop59_mirrorRepresentation_dart_endpoints
    (M : RootedLocallyFiniteMap)
    (B : DirectedDistances.PaperProofs.SourceResults.D39DomainRootedMapV2)
    (x : D39DrawingRepresentationData3 M.toD39RootedMap B)
    (d : M.toD39RootedMap.core.D) :
    (prop59_mirrorRotationVertexEquiv M.toD39RootedMap.core.rot).symm.trans
        x.vertexEquiv
        (rootedLocallyFiniteVertexClass M.toD39RootedMap.core.rot.symm d) =
      if (x.dartEquiv d).2 then
        B.map.geomMirror.toPlaneMapWithMissing.src (x.dartEquiv d).1
      else
        B.map.geomMirror.toPlaneMapWithMissing.tgt (x.dartEquiv d).1 := by
  have hclass :
      (prop59_mirrorRotationVertexEquiv M.toD39RootedMap.core.rot).symm
          (rootedLocallyFiniteVertexClass M.toD39RootedMap.core.rot.symm d) =
        rootedLocallyFiniteVertexClass M.toD39RootedMap.core.rot d := rfl
  change x.vertexEquiv
      ((prop59_mirrorRotationVertexEquiv M.toD39RootedMap.core.rot).symm
        (rootedLocallyFiniteVertexClass M.toD39RootedMap.core.rot.symm d)) = _
  rw [hclass, x.dart_tail_vertex]
  cases hbit : (x.dartEquiv d).2 <;>
    simp [DirectedPlaneMapWithMissing.geomMirror,
      PlaneGraphDrawing.geomMirror]

/-- Helper toward Proposition 5.9. The represented head endpoint is
preserved by reflection after identifying the mirrored rotation-orbit
vertices with the original ones. -/
theorem prop59_mirrorRepresentation_dart_headEndpoint
    (M : RootedLocallyFiniteMap)
    (B : DirectedDistances.PaperProofs.SourceResults.D39DomainRootedMapV2)
    (x : D39DrawingRepresentationData3 M.toD39RootedMap B)
    (d : M.toD39RootedMap.core.D) :
    (prop59_mirrorRotationVertexEquiv M.toD39RootedMap.core.rot).symm.trans
        x.vertexEquiv
        (rootedLocallyFiniteVertexClass M.toD39RootedMap.core.rot.symm
          (M.toD39RootedMap.core.edgeInv d)) =
      if (x.dartEquiv d).2 then
        B.map.geomMirror.toPlaneMapWithMissing.tgt (x.dartEquiv d).1
      else
        B.map.geomMirror.toPlaneMapWithMissing.src (x.dartEquiv d).1 := by
  have hclass :
      (prop59_mirrorRotationVertexEquiv M.toD39RootedMap.core.rot).symm
          (rootedLocallyFiniteVertexClass M.toD39RootedMap.core.rot.symm
            (M.toD39RootedMap.core.edgeInv d)) =
        rootedLocallyFiniteVertexClass M.toD39RootedMap.core.rot
          (M.toD39RootedMap.core.edgeInv d) := rfl
  change x.vertexEquiv
      ((prop59_mirrorRotationVertexEquiv M.toD39RootedMap.core.rot).symm
        (rootedLocallyFiniteVertexClass M.toD39RootedMap.core.rot.symm
          (M.toD39RootedMap.core.edgeInv d))) = _
  rw [hclass, x.dart_head_vertex]
  cases hbit : (x.dartEquiv d).2 <;>
    simp [DirectedPlaneMapWithMissing.geomMirror,
      PlaneGraphDrawing.geomMirror]

/-- Helper toward Proposition 5.9. The face permutation of the mirrored map
has the same cycles as the original face permutation after applying the edge
inverse to dart representatives. -/
theorem prop59_mirrorFaceCycle (M : RootedLocallyFiniteMap) (a b : M.D) :
    Equiv.Perm.SameCycle (M.rot * M.edgeInv) (M.edgeInv a) (M.edgeInv b) ↔
      Equiv.Perm.SameCycle (M.rot.symm * M.edgeInv) a b := by
  have hi : M.edgeInv⁻¹ = M.edgeInv := by
    ext d
    apply M.edgeInv.injective
    change M.edgeInv (M.edgeInv.symm d) = M.edgeInv (M.edgeInv d)
    rw [M.edgeInv.apply_symm_apply, M.edgeInv_invol]
  have hf : M.rot * M.edgeInv =
      M.edgeInv * (M.rot.symm * M.edgeInv)⁻¹ * M.edgeInv⁻¹ := by
    rw [mul_inv_rev, hi, Equiv.Perm.inv_def, Equiv.symm_symm]
    have he : M.edgeInv * M.edgeInv = 1 := by
      ext d
      exact M.edgeInv_invol d
    rw [← mul_assoc, he, one_mul]
  rw [hf, Equiv.Perm.sameCycle_conj, hi]
  simpa only [M.edgeInv_invol] using
    (Equiv.Perm.sameCycle_inv (f := M.rot.symm * M.edgeInv)
      (x := a) (y := b))

/-- Helper toward Proposition 5.9. Reflection preserves each represented
edge identity, its missing tag, and every present-edge orientation; the
combinatorial mirror reverses rotation but keeps its tail predicate. -/
theorem prop59_mirrorRepresentation_edge_fields
    (M : RootedLocallyFiniteMap)
    (B : DirectedDistances.PaperProofs.SourceResults.D39DomainRootedMapV2)
    (x : D39DrawingRepresentationData3 M.toD39RootedMap B)
    (d : M.toD39RootedMap.core.D) :
    (B.map.geomMirror.toPlaneMapWithMissing.missing (x.dartEquiv d).1 ↔
        (mirrorRootedLocallyFiniteMap M).toD39RootedMap.core.missing d) ∧
      (∀ hdB : ¬ B.map.geomMirror.toPlaneMapWithMissing.missing
          (x.dartEquiv d).1,
        ((mirrorRootedLocallyFiniteMap M).toD39RootedMap.core.tail d ↔
          B.map.geomMirror.forward
            ⟨(x.dartEquiv d).1, hdB⟩ = (x.dartEquiv d).2)) := by
  constructor
  · simpa [DirectedPlaneMapWithMissing.geomMirror,
      RootedLocallyFiniteMap.toD39RootedMap, mirrorRootedLocallyFiniteMap] using
      (x.dart_missing d)
  · intro hdB
    have hdBase : ¬ B.map.toPlaneMapWithMissing.missing (x.dartEquiv d).1 := by
      simpa [DirectedPlaneMapWithMissing.geomMirror] using hdB
    have hd : ¬ M.toD39RootedMap.core.missing d :=
      (x.dart_missing d).not.mp hdBase
    have hdB' : hdB = (x.dart_missing d).not.mpr hd := by
      apply Subsingleton.elim
    subst hdB'
    simpa [DirectedPlaneMapWithMissing.geomMirror,
      RootedLocallyFiniteMap.toD39RootedMap, mirrorRootedLocallyFiniteMap] using
      (x.dart_orientation d hd)





































































end DirectedDistances.PaperProofs.Section5

end
