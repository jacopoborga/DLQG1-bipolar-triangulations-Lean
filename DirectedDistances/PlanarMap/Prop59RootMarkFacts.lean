module

public import DirectedDistances.PlanarMap.RootedLocallyFiniteMirrorShifted

/-! Supporting lemmas for paper labels `prop-uihbot-sym` (see CORRESPONDENCE.md). -/

 

public section
namespace DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.9 (prop-uihbot-sym, author ruling Q-59-root option B);
not a paper result.
Convention-level facts only, NOT Proposition 5.9. Still needs the finite boundary-reversal
law with exact mark compatibility (I1 kept as printed), extension from the lower carrier to
the planar carrier, boundary and function transport including reconciliation with the printed
`edgeInv M.outer`; present-edge direction preservation is only via tail equality and is not
separately stated here.
Proves the identity on darts transporting rotation-class sameness from `rot` to `rot.symm`. -/
@[expose] def prop59_rootedVertexMirrorEquiv {D : Type} (rot : Equiv.Perm D) :
    RootedLocallyFiniteVertex D rot ≃
      RootedLocallyFiniteVertex D rot.symm where
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

/-- Helper toward Proposition 5.9 (prop-uihbot-sym, author ruling Q-59-root option B);
not a paper result.
Convention-level facts only, NOT Proposition 5.9. Still needs the finite boundary-reversal
law with exact mark compatibility (I1 kept as printed), extension from the lower carrier to
the planar carrier, boundary and function transport including reconciliation with the printed
`edgeInv M.outer`; present-edge direction preservation is only via tail equality and is not
separately stated here.
Proves that the mirrored root dart is M.edgeInv M.frameEdgeDart. -/
@[simp] theorem mirrorRootedLocallyFiniteMap_rootDart_eq
    (M : RootedLocallyFiniteMap) :
    (mirrorRootedLocallyFiniteMap M).rootDart = M.edgeInv M.frameEdgeDart := rfl

/-- Helper toward Proposition 5.9 (prop-uihbot-sym, author ruling Q-59-root option B);
not a paper result.
Convention-level facts only, NOT Proposition 5.9. Still needs the finite boundary-reversal
law with exact mark compatibility (I1 kept as printed), extension from the lower carrier to
the planar carrier, boundary and function transport including reconciliation with the printed
`edgeInv M.outer`; present-edge direction preservation is only via tail equality and is not
separately stated here.
Proves that the mirrored frame-edge dart is M.edgeInv M.frameEdgeDart. -/
@[simp] theorem mirrorRootedLocallyFiniteMap_frameEdgeDart_eq
    (M : RootedLocallyFiniteMap) :
    (mirrorRootedLocallyFiniteMap M).frameEdgeDart = M.edgeInv M.frameEdgeDart := rfl

/-- Helper toward Proposition 5.9 (prop-uihbot-sym, author ruling Q-59-root option B);
not a paper result.
Convention-level facts only, NOT Proposition 5.9. Still needs the finite boundary-reversal
law with exact mark compatibility (I1 kept as printed), extension from the lower carrier to
the planar carrier, boundary and function transport including reconciliation with the printed
`edgeInv M.outer`; present-edge direction preservation is only via tail equality and is not
separately stated here.
Proves the mirrored other-frame dart equals M.frameOtherDart with M.frameEdgeDart substituted. -/
@[simp] theorem mirrorRootedLocallyFiniteMap_frameOtherDart_eq
    (M : RootedLocallyFiniteMap) :
    (mirrorRootedLocallyFiniteMap M).frameOtherDart =
      M.frameOtherDart.map (fun _ => M.frameEdgeDart) := rfl

/-- Helper toward Proposition 5.9 (prop-uihbot-sym, author ruling Q-59-root option B);
not a paper result.
Convention-level facts only, NOT Proposition 5.9. Still needs the finite boundary-reversal
law with exact mark compatibility (I1 kept as printed), extension from the lower carrier to
the planar carrier, boundary and function transport including reconciliation with the printed
`edgeInv M.outer`; present-edge direction preservation is only via tail equality and is not
separately stated here.
Proves the mirror root and frame-edge darts use the edge inverse, with the stated other-frame map. -/
theorem mirrorRootedLocallyFiniteMap_rootMark_swap (M : RootedLocallyFiniteMap) :
    (mirrorRootedLocallyFiniteMap M).rootDart =
      M.edgeInv M.frameEdgeDart ∧
    (mirrorRootedLocallyFiniteMap M).frameEdgeDart =
      M.edgeInv M.frameEdgeDart ∧
    (mirrorRootedLocallyFiniteMap M).frameOtherDart =
      M.frameOtherDart.map (fun _ => M.frameEdgeDart) := by
  exact ⟨mirrorRootedLocallyFiniteMap_rootDart_eq M,
    mirrorRootedLocallyFiniteMap_frameEdgeDart_eq M,
    mirrorRootedLocallyFiniteMap_frameOtherDart_eq M⟩

/-- Helper toward Proposition 5.9 (prop-uihbot-sym, author ruling Q-59-root option B);
not a paper result.
Convention-level facts only, NOT Proposition 5.9. Still needs the finite boundary-reversal
law with exact mark compatibility (I1 kept as printed), extension from the lower carrier to
the planar carrier, boundary and function transport including reconciliation with the printed
`edgeInv M.outer`; present-edge direction preservation is only via tail equality and is not
separately stated here.
Proves the mirrored frame dart and its edge-inverse identify the same geometric edge. -/
@[simp] theorem prop59_mirrorFrameEdge_sameGeometricEdge
    (M : RootedLocallyFiniteMap) :
    (mirrorRootedLocallyFiniteMap M).frameEdgeDart =
      M.edgeInv M.frameEdgeDart ∧
    M.edgeInv (mirrorRootedLocallyFiniteMap M).frameEdgeDart = M.frameEdgeDart := by
  exact ⟨rfl, M.edgeInv_invol _⟩

/-- Helper toward Proposition 5.9 (prop-uihbot-sym, author ruling Q-59-root option B);
not a paper result.
Convention-level facts only, NOT Proposition 5.9. Still needs the finite boundary-reversal
law with exact mark compatibility (I1 kept as printed), extension from the lower carrier to
the planar carrier, boundary and function transport including reconciliation with the printed
`edgeInv M.outer`; present-edge direction preservation is only via tail equality and is not
separately stated here.
Proves the mirrored root vertex corresponds to the original other frame vertex. -/
@[simp] theorem prop59_mirrorRootVertex_is_originalOtherFrameVertex
    (M : RootedLocallyFiniteMap) :
    prop59_rootedVertexMirrorEquiv M.rot
        (rootedLocallyFiniteVertexClass M.rot (M.edgeInv M.frameEdgeDart)) =
      rootedLocallyFiniteVertexClass (mirrorRootedLocallyFiniteMap M).rot
        (mirrorRootedLocallyFiniteMap M).rootDart := rfl

/-- Helper toward Proposition 5.9 (prop-uihbot-sym, author ruling Q-59-root option B);
not a paper result.
Convention-level facts only, NOT Proposition 5.9. Still needs the finite boundary-reversal
law with exact mark compatibility (I1 kept as printed), extension from the lower carrier to
the planar carrier, boundary and function transport including reconciliation with the printed
`edgeInv M.outer`; present-edge direction preservation is only via tail equality and is not
separately stated here.
Proves the mirrored other frame vertex corresponds to the original root vertex. -/
@[simp] theorem prop59_mirrorOtherFrameVertex_is_originalRootVertex
    (M : RootedLocallyFiniteMap) :
    prop59_rootedVertexMirrorEquiv M.rot
        (rootedLocallyFiniteVertexClass M.rot M.rootDart) =
      rootedLocallyFiniteVertexClass (mirrorRootedLocallyFiniteMap M).rot
        ((mirrorRootedLocallyFiniteMap M).edgeInv
          (mirrorRootedLocallyFiniteMap M).frameEdgeDart) := by
  rw [mirrorRootedLocallyFiniteMap_frameEdgeDart_eq, M.edgeInv_invol]
  apply Quotient.sound
  exact Equiv.Perm.sameCycle_inv.mpr M.frameEdge_at_root

/-- Helper toward Proposition 5.9 (prop-uihbot-sym, author ruling Q-59-root option B);
not a paper result.
Convention-level facts only, NOT Proposition 5.9. Still needs the finite boundary-reversal
law with exact mark compatibility (I1 kept as printed), extension from the lower carrier to
the planar carrier, boundary and function transport including reconciliation with the printed
`edgeInv M.outer`; present-edge direction preservation is only via tail equality and is not
separately stated here.
Proves the root and other-frame vertices swap under the mirror vertex equivalence. -/
theorem prop59_mirrorRootEndpoints_swap (M : RootedLocallyFiniteMap) :
    prop59_rootedVertexMirrorEquiv M.rot
        (rootedLocallyFiniteVertexClass M.rot (M.edgeInv M.frameEdgeDart)) =
      rootedLocallyFiniteVertexClass (mirrorRootedLocallyFiniteMap M).rot
        (mirrorRootedLocallyFiniteMap M).rootDart ∧
    prop59_rootedVertexMirrorEquiv M.rot
        (rootedLocallyFiniteVertexClass M.rot M.rootDart) =
      rootedLocallyFiniteVertexClass (mirrorRootedLocallyFiniteMap M).rot
        ((mirrorRootedLocallyFiniteMap M).edgeInv
          (mirrorRootedLocallyFiniteMap M).frameEdgeDart) := by
  exact ⟨prop59_mirrorRootVertex_is_originalOtherFrameVertex M,
    prop59_mirrorOtherFrameVertex_is_originalRootVertex M⟩

/-- Helper toward Proposition 5.9 (prop-uihbot-sym, author ruling Q-59-root option B);
not a paper result.
Convention-level facts only, NOT Proposition 5.9. Still needs the finite boundary-reversal
law with exact mark compatibility (I1 kept as printed), extension from the lower carrier to
the planar carrier, boundary and function transport including reconciliation with the printed
`edgeInv M.outer`; present-edge direction preservation is only via tail equality and is not
separately stated here.
Proves that a dart is missing in the mirror exactly when it is missing in M. -/
@[simp] theorem mirrorRootedLocallyFiniteMap_missing_iff (M : RootedLocallyFiniteMap)
    (d : M.D) :
    (mirrorRootedLocallyFiniteMap M).missing d ↔
      M.missing d := Iff.rfl

/-- Helper toward Proposition 5.9 (prop-uihbot-sym, author ruling Q-59-root option B);
not a paper result.
Convention-level facts only, NOT Proposition 5.9. Still needs the finite boundary-reversal
law with exact mark compatibility (I1 kept as printed), extension from the lower carrier to
the planar carrier, boundary and function transport including reconciliation with the printed
`edgeInv M.outer`; present-edge direction preservation is only via tail equality and is not
separately stated here.
Proves that a dart has a tail in the mirror exactly when it has a tail in M. -/
@[simp] theorem mirrorRootedLocallyFiniteMap_tail_iff (M : RootedLocallyFiniteMap)
    (d : M.D) :
    (mirrorRootedLocallyFiniteMap M).tail d ↔
      M.tail d := Iff.rfl

/-- Helper toward Proposition 5.9 (prop-uihbot-sym, author ruling Q-59-root option B);
not a paper result.
Convention-level facts only, NOT Proposition 5.9. Still needs the finite boundary-reversal
law with exact mark compatibility (I1 kept as printed), extension from the lower carrier to
the planar carrier, boundary and function transport including reconciliation with the printed
`edgeInv M.outer`; present-edge direction preservation is only via tail equality and is not
separately stated here.
Proves that applying the mirror twice yields normalizeRootedLocallyFiniteFrame M, not literally M. -/
theorem prop59_mirrorRootedLocallyFiniteMap_involutive (M : RootedLocallyFiniteMap) :
    mirrorRootedLocallyFiniteMap (mirrorRootedLocallyFiniteMap M) =
      normalizeRootedLocallyFiniteFrame M :=
  mirrorRootedLocallyFiniteMap_involutive M

end DirectedDistances.PlanarMap
