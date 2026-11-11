module

public import DirectedDistances.PlanarMap.FacedFramedBall
public import DirectedDistances.PlanarMap.MirrorMap

public section
namespace DirectedDistances.PlanarMap

open Equiv CombinatorialMap

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv);
not a paper result. The reflected root convention retains this carrier's root
vertex and missing frame edge. This is not the finite directed-dart reversal. -/
@[expose] def mirrorFacedFramedBall (B : FacedFramedBall) : FacedFramedBall where
  toFramedBall := {
    D := B.toFramedBall.D
    map := B.toFramedBall.map.mirror
    rootDart := B.toFramedBall.rootDart
    frameEdgeDart := B.toFramedBall.frameEdgeDart
    frameEdge_missing := by
      simpa [DirectedMapWithMissing.mirror] using B.toFramedBall.frameEdge_missing
    frameEdge_at_root := by
      change Equiv.Perm.SameCycle (B.toFramedBall.map.rot.symm)
        B.toFramedBall.rootDart B.toFramedBall.frameEdgeDart
      exact Equiv.Perm.sameCycle_inv.mpr B.toFramedBall.frameEdge_at_root
    frameOtherDart := B.toFramedBall.frameOtherDart
    frameOtherDart_valid := by
      intro y hy
      change Equiv.Perm.SameCycle (B.toFramedBall.map.rot.symm)
        (B.toFramedBall.map.edgeInv B.toFramedBall.frameEdgeDart) y
      exact Equiv.Perm.sameCycle_inv.mpr (B.toFramedBall.frameOtherDart_valid y hy)
  }
  original := {d | B.toFramedBall.map.edgeInv d ∈ B.original}
  original_closed := by
    intro d
    let M := B.toFramedBall.map.toCombinatorialMap
    change M.edgeInv (M.mirror.faceSucc d) ∈ B.original ↔
      M.edgeInv d ∈ B.original
    have hface : M.edgeInv (M.mirror.faceSucc d) =
        M.faceSucc.symm (M.edgeInv d) := by
      rw [CombinatorialMap.mirror_faceSucc]
      simp [Equiv.Perm.mul_apply, M.edgeInv_invol]
    rw [hface]
    simpa [M] using (B.original_closed (M.faceSucc.symm (M.edgeInv d))).symm

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv);
not a paper result. The reversed finite root dart is not represented by this
carrier's root vertex mark; this is the unclosed compatibility condition. -/
def mirrorFacedFramedBall_rootPairConvention (B : FacedFramedBall) : Prop :=
  (mirrorFacedFramedBall B).toFramedBall.rootDart =
    B.toFramedBall.map.edgeInv B.toFramedBall.rootDart

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv);
not a paper result. Reflection sends orientation-preserving isomorphisms to
orientation-preserving isomorphisms, including the retained root vertex and
reflected original-face selection. Source: -/
@[expose] def FacedFramedBallIso.mirror {B C : FacedFramedBall}
    (I : FacedFramedBallIso B C) :
    FacedFramedBallIso (mirrorFacedFramedBall B) (mirrorFacedFramedBall C) := by
  unfold mirrorFacedFramedBall
  refine {
    toFramedBallIso := {
      mapIso := {
        toEquiv := I.toFramedBallIso.mapIso.toEquiv
        rot_comm := by
          intro d
          change I.toFramedBallIso.mapIso.toEquiv
              (B.toFramedBall.map.rot.symm d) =
            C.toFramedBall.map.rot.symm
              (I.toFramedBallIso.mapIso.toEquiv d)
          apply C.toFramedBall.map.rot.injective
          rw [← I.toFramedBallIso.mapIso.rot_comm,
            B.toFramedBall.map.rot.apply_symm_apply,
            C.toFramedBall.map.rot.apply_symm_apply]
        edgeInv_comm := I.toFramedBallIso.mapIso.edgeInv_comm
        missing_iff := I.toFramedBallIso.mapIso.missing_iff
        tail_iff := I.toFramedBallIso.mapIso.tail_iff
        outer_iff := by
          intro d
          change C.toFramedBall.map.mirror.IsOuter
              (I.toFramedBallIso.mapIso.toEquiv d) ↔
            B.toFramedBall.map.mirror.IsOuter d
          rw [DirectedMapWithMissing.mirror_isOuter_iff,
            DirectedMapWithMissing.mirror_isOuter_iff,
            ← I.toFramedBallIso.mapIso.edgeInv_comm]
          exact I.toFramedBallIso.mapIso.outer_iff
            (B.toFramedBall.map.edgeInv d)
      }
      root_vertex := by
        change Equiv.Perm.SameCycle (C.toFramedBall.map.rot.symm)
          (I.toFramedBallIso.mapIso.toEquiv B.toFramedBall.rootDart)
          C.toFramedBall.rootDart
        exact Equiv.Perm.sameCycle_inv.mpr I.toFramedBallIso.root_vertex
      frameEdge_comm := I.toFramedBallIso.frameEdge_comm
      frameOther_comm := by
        rcases I.toFramedBallIso.frameOther_comm with h | h
        · exact Or.inl h
        · rcases h with ⟨x, y, hx, hy, hxy⟩
          exact Or.inr ⟨x, y, hx, hy, Equiv.Perm.sameCycle_inv.mpr hxy⟩
    }
    original_iff := by
      intro d
      change C.toFramedBall.map.edgeInv
          (I.toFramedBallIso.mapIso.toEquiv d) ∈ C.original ↔
        B.toFramedBall.map.edgeInv d ∈ B.original
      rw [← I.toFramedBallIso.mapIso.edgeInv_comm]
      exact I.original_iff (B.toFramedBall.map.edgeInv d)
  }

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv);
not a paper result. Isomorphic faced balls have isomorphic reflected faced -/
theorem mirrorFacedFramedBall_iso {B C : FacedFramedBall}
    (I : FacedFramedBallIso B C) :
    Nonempty (FacedFramedBallIso (mirrorFacedFramedBall B)
      (mirrorFacedFramedBall C)) := ⟨I.mirror⟩

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv);
not a paper result. Identity transport preserves an optional frame mark. -/
private theorem optionFrameOther_refl {D : Type} (rot : Equiv.Perm D)
    (o : Option D) :
    (o.map id = none ∧ o = none) ∨
      (∃ x y, o.map id = some x ∧ o = some y ∧
        Equiv.Perm.SameCycle rot x y) := by
  cases o with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some d => exact Or.inr ⟨d, d, rfl, rfl, Equiv.Perm.SameCycle.rfl⟩

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv);
not a paper result. The mirror action on the orientation-preserving faced-ball -/
@[expose] def mirrorFacedBallClass : FacedFramedBallClass → FacedFramedBallClass :=
  Quotient.map mirrorFacedFramedBall (by
    intro B C h
    rcases h with ⟨I⟩
    exact mirrorFacedFramedBall_iso I)

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv);
not a paper result. The reflected faced-ball class is involutive. Source: -/
theorem mirrorFacedBallClass_involutive (q : FacedFramedBallClass) :
    mirrorFacedBallClass (mirrorFacedBallClass q) = q := by
  refine Quotient.inductionOn q ?_
  intro B
  apply Quotient.sound
  unfold mirrorFacedFramedBall
  refine ⟨{
    toFramedBallIso := {
      mapIso := {
        toEquiv := Equiv.refl _
        rot_comm := by intro d; rfl
        edgeInv_comm := by intro d; rfl
        missing_iff := by intro d; rfl
        tail_iff := by intro d; rfl
        outer_iff := by
          intro d
          have h := congrArg
            (fun X : DirectedMapWithMissing B.toFramedBall.D => X.IsOuter d)
            (DirectedMapWithMissing.mirror_mirror B.toFramedBall.map)
          simpa using (Iff.of_eq h).symm
      }
      root_vertex := Equiv.Perm.SameCycle.rfl
      frameEdge_comm := rfl
      frameOther_comm := by
        change (B.toFramedBall.frameOtherDart.map id = none ∧
          B.toFramedBall.frameOtherDart = none) ∨
          (∃ x y, B.toFramedBall.frameOtherDart.map id = some x ∧
            B.toFramedBall.frameOtherDart = some y ∧
            Equiv.Perm.SameCycle B.toFramedBall.map.rot x y)
        exact optionFrameOther_refl B.toFramedBall.map.rot
          B.toFramedBall.frameOtherDart
    }
    original_iff := by
      intro d
      change d ∈ B.original ↔
        B.toFramedBall.map.edgeInv
          (B.toFramedBall.map.mirror.edgeInv d) ∈ B.original
      rw [show B.toFramedBall.map.mirror.edgeInv d =
        B.toFramedBall.map.edgeInv d by rfl,
        B.toFramedBall.map.edgeInv_invol]
  }⟩

end DirectedDistances.PlanarMap
