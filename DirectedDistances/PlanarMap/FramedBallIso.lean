/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.DirectedMapIso

public section
namespace DirectedDistances.PlanarMap

open Equiv
open CombinatorialMap

/-! proposes all-geometric distance, a tagged induced ball, and an ordered missing
root mark. No reading is adopted here, and this helper carrier is not a paper
result. The map retains present/missing tags and the outer face; the frame
records the missing root edge and its order, without a separate corner choice. -/

/-- uses all-geometric distance, a tagged induced ball, and an ordered missing root
mark. No reading is adopted here; this helper carrier is not a paper result.
The map retains present/missing tags and the outer face. -/
structure FramedBall where
  D : Type
  [instFintypeD : Fintype D]
  [instDecidableEqD : DecidableEq D]
  map : DirectedMapWithMissing D
  rootDart : D
  frameEdgeDart : D
  frameEdge_missing : map.missing frameEdgeDart
  frameEdge_at_root : map.rot.SameCycle rootDart frameEdgeDart
  frameOtherDart : Option D
  frameOtherDart_valid : ∀ y, frameOtherDart = some y →
    map.rot.SameCycle (map.edgeInv frameEdgeDart) y

instance (M : FramedBall) : Fintype M.D := M.instFintypeD

instance (M : FramedBall) : DecidableEq M.D := M.instDecidableEqD

/-- isomorphism preserves tags and outer face; root and optional other-endpoint
markers are preserved up to vertex orbit, and the frame edge on the nose. No
reading is adopted here; this helper is not a paper result. -/
structure FramedBallIso (M N : FramedBall) where
  mapIso : DirectedMapWithMissingIso M.map N.map
  root_vertex : N.map.rot.SameCycle
    (mapIso.toEquiv M.rootDart) N.rootDart
  frameEdge_comm : mapIso.toEquiv M.frameEdgeDart = N.frameEdgeDart
  frameOther_comm :
    (M.frameOtherDart.map mapIso.toEquiv = none ∧ N.frameOtherDart = none) ∨
      (∃ x y, M.frameOtherDart.map mapIso.toEquiv = some x ∧
        N.frameOtherDart = some y ∧
        N.map.rot.SameCycle x y)

namespace FramedBallIso

variable {M N P : FramedBall}

/-- A dart isomorphism transports rotation-orbit vertex relation on the local topology
reading-R candidate carrier. No reading is adopted; this is not a paper result. -/
theorem vertexRel_map (I : DirectedMapWithMissingIso M.map N.map)
    {x y : M.D} (h : M.map.rot.SameCycle x y) :
    N.map.rot.SameCycle (I.toEquiv x) (I.toEquiv y) := by
  have hrot : N.map.rot = I.toEquiv.permCongr M.map.rot := by
    ext z
    simp only [Equiv.permCongr_apply]
    simpa using (I.rot_comm (I.toEquiv.symm z)).symm
  rcases h with ⟨i, hi⟩
  have hpow : I.toEquiv.permCongr (M.map.rot ^ i) =
      (I.toEquiv.permCongr M.map.rot) ^ i := by
    change I.toEquiv.permCongrHom (M.map.rot ^ i) = _
    exact map_zpow I.toEquiv.permCongrHom M.map.rot i
  refine ⟨i, ?_⟩
  calc
    (N.map.rot ^ i) (I.toEquiv x) =
        (I.toEquiv.permCongr M.map.rot ^ i) (I.toEquiv x) := by rw [hrot]
    _ = (I.toEquiv.permCongr (M.map.rot ^ i)) (I.toEquiv x) := by
      rw [← hpow]
    _ = I.toEquiv ((M.map.rot ^ i) x) := by simp
    _ = I.toEquiv y := congrArg I.toEquiv hi

/-- Identity isomorphism of local topology reading-R candidate carriers. No reading is
adopted; this helper is not a paper result. -/
@[expose] def refl (M : FramedBall) : FramedBallIso M M where
  mapIso := DirectedMapWithMissingIso.refl M.map
  root_vertex := Equiv.Perm.SameCycle.rfl
  frameEdge_comm := rfl
  frameOther_comm := by
    cases M.frameOtherDart with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some d => exact Or.inr ⟨d, d, rfl, rfl, Equiv.Perm.SameCycle.rfl⟩

/-- Inverse isomorphism of local topology reading-R candidate carriers. Root and optional
other-endpoint markers are compared up to vertex orbit. No reading is adopted;
this helper is not a paper result. -/
@[expose] def symm (I : FramedBallIso M N) : FramedBallIso N M where
  mapIso := DirectedMapWithMissingIso.symm I.mapIso
  root_vertex := by
    have h := vertexRel_map I.mapIso.symm I.root_vertex
    have hleft : I.mapIso.symm.toEquiv
        (I.mapIso.toEquiv M.rootDart) = M.rootDart := by
      simp [DirectedMapWithMissingIso.symm]
    rw [hleft] at h
    exact h.symm
  frameEdge_comm := by
    rw [← I.frameEdge_comm]
    exact Equiv.apply_symm_apply _ _
  frameOther_comm := by
    rcases I.frameOther_comm with hnone | ⟨x, y, hx, hy, hrel⟩
    · left
      constructor
      · simp [hnone.2]
      · cases hm : M.frameOtherDart with
        | none => rfl
        | some d => simp [hm] at hnone
    · right
      cases hm : M.frameOtherDart with
      | none => simp [hm] at hx
      | some m =>
        have hxm : I.mapIso.toEquiv m = x := by simpa [hm] using hx
        refine ⟨I.mapIso.symm.toEquiv y, m, ?_, rfl, ?_⟩
        · simp [hy, DirectedMapWithMissingIso.symm]
        · have h := vertexRel_map I.mapIso.symm hrel
          have hxm' : I.mapIso.symm.toEquiv x = m := by
            rw [← hxm]
            simp [DirectedMapWithMissingIso.symm]
          rw [hxm'] at h
          exact h.symm

/-- Composite isomorphism of local topology reading-R candidate carriers. Root and
optional other-endpoint markers are compared up to vertex orbit. No reading is
adopted; this helper is not a paper result. -/
@[expose] def trans (I : FramedBallIso M N) (J : FramedBallIso N P) :
    FramedBallIso M P where
  mapIso := DirectedMapWithMissingIso.trans I.mapIso J.mapIso
  root_vertex := by
    have h := vertexRel_map J.mapIso I.root_vertex
    exact h.trans J.root_vertex
  frameEdge_comm := by
    change J.mapIso.toEquiv (I.mapIso.toEquiv M.frameEdgeDart) = P.frameEdgeDart
    rw [I.frameEdge_comm, J.frameEdge_comm]
  frameOther_comm := by
    cases hm : M.frameOtherDart with
    | none =>
      have hn : N.frameOtherDart = none := by
        rcases I.frameOther_comm with hnone | ⟨x, y, hx, hy, hxy⟩
        · exact hnone.2
        · simp [hm] at hx
      have hp : P.frameOtherDart = none := by
        rcases J.frameOther_comm with hnone | ⟨x, y, hx, hy, hxy⟩
        · exact hnone.2
        · simp [hn] at hx
      left
      exact ⟨by simp, hp⟩
    | some a =>
      obtain ⟨b, hnb, hab⟩ : ∃ b, N.frameOtherDart = some b ∧
          N.map.rot.SameCycle (I.mapIso.toEquiv a) b := by
        rcases I.frameOther_comm with hnone | ⟨x, y, hx, hy, hxy⟩
        · simp [hm] at hnone
        · have hxa : I.mapIso.toEquiv a = x := by simpa [hm] using hx
          exact ⟨y, hy, hxa ▸ hxy⟩
      obtain ⟨c, hpc, hbc⟩ : ∃ c, P.frameOtherDart = some c ∧
          P.map.rot.SameCycle (J.mapIso.toEquiv b) c := by
        rcases J.frameOther_comm with hnone | ⟨x, y, hx, hy, hxy⟩
        · simp [hnb] at hnone
        · have hxb : J.mapIso.toEquiv b = x := by simpa [hnb] using hx
          exact ⟨y, hy, hxb ▸ hxy⟩
      right
      refine ⟨J.mapIso.toEquiv (I.mapIso.toEquiv a), c, ?_, hpc, ?_⟩
      · simp [DirectedMapWithMissingIso.trans]
      · have hmid := vertexRel_map J.mapIso hab
        simpa only [DirectedMapWithMissingIso.trans, Equiv.trans_apply] using
          hmid.trans hbc
end FramedBallIso

namespace FramedBall

/-- Isomorphism equivalence of local topology reading-R candidate carriers. Root and
optional other-endpoint markers are compared up to vertex orbit; the frame edge
is preserved on the nose. No reading is adopted; this helper is not a paper
result. -/
@[expose] def equiv (M N : FramedBall) : Prop := Nonempty (FramedBallIso M N)

/-- Isomorphism is an equivalence relation on local topology reading-R candidate carriers.
No reading is adopted; this helper is not a paper result. -/
@[expose] def setoid : Setoid FramedBall where
  r := equiv
  iseqv := by
    constructor
    · intro M
      exact ⟨FramedBallIso.refl M⟩
    · intro M N h
      rcases h with ⟨I⟩
      exact ⟨FramedBallIso.symm I⟩
    · intro M N P hMN hNP
      rcases hMN with ⟨I⟩
      rcases hNP with ⟨J⟩
      exact ⟨FramedBallIso.trans I J⟩

/-- The missing frame edge cannot witness a directed step, since every
`directedStep` witness must be a present edge. local topology reading-R candidate helper;
no reading is adopted, and this is not a paper result. -/
theorem frameEdge_not_directedStep_witness (M : FramedBall) (v w :
    CombinatorialMap.VertexQuotient M.map.toCombinatorialMap) :
    ¬ ∃ d, d = M.frameEdgeDart ∧ ¬ M.map.missing d ∧ M.map.tail d ∧
      Quotient.mk (Equiv.Perm.SameCycle.setoid M.map.rot) d = v ∧
      Quotient.mk (Equiv.Perm.SameCycle.setoid M.map.rot) (M.map.edgeInv d) = w := by
  rintro ⟨d, rfl, hpresent, htail, hsource, htarget⟩
  exact hpresent M.frameEdge_missing

end FramedBall

/-- Equivalence class of local topology reading-R candidate carriers. Its ambient universe
is `Type 1`, because `FramedBall.D : Type`. No reading is adopted; this helper
is not a paper result. -/
@[expose] def FramedBallClass := Quotient FramedBall.setoid

end DirectedDistances.PlanarMap
