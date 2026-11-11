/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.RootedLocallyFiniteBall
public import DirectedDistances.PlanarMap.RootedLocallyFiniteBallOuter
public import DirectedDistances.PlanarMap.KMSWStageFramedBall

public section
namespace DirectedDistances.PlanarMap

open Equiv



theorem rootedLocallyFiniteBall_rot_sameCycle_iff
    (M : RootedLocallyFiniteMap) (r : ℕ)
    [DecidableEq {d : M.D // d ∈ rootedLocallyFiniteBallDarts M r}]
    (x y : {d : M.D // d ∈ rootedLocallyFiniteBallDarts M r}) :
    (rootedLocallyFiniteBallCombinatorialMap M r).rot.SameCycle x y ↔
      M.rot.SameCycle x.1 y.1 := by
  classical
  let S := rootedLocallyFiniteBallDarts M r
  let hreturn : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (M.rot ^ k) x.1 ∈ S := by
    intro x
    obtain ⟨k, hk, hperiod⟩ := rootedLocallyFiniteRotationReturn M x.1
    exact ⟨k, hk, by rw [hperiod]; exact x.2⟩
  change (cyclicFirstReturn M.rot S hreturn).SameCycle x y ↔ _
  exact firstReturn_sameCycle_iff M.rot S hreturn x y

private def rootedLocallyFiniteBallStep {D : Type} [Fintype D]
    [DecidableEq D] (M : CombinatorialMap D) (x y : D) : Prop :=
  y = M.rot x ∨ y = M.rot.symm x ∨
    y = M.edgeInv x ∨ y = M.edgeInv.symm x

private theorem rootedLocallyFiniteBallRotation_reachable
    {D : Type} [Fintype D] [DecidableEq D] (M : CombinatorialMap D)
    {x y : D} (h : M.rot.SameCycle x y) :
    Relation.ReflTransGen (rootedLocallyFiniteBallStep M) x y := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have hpow : ∀ n, Relation.ReflTransGen (rootedLocallyFiniteBallStep M)
      x ((M.rot ^ n) x) := by
    intro n
    induction n with
    | zero => exact Relation.ReflTransGen.refl
    | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact ih.tail (Or.inl rfl)
  rw [← hn]
  exact hpow n

private theorem rootedLocallyFiniteBallRoot_mem (M : RootedLocallyFiniteMap)
    (r : ℕ) (hr : 0 < r) : M.rootDart ∈ rootedLocallyFiniteBallDarts M r :=
  (rootedLocallyFiniteBallDarts_frame_mem M hr).1

private theorem rootedLocallyFiniteBall_edgeInv_symm
    {D : Type} [Fintype D] [DecidableEq D] (C : CombinatorialMap D) (d : D) :
    C.edgeInv.symm d = C.edgeInv d := by
  apply C.edgeInv.injective
  simp [C.edgeInv_invol]

private theorem rootedLocallyFiniteBallPath_reaches (M : RootedLocallyFiniteMap)
    (r : ℕ) (hr : 0 < r)
    [DecidableEq {d : M.D // d ∈ rootedLocallyFiniteBallDarts M r}]
    {v : RootedLocallyFiniteVertex M.D M.rot} {n : ℕ}
    (hp : rootedLocallyFiniteWithinRadius M n v) (hn : n ≤ r)
    (d : M.D) (hd : d ∈ rootedLocallyFiniteBallDarts M r)
    (hvertex : rootedLocallyFiniteVertexClassOf M d = v) :
    Relation.ReflTransGen
      (rootedLocallyFiniteBallStep
        (rootedLocallyFiniteBallCombinatorialMap M r))
      ⟨M.rootDart, rootedLocallyFiniteBallRoot_mem M r hr⟩ ⟨d, hd⟩ := by
  classical
  let S := rootedLocallyFiniteBallDarts M r
  let hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S :=
    fun d hd => rootedLocallyFiniteBallDarts_edgeInv_closed M r d hd
  let N := rootedLocallyFiniteBallCombinatorialMap M r
  revert hn d hd hvertex
  induction hp with
  | root =>
      intro hn d hd hvertex
      have hcycle : M.rot.SameCycle M.rootDart d :=
        (Quotient.exact hvertex).symm
      have hcycleN : N.rot.SameCycle
          (⟨M.rootDart, rootedLocallyFiniteBallRoot_mem M r hr⟩ :
            {d : M.D // d ∈ S}) ⟨d, hd⟩ := by
        exact (rootedLocallyFiniteBall_rot_sameCycle_iff M r _ _).2 hcycle
      exact rootedLocallyFiniteBallRotation_reachable N hcycleN
  | @stay n v hp ih =>
      intro hn d hd hvertex
      exact ih (by omega) d hd hvertex
  | @edge n v w hp hstep ih =>
      intro hn d hd hvertex
      rcases hstep with ⟨e, hev, hew⟩
      have hn' : n ≤ r := by omega
      have hw : v ∈ rootedLocallyFiniteRadiusVertices M r := by
        exact rootedLocallyFiniteRadiusVertices_mono M hn'
          ((mem_rootedLocallyFiniteRadiusVertices M n v).2 hp)
      have hz : w ∈ rootedLocallyFiniteRadiusVertices M r := by
        exact rootedLocallyFiniteRadiusVertices_mono M hn
          ((mem_rootedLocallyFiniteRadiusVertices M (n + 1) w).2
            (rootedLocallyFiniteWithinRadius.edge hp ⟨e, hev, hew⟩))
      have heS : e ∈ S := by
        apply (mem_rootedLocallyFiniteBallDarts M r e).2
        constructor
        · change rootedLocallyFiniteVertexClass M.rot e ∈ _
          exact hev ▸ hw
        · change rootedLocallyFiniteVertexClass M.rot (M.edgeInv e) ∈ _
          exact hew ▸ hz
      have hreach := ih hn' e heS hev
      have hedge : N.edgeInv (⟨e, heS⟩ : {d : M.D // d ∈ S}) =
          ⟨M.edgeInv e, hflip e heS⟩ := by
        apply Subtype.ext
        rfl
      have hflipstep : Relation.ReflTransGen
          (rootedLocallyFiniteBallStep N) (⟨e, heS⟩ : {d : M.D // d ∈ S})
          ⟨M.edgeInv e, hflip e heS⟩ :=
        Relation.ReflTransGen.single (Or.inr (Or.inr (Or.inl hedge)))
      have hcycle : M.rot.SameCycle (M.edgeInv e) d :=
        Quotient.exact (hew.trans hvertex.symm)
      have hcycleN : N.rot.SameCycle ⟨M.edgeInv e, hflip e heS⟩ ⟨d, hd⟩ :=
        (rootedLocallyFiniteBall_rot_sameCycle_iff M r _ _).2 hcycle
      exact hreach.trans (hflipstep.trans
        (rootedLocallyFiniteBallRotation_reachable N hcycleN))




theorem rootedLocallyFiniteBallCombinatorialMap_connected
    (M : RootedLocallyFiniteMap) (r : ℕ) (hr : 0 < r)
    [DecidableEq {d : M.D // d ∈ rootedLocallyFiniteBallDarts M r}] :
    (rootedLocallyFiniteBallCombinatorialMap M r).IsConnected := by
  classical
  let S := rootedLocallyFiniteBallDarts M r
  let N := rootedLocallyFiniteBallCombinatorialMap M r
  have hsymmetric : Std.Symm (rootedLocallyFiniteBallStep N) := ⟨by
    intro x y hxy
    rcases hxy with hxy | hxy | hxy | hxy
    · exact Or.inr (Or.inl (by simp [hxy]))
    · exact Or.inl (by simp [hxy])
    · exact Or.inr (Or.inr (Or.inr (by simp [hxy])))
    · exact Or.inr (Or.inr (Or.inl (by simp [hxy])))⟩
  intro x y
  have hxmem := (mem_rootedLocallyFiniteBallDarts M r x.1).1 x.2
  have hymem := (mem_rootedLocallyFiniteBallDarts M r y.1).1 y.2
  have hpx := (mem_rootedLocallyFiniteRadiusVertices M r _).1 hxmem.1
  have hpy := (mem_rootedLocallyFiniteRadiusVertices M r _).1 hymem.1
  have hreachx := rootedLocallyFiniteBallPath_reaches M r hr hpx
    (Nat.le_refl r) x.1 x.2 rfl
  have hreachy := rootedLocallyFiniteBallPath_reaches M r hr hpy
    (Nat.le_refl r) y.1 y.2 rfl
  have hreverseSymm : Std.Symm
      (Relation.ReflTransGen (rootedLocallyFiniteBallStep N)) :=
    @Relation.ReflTransGen.stdSymm _ _ hsymmetric
  exact (hreverseSymm.symm
    (⟨M.rootDart, rootedLocallyFiniteBallRoot_mem M r hr⟩ :
      {d : M.D // d ∈ S}) x hreachx).trans hreachy




theorem inducedCombinatorialMap_nested_connected
    {D : Type} [Fintype D] [DecidableEq D] (M : CombinatorialMap D)
    (S T : Finset D) (hST : ∀ d, d ∈ S → d ∈ T)
    (hS : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (hT : ∀ d, d ∈ T → M.edgeInv d ∈ T)
    (hconn : (inducedCombinatorialMap M S hS).IsConnected) :
    let N := inducedCombinatorialMap M T hT
    let U := firstReturnSubset T S
    let hU := inducedCombinatorialMap_nested_edgeInvClosed M S T hS hT
    (inducedCombinatorialMap N U hU).IsConnected := by
  classical
  let N := inducedCombinatorialMap M T hT
  let U := firstReturnSubset T S
  let hU := inducedCombinatorialMap_nested_edgeInvClosed M S T hS hT
  let K := inducedCombinatorialMap N U hU
  let L := inducedCombinatorialMap M S hS
  let e : {z : {d : D // d ∈ T} // z ∈ U} ≃ {d : D // d ∈ S} := {
    toFun := fun z => ⟨z.1.1, by simpa [U, firstReturnSubset] using z.2⟩
    invFun := fun z => ⟨⟨z.1, hST z.1 z.2⟩,
      by simp [U, firstReturnSubset, z.2]⟩
    left_inv := by intro z; cases z with | mk z hz => cases z; rfl
    right_inv := by intro z; cases z; rfl }
  have hrot (z : {z : {d : D // d ∈ T} // z ∈ U}) :
      e (K.rot z) = L.rot (e z) := by
    cases z with
    | mk z hz =>
      cases z with
      | mk a haT =>
        have haS : a ∈ S := by simpa [U, firstReturnSubset] using hz
        let az : {d : D // d ∈ S} := ⟨a, haS⟩
        have hfirst := firstReturn_nested' M.rot T S
          (finitePermutationReturn M.rot T) hST
          (finitePermutationReturn
            (cyclicFirstReturn M.rot T (finitePermutationReturn M.rot T)) U)
          (finitePermutationReturn M.rot S) az
        apply Subtype.ext
        change ((K.rot ⟨⟨a, haT⟩, hz⟩).1).1 = (L.rot az).1
        exact hfirst
  have hedge (z : {z : {d : D // d ∈ T} // z ∈ U}) :
      e (K.edgeInv z) = L.edgeInv (e z) := by
    apply Subtype.ext
    rfl
  have hrotSymm (z : {z : {d : D // d ∈ T} // z ∈ U}) :
      e (K.rot.symm z) = L.rot.symm (e z) := by
    apply L.rot.injective
    calc
      L.rot (e (K.rot.symm z)) = e (K.rot (K.rot.symm z)) := (hrot _).symm
      _ = e z := by simp
      _ = L.rot (L.rot.symm (e z)) := by simp
  have hstep {a b : {d : D // d ∈ S}}
      (hab : b = L.rot a ∨ b = L.rot.symm a ∨
        b = L.edgeInv a ∨ b = L.edgeInv.symm a) :
      e.symm b = K.rot (e.symm a) ∨
        e.symm b = K.rot.symm (e.symm a) ∨
        e.symm b = K.edgeInv (e.symm a) ∨
        e.symm b = K.edgeInv.symm (e.symm a) := by
    rcases hab with h | h | h | h
    · left
      apply e.injective
      calc
        e (e.symm b) = b := e.apply_symm_apply b
        _ = L.rot a := h
        _ = e (K.rot (e.symm a)) := by rw [hrot]; simp
    · right
      left
      apply e.injective
      calc
        e (e.symm b) = b := e.apply_symm_apply b
        _ = L.rot.symm a := h
        _ = e (K.rot.symm (e.symm a)) := by rw [hrotSymm]; simp
    · right
      right
      left
      apply e.injective
      calc
        e (e.symm b) = b := e.apply_symm_apply b
        _ = L.edgeInv a := h
        _ = e (K.edgeInv (e.symm a)) := by rw [hedge]; simp
    · right
      right
      right
      have h' : b = L.edgeInv a := h.trans
        (rootedLocallyFiniteBall_edgeInv_symm L a)
      apply e.injective
      calc
        e (e.symm b) = b := e.apply_symm_apply b
        _ = L.edgeInv a := h'
        _ = e (K.edgeInv.symm (e.symm a)) := by
          rw [rootedLocallyFiniteBall_edgeInv_symm K (e.symm a), hedge]
          simp
  have hmap : ∀ {a b : {d : D // d ∈ S}},
      Relation.ReflTransGen
        (fun x y => y = L.rot x ∨ y = L.rot.symm x ∨
          y = L.edgeInv x ∨ y = L.edgeInv.symm x) a b →
      Relation.ReflTransGen
        (fun x y => y = K.rot x ∨ y = K.rot.symm x ∨
          y = K.edgeInv x ∨ y = K.edgeInv.symm x)
        (e.symm a) (e.symm b) := by
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail hprev hlast ih => exact ih.tail (hstep hlast)
  change K.IsConnected
  intro x y
  have hxy := hconn (e x) (e y)
  have hxyK := hmap hxy
  exact hxyK

end DirectedDistances.PlanarMap
end
