/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.RootedLocallyFiniteBall
public import DirectedDistances.PlanarMap.KMSWStageFramedBall

public section
namespace DirectedDistances.PlanarMap

open Equiv



theorem inducedCombinatorialMap_nested_edgeInvClosed
    {D : Type} [Fintype D] [DecidableEq D] (M : CombinatorialMap D)
    (S T : Finset D) (hS : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (hT : ∀ d, d ∈ T → M.edgeInv d ∈ T) :
    ∀ z, z ∈ firstReturnSubset T S →
      (inducedCombinatorialMap M T hT).edgeInv z ∈ firstReturnSubset T S := by
  intro z hz
  simp only [firstReturnSubset, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  simp only [inducedCombinatorialMap, Equiv.Perm.subtypePerm_apply]
  exact hS z.1 hz




theorem inducedCombinatorialMap_nested_face_sameCycle
    {D : Type} [Fintype D] [DecidableEq D] (M : CombinatorialMap D)
    (S T : Finset D) (hST : ∀ d, d ∈ S → d ∈ T)
    (hS : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (hT : ∀ d, d ∈ T → M.edgeInv d ∈ T)
    (x y : {d : D // d ∈ S})
    (hxy :
      let N := inducedCombinatorialMap M T hT
      let U := firstReturnSubset T S
      let hU := inducedCombinatorialMap_nested_edgeInvClosed M S T hS hT
      let K := inducedCombinatorialMap N U hU
      K.faceSucc.SameCycle
        (⟨⟨x.1, hST x.1 x.2⟩, by simp [U, firstReturnSubset, x.2]⟩)
        (⟨⟨y.1, hST y.1 y.2⟩, by simp [U, firstReturnSubset, y.2]⟩)) :
    (inducedCombinatorialMap M S hS).faceSucc.SameCycle x y := by
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
  let xU : {z : {d : D // d ∈ T} // z ∈ U} :=
    ⟨⟨x.1, hST x.1 x.2⟩, by simp [U, firstReturnSubset, x.2]⟩
  let yU : {z : {d : D // d ∈ T} // z ∈ U} :=
    ⟨⟨y.1, hST y.1 y.2⟩, by simp [U, firstReturnSubset, y.2]⟩
  have hxy' : K.faceSucc.SameCycle xU yU := hxy
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
  have hface (z : {z : {d : D // d ∈ T} // z ∈ U}) :
      e (K.faceSucc z) = L.faceSucc (e z) := by
    change e (K.rot.symm (K.edgeInv z)) = L.rot.symm (L.edgeInv (e z))
    rw [hrotSymm, hedge]
  obtain ⟨n, hn⟩ := hxy'.exists_nat_pow_eq
  have hpow (n : ℕ) (z : {z : {d : D // d ∈ T} // z ∈ U}) :
      e ((K.faceSucc ^ n) z) = (L.faceSucc ^ n) (e z) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply,
        hface, ih]
  have hmapped : (L.faceSucc ^ n) (e xU) = e yU := by
    calc
      (L.faceSucc ^ n) (e xU) = e ((K.faceSucc ^ n) xU) := (hpow n xU).symm
      _ = e yU := congrArg e hn
  have hx : e xU = x := by apply Subtype.ext; rfl
  have hy : e yU = y := by apply Subtype.ext; rfl
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast]
  rw [hx, hy] at hmapped
  exact hmapped




theorem inducedCombinatorialMap_nested_face_restriction
    {D : Type} [Fintype D] [DecidableEq D] (M : CombinatorialMap D)
    (S T : Finset D) (hST : ∀ d, d ∈ S → d ∈ T)
    (hS : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (hT : ∀ d, d ∈ T → M.edgeInv d ∈ T)
    (x y : {d : D // d ∈ S})
    (hplanar : (inducedCombinatorialMap M T hT).IsPlanar)
    (hconn :
      let N := inducedCombinatorialMap M T hT
      let U := firstReturnSubset T S
      let hU := inducedCombinatorialMap_nested_edgeInvClosed M S T hS hT
      (inducedCombinatorialMap N U hU).IsConnected)
    (hxy :
      (inducedCombinatorialMap M T hT).faceSucc.SameCycle
        ⟨x.1, hST x.1 x.2⟩ ⟨y.1, hST y.1 y.2⟩) :
    (inducedCombinatorialMap M S hS).faceSucc.SameCycle x y := by
  classical
  let N := inducedCombinatorialMap M T hT
  let U := firstReturnSubset T S
  let hU := inducedCombinatorialMap_nested_edgeInvClosed M S T hS hT
  let K := inducedCombinatorialMap N U hU
  let xU : {z : {d : D // d ∈ T} // z ∈ U} :=
    ⟨⟨x.1, hST x.1 x.2⟩, by simp [U, firstReturnSubset, x.2]⟩
  let yU : {z : {d : D // d ∈ T} // z ∈ U} :=
    ⟨⟨y.1, hST y.1 y.2⟩, by simp [U, firstReturnSubset, y.2]⟩
  have hxyK : K.faceSucc.SameCycle xU yU := by
    apply inducedCombinatorialMap_face_sameCycle_of_connected_planar
      N hplanar U hU hconn xU yU
    exact hxy
  exact inducedCombinatorialMap_nested_face_sameCycle M S T hST hS hT x y hxyK

end DirectedDistances.PlanarMap
end
