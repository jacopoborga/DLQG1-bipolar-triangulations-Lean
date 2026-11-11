/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.CyclicRestriction
public import DirectedDistances.PlanarMap.RootedLocallyFiniteMap
import DirectedDistances.PlanarMap.KMSWStageFramedBall

public section
namespace DirectedDistances.PlanarMap

open Equiv



theorem rootedLocallyFiniteRadiusVertices_mono (M : RootedLocallyFiniteMap)
    {r s : ℕ} (hrs : r ≤ s) :
    rootedLocallyFiniteRadiusVertices M r ⊆ rootedLocallyFiniteRadiusVertices M s := by
  intro v hv
  rw [mem_rootedLocallyFiniteRadiusVertices] at hv ⊢
  induction s generalizing r v with
  | zero =>
      have hr : r = 0 := by omega
      subst r
      exact hv
  | succ s ih =>
      by_cases hrs' : r ≤ s
      · exact .stay (ih hrs' hv)
      · have hr : r = s + 1 := by omega
        subst r
        exact hv



theorem rootedLocallyFiniteRotationReturn (M : RootedLocallyFiniteMap) (d : M.D) :
    ∃ k : ℕ, 0 < k ∧ (M.rot ^ k) d = d := by
  classical
  let O := rootedLocallyFiniteVertexDartFinset M
    (rootedLocallyFiniteVertexClassOf M d)
  have hd : d ∈ O := by
    simp [O, mem_rootedLocallyFiniteVertexDartFinset]
  have hrot : ∀ x : M.D, M.rot x ∈ O ↔ x ∈ O := by
    intro x
    change M.rot x ∈ rootedLocallyFiniteVertexDartFinset M
        (rootedLocallyFiniteVertexClassOf M d) ↔
      x ∈ rootedLocallyFiniteVertexDartFinset M
        (rootedLocallyFiniteVertexClassOf M d)
    rw [mem_rootedLocallyFiniteVertexDartFinset,
      mem_rootedLocallyFiniteVertexDartFinset]
    have hcycle : M.rot.SameCycle (M.rot x) x :=
      Equiv.Perm.SameCycle.rfl.apply_left
    have hclass : rootedLocallyFiniteVertexClassOf M (M.rot x) =
        rootedLocallyFiniteVertexClassOf M x := Quotient.sound hcycle
    constructor
    · intro hx
      exact hclass.symm.trans hx
    · intro hx
      exact hclass.trans hx
  let ρ : Equiv.Perm O := M.rot.subtypePerm hrot
  let x : O := ⟨d, hd⟩
  refine ⟨orderOf ρ, orderOf_pos ρ, ?_⟩
  have hpow (n : ℕ) : ((ρ ^ n) x).1 = (M.rot ^ n) d := by
    induction n with
    | zero => rfl
    | succ n ih =>
        calc
          ((ρ ^ (n + 1)) x).1 = (ρ ((ρ ^ n) x)).1 := by
            rw [pow_succ', Equiv.Perm.mul_apply]
          _ = M.rot ((M.rot ^ n) d) := by
            simp only [ρ, Equiv.Perm.subtypePerm_apply, ih]
          _ = (M.rot ^ (n + 1)) d := by
            rw [pow_succ', Equiv.Perm.mul_apply]
  have hone : ρ ^ orderOf ρ = 1 := pow_orderOf_eq_one ρ
  have hval : ((ρ ^ orderOf ρ) x).1 = d := by rw [hone]; rfl
  exact (hpow (orderOf ρ)).symm.trans hval



theorem rootedLocallyFiniteBallDarts_edgeInv_closed
    (M : RootedLocallyFiniteMap) (r : ℕ) (d : M.D)
    (hd : d ∈ rootedLocallyFiniteBallDarts M r) :
    M.edgeInv d ∈ rootedLocallyFiniteBallDarts M r := by
  rw [mem_rootedLocallyFiniteBallDarts] at hd ⊢
  simpa only [M.edgeInv_invol] using hd.symm




theorem rootedLocallyFiniteBallDarts_frame_mem
    (M : RootedLocallyFiniteMap) {r : ℕ} (hr : 0 < r) :
    M.rootDart ∈ rootedLocallyFiniteBallDarts M r ∧
      M.frameEdgeDart ∈ rootedLocallyFiniteBallDarts M r ∧
      M.edgeInv M.frameEdgeDart ∈ rootedLocallyFiniteBallDarts M r := by
  have hroot0 : rootedLocallyFiniteVertexClassOf M M.rootDart ∈
      rootedLocallyFiniteRadiusVertices M 0 := by
    simp [rootedLocallyFiniteRadiusVertices]
  have hframe0 : rootedLocallyFiniteVertexClassOf M M.frameEdgeDart ∈
      rootedLocallyFiniteRadiusVertices M 0 := by
    rw [mem_rootedLocallyFiniteRadiusVertices]
    have hclass : rootedLocallyFiniteVertexClassOf M M.frameEdgeDart =
        rootedLocallyFiniteVertexClassOf M M.rootDart :=
      (Quotient.sound M.frameEdge_at_root).symm
    rw [hclass]
    exact rootedLocallyFiniteWithinRadius.root
  have hrootopp1 : rootedLocallyFiniteVertexClassOf M
      (M.edgeInv M.rootDart) ∈ rootedLocallyFiniteRadiusVertices M 1 := by
    rw [mem_rootedLocallyFiniteRadiusVertices]
    apply rootedLocallyFiniteWithinRadius.edge
      rootedLocallyFiniteWithinRadius.root
    exact ⟨M.rootDart, rfl, rfl⟩
  have hedge1 : rootedLocallyFiniteVertexClassOf M
      (M.edgeInv M.frameEdgeDart) ∈ rootedLocallyFiniteRadiusVertices M 1 := by
    rw [mem_rootedLocallyFiniteRadiusVertices]
    apply rootedLocallyFiniteWithinRadius.edge
      rootedLocallyFiniteWithinRadius.root
    exact ⟨M.frameEdgeDart,
      (Quotient.sound M.frameEdge_at_root).symm, rfl⟩
  have hroot : rootedLocallyFiniteVertexClassOf M M.rootDart ∈
      rootedLocallyFiniteRadiusVertices M r :=
    rootedLocallyFiniteRadiusVertices_mono M (Nat.zero_le r) hroot0
  have hframe : rootedLocallyFiniteVertexClassOf M M.frameEdgeDart ∈
      rootedLocallyFiniteRadiusVertices M r :=
    rootedLocallyFiniteRadiusVertices_mono M (Nat.zero_le r) hframe0
  have hrootopp : rootedLocallyFiniteVertexClassOf M
      (M.edgeInv M.rootDart) ∈ rootedLocallyFiniteRadiusVertices M r :=
    rootedLocallyFiniteRadiusVertices_mono M (Nat.succ_le_iff.mpr hr) hrootopp1
  have hedge : rootedLocallyFiniteVertexClassOf M
      (M.edgeInv M.frameEdgeDart) ∈ rootedLocallyFiniteRadiusVertices M r :=
    rootedLocallyFiniteRadiusVertices_mono M (Nat.succ_le_iff.mpr hr) hedge1
  refine ⟨?_, ?_, ?_⟩
  · exact (mem_rootedLocallyFiniteBallDarts M r M.rootDart).mpr
      ⟨hroot, hrootopp⟩
  · exact (mem_rootedLocallyFiniteBallDarts M r M.frameEdgeDart).mpr
      ⟨hframe, hedge⟩
  · exact (mem_rootedLocallyFiniteBallDarts M r (M.edgeInv M.frameEdgeDart)).mpr
      ⟨hedge, by simpa only [M.edgeInv_invol] using hframe⟩



@[expose] noncomputable def rootedLocallyFiniteBallCombinatorialMap
    (M : RootedLocallyFiniteMap) (r : ℕ)
    [DecidableEq {d : M.D // d ∈ rootedLocallyFiniteBallDarts M r}] :
    CombinatorialMap {d : M.D // d ∈ rootedLocallyFiniteBallDarts M r} := by
  classical
  let S := rootedLocallyFiniteBallDarts M r
  have hflip : ∀ d : M.D, M.edgeInv d ∈ S ↔ d ∈ S := by
    intro d
    constructor
    · intro hd
      have h := rootedLocallyFiniteBallDarts_edgeInv_closed M r (M.edgeInv d) hd
      simpa only [M.edgeInv_invol] using h
    · exact rootedLocallyFiniteBallDarts_edgeInv_closed M r d
  let hreturn : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (M.rot ^ k) x.1 ∈ S := by
    intro x
    obtain ⟨k, hk, hperiod⟩ := rootedLocallyFiniteRotationReturn M x.1
    refine ⟨k, hk, ?_⟩
    rw [hperiod]
    exact x.2
  exact
    { edgeInv := M.edgeInv.subtypePerm hflip
      edgeInv_invol := by
        intro d
        apply Subtype.ext
        exact M.edgeInv_invol d.1
      edgeInv_ne := by
        intro d hd
        exact M.edgeInv_ne d.1 (congrArg Subtype.val hd)
      rot := cyclicFirstReturn M.rot S hreturn }



@[expose] def rootedLocallyFiniteBallMissing (M : RootedLocallyFiniteMap)
    (r : ℕ) : {d : M.D // d ∈ rootedLocallyFiniteBallDarts M r} → Prop :=
  fun d => M.missing d.1



@[expose] def rootedLocallyFiniteBallTail (M : RootedLocallyFiniteMap)
    (r : ℕ) : {d : M.D // d ∈ rootedLocallyFiniteBallDarts M r} → Prop :=
  fun d => M.tail d.1



@[expose] noncomputable def rootedLocallyFiniteOuterFrameDart
    (M : RootedLocallyFiniteMap) : M.D := by
  classical
  exact if Equiv.Perm.SameCycle (M.rot.symm * M.edgeInv) M.outer M.frameEdgeDart
    then M.frameEdgeDart else M.edgeInv M.frameEdgeDart

/-- The selected side of the missing frame edge belongs to the ambient outer -/
theorem rootedLocallyFiniteOuterFrameDart_outer (M : RootedLocallyFiniteMap) :
    Equiv.Perm.SameCycle (M.rot.symm * M.edgeInv) M.outer
      (rootedLocallyFiniteOuterFrameDart M) := by
  classical
  unfold rootedLocallyFiniteOuterFrameDart
  split
  · assumption
  · rename_i h
    rcases M.missing_outer M.frameEdgeDart M.frameEdge_missing with hframe | hopposite
    · exact (h hframe).elim
    · exact hopposite











structure RootedLocallyFinitePlanarMap extends RootedLocallyFiniteMap where
  /-- Expected provider input: each positive-radius induced ball has
  genus-zero combinatorial planarity. For UIQBOT and UIBHBOT, the corresponding
  embedding or stabilization argument is an expected provider input; this file
  does not establish it for concrete maps. -/
  ball_isPlanar : ∀ r, 0 < r →
    letI : DecidableEq {d : D // d ∈ rootedLocallyFiniteBallDarts
        toRootedLocallyFiniteMap r} := Classical.decEq _
    (rootedLocallyFiniteBallCombinatorialMap toRootedLocallyFiniteMap r).IsPlanar
  /-- An ambient outer-face dart and the selected outer-facing side of the
  frame edge are jointly captured on one finite outer face at some radius at
  least as large as the source ball. For UIQBOT and UIBHBOT this is an expected
  provider input from the embedding or stabilization of finite planar
  approximants; this file does not establish it for concrete maps. -/
  outerFace_captured_in_larger_ball : ∀ r, 0 < r → ∀ d,
    d ∈ rootedLocallyFiniteBallDarts toRootedLocallyFiniteMap r →
    Equiv.Perm.SameCycle
      (rot.symm * edgeInv) outer d →
    ∃ R, r ≤ R ∧ ∃ hdR : d ∈ rootedLocallyFiniteBallDarts
        toRootedLocallyFiniteMap R,
      ∃ hfR : rootedLocallyFiniteOuterFrameDart toRootedLocallyFiniteMap ∈
          rootedLocallyFiniteBallDarts
        toRootedLocallyFiniteMap R,
        letI : DecidableEq {d : D // d ∈ rootedLocallyFiniteBallDarts
            toRootedLocallyFiniteMap R} := Classical.decEq _
        CombinatorialMap.IsOuter
          (rootedLocallyFiniteBallCombinatorialMap toRootedLocallyFiniteMap R)
          ⟨rootedLocallyFiniteOuterFrameDart toRootedLocallyFiniteMap, hfR⟩
          ⟨d, hdR⟩

private theorem inducedCombinatorialMap_nested_edgeInvClosed
    {D : Type} [Fintype D] [DecidableEq D] (M : CombinatorialMap D)
    (S T : Finset D) (hS : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (hT : ∀ d, d ∈ T → M.edgeInv d ∈ T) :
    ∀ z, z ∈ firstReturnSubset T S →
      (inducedCombinatorialMap M T hT).edgeInv z ∈ firstReturnSubset T S := by
  intro z hz
  simp only [firstReturnSubset, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  simp only [inducedCombinatorialMap, Equiv.Perm.subtypePerm_apply]
  exact hS z.1 hz

private theorem inducedCombinatorialMap_nested_face_sameCycle
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
  have hx : e xU = x := by
    apply Subtype.ext
    rfl
  have hy : e yU = y := by
    apply Subtype.ext
    rfl
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast]
  rw [hx, hy] at hmapped
  exact hmapped

end DirectedDistances.PlanarMap
end
