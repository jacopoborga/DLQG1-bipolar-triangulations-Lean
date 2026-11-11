/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlanarPathCutHalves

/-! # Half maps of a planar path cut

paper result. The finite-permutation first-return construction supplies the
vertex rotations on the two closed half-dart carriers. -/

public section
namespace DirectedDistances.PlanarMap

open Equiv

/-- Iteration of a permutation agrees with its natural-number power. Helper
result. -/
theorem perm_iterate_eq_pow {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (k : ℕ) :
    (σ : α → α)^[k] = (σ ^ k : Equiv.Perm α) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext x
    rw [Function.iterate_succ_apply, ih]
    simp only [pow_succ, Equiv.Perm.mul_apply]

/-- The least positive return time of a point of `S` under a finite
not the paper result. -/
@[expose] noncomputable def firstReturnTime {α : Type*} [Fintype α]
    [DecidableEq α] (σ : Equiv.Perm α) (S : Set α)
    [DecidablePred (fun y : α => y ∈ S)] (x : S) : ℕ :=
  Nat.find (show ∃ k : ℕ, 0 < k ∧ (σ : α → α)^[k] x.1 ∈ S from by
    refine ⟨orderOf σ, orderOf_pos σ, ?_⟩
    rw [perm_iterate_eq_pow]
    simp)

/-- The first-return time is positive and returns to `S`.
paper result. -/
theorem firstReturnTime_spec {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (S : Set α)
    [DecidablePred (fun y : α => y ∈ S)] (x : S) :
    0 < firstReturnTime σ S x ∧
      (σ : α → α)^[firstReturnTime σ S x] x.1 ∈ S := by
  exact Nat.find_spec (show ∃ k : ℕ, 0 < k ∧ (σ : α → α)^[k] x.1 ∈ S from by
    refine ⟨orderOf σ, orderOf_pos σ, ?_⟩
    rw [perm_iterate_eq_pow]
    simp)

/-- No earlier positive iterate returns to `S`.
paper result. -/
theorem firstReturnTime_min {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (S : Set α)
    [DecidablePred (fun y : α => y ∈ S)] (x : S) {k : ℕ}
    (hk : 0 < k) (hret : (σ : α → α)^[k] x.1 ∈ S) :
    firstReturnTime σ S x ≤ k := by
  change Nat.find (show ∃ j : ℕ, 0 < j ∧ (σ : α → α)^[j] x.1 ∈ S from by
    refine ⟨orderOf σ, orderOf_pos σ, ?_⟩
    rw [perm_iterate_eq_pow]
    simp) ≤ k
  exact Nat.find_min'
    (show ∃ j : ℕ, 0 < j ∧ (σ : α → α)^[j] x.1 ∈ S from by
      refine ⟨orderOf σ, orderOf_pos σ, ?_⟩
      rw [perm_iterate_eq_pow]
      simp)
    ⟨hk, hret⟩

/-- The first positive return of a point to a subset, as a point of that
paper result. -/
@[expose] noncomputable def firstReturn {α : Type*} [Fintype α]
    [DecidableEq α] (σ : Equiv.Perm α) (S : Set α)
    [DecidablePred (fun y : α => y ∈ S)] (x : S) : S :=
  ⟨(σ : α → α)^[firstReturnTime σ S x] x.1,
    (firstReturnTime_spec σ S x).2⟩

/-- The first return time is characterized by return and avoidance of every
intermediate iterate. Helper toward `lem-lr-ind` -/
theorem firstReturnTime_eq_iff {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (S : Set α)
    [DecidablePred (fun y : α => y ∈ S)] (x : S) (k : ℕ) :
    firstReturnTime σ S x = k ↔
      0 < k ∧ (σ : α → α)^[k] x.1 ∈ S ∧
        ∀ j : ℕ, 0 < j → j < k → (σ : α → α)^[j] x.1 ∉ S := by
  constructor
  · intro hk
    subst k
    refine ⟨(firstReturnTime_spec σ S x).1,
      (firstReturnTime_spec σ S x).2, ?_⟩
    intro j hj hjk hmem
    have hmin := firstReturnTime_min σ S x hj hmem
    omega
  · rintro ⟨hk, hret, hbefore⟩
    apply Nat.le_antisymm
    · exact firstReturnTime_min σ S x hk hret
    · by_contra hnot
      have hlt : firstReturnTime σ S x < k := Nat.lt_of_not_ge hnot
      exact hbefore (firstReturnTime σ S x)
        (firstReturnTime_spec σ S x).1 hlt (firstReturnTime_spec σ S x).2

/-- At its first-return time the iterate is the first-return point, and no
intermediate positive iterate lies in the subset. Helper toward `lem-lr-ind`, -/
theorem firstReturn_characterization {α : Type*} [Fintype α]
    [DecidableEq α] (σ : Equiv.Perm α) (S : Set α)
    [DecidablePred (fun y : α => y ∈ S)] (x : S) :
    (σ : α → α)^[firstReturnTime σ S x] x.1 = (firstReturn σ S x : α) ∧
      ∀ j : ℕ, 0 < j → j < firstReturnTime σ S x →
        (σ : α → α)^[j] x.1 ∉ S := by
  constructor
  · rfl
  · intro j hj hjk hmem
    have hmin := firstReturnTime_min σ S x hj hmem
    omega

/-- Inverse iterates traverse the same finite permutation segment backward.
paper result. -/
theorem perm_iterate_inv_sub {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) {j k : ℕ} (hjk : j ≤ k) (x : α) :
    ((σ⁻¹ : Equiv.Perm α) : α → α)^[j] ((σ : α → α)^[k] x) =
      (σ : α → α)^[k - j] x := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjk' : j ≤ k := Nat.le_trans (Nat.le_succ j) hjk
    rw [Function.iterate_succ_apply', ih hjk']
    have hdecomp : k - j = (k - (j + 1)) + 1 := by omega
    rw [hdecomp, Function.iterate_succ_apply']
    simp

/-- The first return under the inverse permutation reverses the first return
under the permutation. Helper toward `lem-lr-ind` -/
theorem firstReturn_inv_apply {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (S : Set α)
    [DecidablePred (fun y : α => y ∈ S)] (x : S) :
    firstReturn (σ⁻¹) S (firstReturn σ S x) = x := by
  let k := firstReturnTime σ S x
  have hchar := firstReturn_characterization σ S x
  have htime : firstReturnTime (σ⁻¹) S (firstReturn σ S x) = k := by
    apply (firstReturnTime_eq_iff (σ⁻¹) S (firstReturn σ S x) k).2
    refine ⟨(firstReturnTime_spec σ S x).1, ?_, ?_⟩
    · change ((σ⁻¹ : Equiv.Perm α) : α → α)^[k]
        ((σ : α → α)^[k] x.1) ∈ S
      rw [perm_iterate_inv_sub σ (Nat.le_refl k)]
      simp
    · intro j hj hjk hmem
      have hkj : j ≤ k := Nat.le_of_lt hjk
      have hqpos : 0 < k - j := by omega
      have hqlt : k - j < k := by omega
      change ((σ⁻¹ : Equiv.Perm α) : α → α)^[j]
        ((σ : α → α)^[k] x.1) ∈ S at hmem
      rw [perm_iterate_inv_sub σ hkj] at hmem
      exact hchar.2 (k - j) hqpos hqlt hmem
  apply Subtype.ext
  change ((σ⁻¹ : Equiv.Perm α) : α → α)^[firstReturnTime (σ⁻¹) S (firstReturn σ S x)]
    ((σ : α → α)^[k] x.1) = x.1
  rw [htime]
  simpa using perm_iterate_inv_sub σ (Nat.le_refl k) x.1

/-- The first-return function is bijective; its inverse is first return under
not the paper result. -/
theorem firstReturn_bijective {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (S : Set α)
    [DecidablePred (fun y : α => y ∈ S)] :
    Function.Bijective (firstReturn σ S) := by
  constructor
  · intro x y hxy
    have h := congrArg (firstReturn (σ⁻¹) S) hxy
    rw [firstReturn_inv_apply σ S x, firstReturn_inv_apply σ S y] at h
    exact h
  · intro y
    refine ⟨firstReturn (σ⁻¹) S y, ?_⟩
    have h := firstReturn_inv_apply (σ⁻¹) S y
    simpa using h

/-- The first-return permutation of a subset under a finite permutation.
paper result. -/
@[expose] noncomputable def firstReturnPerm {α : Type*} [Fintype α]
    [DecidableEq α] (σ : Equiv.Perm α) (S : Set α)
    [DecidablePred (fun y : α => y ∈ S)] : Equiv.Perm S :=
  Equiv.ofBijective (firstReturn σ S) (firstReturn_bijective σ S)

/-- Inverting the first-return permutation is the first-return permutation
of the inverse. Helper toward `lem-lr-ind` -/
theorem firstReturnPerm_symm {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (S : Set α)
    [DecidablePred (fun y : α => y ∈ S)] :
    (firstReturnPerm σ S).symm = firstReturnPerm (σ⁻¹) S := by
  apply Equiv.ext
  intro x
  apply (firstReturnPerm σ S).injective
  rw [Equiv.apply_symm_apply]
  exact (firstReturn_inv_apply (σ⁻¹) S x).symm

/-- Restriction of a permutation to a forward-invariant finite subset.
paper result. -/
@[expose] noncomputable def restrictedPerm {α : Type*} [Fintype α]
    [DecidableEq α] (σ : Equiv.Perm α) (S : Set α)
    [DecidablePred (fun y : α => y ∈ S)]
    (hσ : ∀ x : α, x ∈ S → σ x ∈ S) : Equiv.Perm S := by
  let f : S → S := fun x => ⟨σ x.1, hσ x.1 x.2⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact σ.injective (congrArg Subtype.val hxy)
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  exact Equiv.ofBijective f ⟨hinj, hsurj⟩

/-- On an invariant subset the first-return permutation is ordinary
restriction. Helper toward `lem-lr-ind` -/
theorem firstReturnPerm_eq_restricted {α : Type*} [Fintype α]
    [DecidableEq α] (σ : Equiv.Perm α) (S : Set α)
    [DecidablePred (fun y : α => y ∈ S)]
    (hσ : ∀ x : α, x ∈ S → σ x ∈ S) :
    firstReturnPerm σ S = restrictedPerm σ S hσ := by
  apply Equiv.ext
  intro x
  have htime : firstReturnTime σ S x = 1 := by
    apply (firstReturnTime_eq_iff σ S x 1).2
    refine ⟨Nat.zero_lt_one, hσ x.1 x.2, ?_⟩
    intro j hj hjlt
    omega
  change firstReturn σ S x = ⟨σ x.1, hσ x.1 x.2⟩
  apply Subtype.ext
  simp [firstReturn, htime]

/-- On a subset containing the next iterate, first return agrees with one
application of the permutation. Helper toward `lem-lr-ind` -/
theorem firstReturnPerm_apply_of_mem {α : Type*} [Fintype α]
    [DecidableEq α] (σ : Equiv.Perm α) (S : Set α)
    [DecidablePred (fun y : α => y ∈ S)] (x : S)
    (hσ : σ x.1 ∈ S) :
    (firstReturnPerm σ S x).1 = σ x.1 := by
  have htime : firstReturnTime σ S x = 1 := by
    apply (firstReturnTime_eq_iff σ S x 1).2
    refine ⟨Nat.zero_lt_one, hσ, ?_⟩
    intro j hj hjlt
    omega
  change (firstReturn σ S x).1 = σ x.1
  simp [firstReturn, htime]

/-- On a subset containing the previous iterate, inverse first return agrees
with one inverse-rotation step. Helper toward `lem-lr-ind` -/
theorem firstReturnPerm_symm_apply_of_mem {α : Type*} [Fintype α]
    [DecidableEq α] (σ : Equiv.Perm α) (S : Set α)
    [DecidablePred (fun y : α => y ∈ S)] (x : S)
    (hσ : σ.symm x.1 ∈ S) :
    ((firstReturnPerm σ S).symm x).1 = σ.symm x.1 := by
  rw [firstReturnPerm_symm]
  exact firstReturnPerm_apply_of_mem σ.symm S x hσ

/-- Pointwise action of the restriction permutation. Helper toward -/
theorem restrictedPerm_apply {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (S : Set α)
    [DecidablePred (fun y : α => y ∈ S)]
    (hσ : ∀ x : α, x ∈ S → σ x ∈ S) (x : S) :
    restrictedPerm σ S hσ x = ⟨σ x.1, hσ x.1 x.2⟩ := rfl

/-- The combinatorial map carried by an edge-invariant subset of darts.
paper result. -/
@[expose] noncomputable def closedHalfCombinatorialMap {D : Type*}
    [Fintype D] [DecidableEq D] (B : DirectedMapWithMissing D)
    (S : Set D) [DecidablePred (fun d : D => d ∈ S)]
    (hclosed : ∀ d : D, d ∈ S → B.edgeInv d ∈ S) :
    CombinatorialMap {d : D // d ∈ S} := by
  classical
  refine {
    edgeInv := restrictedPerm B.edgeInv S hclosed
    edgeInv_invol := ?_
    edgeInv_ne := ?_
    rot := firstReturnPerm B.rot S }
  · intro d
    apply Subtype.ext
    simp only [restrictedPerm_apply]
    exact B.edgeInv_invol d.1
  · intro d h
    apply B.edgeInv_ne d.1
    exact congrArg Subtype.val h

/-- A directed map on an edge-invariant subset, with inherited tails and no
missing darts. The marked outer dart is any member; it is immaterial when no
darts are missing. Helper toward `lem-lr-ind` -/
@[expose] noncomputable def closedHalfDirectedMap {D : Type*}
    [Fintype D] [DecidableEq D] (B : DirectedMapWithMissing D)
    (S : Set D) [DecidablePred (fun d : D => d ∈ S)]
    (hclosed : ∀ d : D, d ∈ S → B.edgeInv d ∈ S)
    (hpresent : ∀ d : D, d ∈ S → ¬ B.missing d)
    (hne : ∃ d : D, d ∈ S) :
    DirectedMapWithMissing {d : D // d ∈ S} := by
  classical
  refine {
    toCombinatorialMap := closedHalfCombinatorialMap B S hclosed
    missing := fun _ => False
    missing_edgeInv := ?_
    tail := fun d => B.tail d.1
    tail_iff := ?_
    tail_missing := ?_
    outer := ⟨Classical.choose hne, Classical.choose_spec hne⟩
    missing_outer := ?_ }
  · intro d
    simp
  · intro d hd
    exact B.tail_iff d.1 (hpresent d.1 d.2)
  · intro d hd
    exact False.elim hd
  · intro d hd
    exact False.elim hd

/-- The left closed half has a dart, witnessed by the nonempty left boundary
the paper result. -/
theorem pathCutLeftHalfDarts_nonempty {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    ∃ d : D, d ∈ pathCutLeftHalfDarts B P := by
  have hlen : 0 < B.leftPath.darts.length := by
    rw [B.leftPath.darts_length]
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one B.left_length_pos
  let i : Fin B.leftPath.darts.length := ⟨0, hlen⟩
  let d := B.leftPath.darts.get i
  have hpath : d ∈ B.leftPath.darts := List.get_mem _ _
  have harc : d ∈ pathCutLeftOuterArc B :=
    (mem_pathCutLeftOuterArc_iff B d).2 hpath
  have hleft : d ∈ pathCutLeftDarts B P :=
    ⟨d, Or.inl harc, Relation.ReflTransGen.refl⟩
  exact ⟨d, Or.inl hleft⟩

/-- The right closed half has a dart, witnessed by the reverse of a dart on
the nonempty right boundary path. Helper toward `lem-lr-ind` -/
theorem pathCutRightHalfDarts_nonempty {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    ∃ d : D, d ∈ pathCutRightHalfDarts B P := by
  have hlen : 0 < B.rightPath.darts.length := by
    rw [B.rightPath.darts_length]
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one B.right_length_pos
  let i : Fin B.rightPath.darts.length := ⟨0, hlen⟩
  let p := B.rightPath.darts.get i
  let d := B.map.toCombinatorialMap.edgeInv p
  have hpath : p ∈ B.rightPath.darts := List.get_mem _ _
  have hrev : p ∈ B.rightPath.darts.reverse := List.mem_reverse.mpr hpath
  have houter : d ∈ pathCutRightOuterArc B := by
    apply (mem_pathCutRightOuterArc_iff B d).2
    exact List.mem_map.mpr ⟨p, hrev, rfl⟩
  have hright : d ∈ pathCutRightDarts B P :=
    ⟨d, Or.inl houter, Relation.ReflTransGen.refl⟩
  exact ⟨d, Or.inl hright⟩

/-- The combinatorial map carried by the left closed half of a path cut.
paper result. -/
@[expose] noncomputable def pathCutLeftHalfMap {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    CombinatorialMap {d : D // d ∈ pathCutLeftHalfDarts B P} := by
  classical
  exact closedHalfCombinatorialMap B.map (pathCutLeftHalfDarts B P)
    (fun d hd => pathCutLeftHalf_edgeInv_mem B P hd)

/-- The combinatorial map carried by the right closed half of a path cut.
paper result. -/
@[expose] noncomputable def pathCutRightHalfMap {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    CombinatorialMap {d : D // d ∈ pathCutRightHalfDarts B P} := by
  classical
  exact closedHalfCombinatorialMap B.map (pathCutRightHalfDarts B P)
    (fun d hd => pathCutRightHalf_edgeInv_mem B P hd)

/-- The directed map on the left closed half, with inherited tails and no
not the paper result. -/
@[expose] noncomputable def pathCutLeftHalfDirectedMap {D : Type*}
    [Fintype D] [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    DirectedMapWithMissing {d : D // d ∈ pathCutLeftHalfDarts B P} := by
  classical
  exact closedHalfDirectedMap B.map (pathCutLeftHalfDarts B P)
    (fun d hd => pathCutLeftHalf_edgeInv_mem B P hd)
    (fun d hd => B.noMissingDarts d)
    (pathCutLeftHalfDarts_nonempty B P)

/-- The directed map on the right closed half, with inherited tails and no
not the paper result. -/
@[expose] noncomputable def pathCutRightHalfDirectedMap {D : Type*}
    [Fintype D] [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    DirectedMapWithMissing {d : D // d ∈ pathCutRightHalfDarts B P} := by
  classical
  exact closedHalfDirectedMap B.map (pathCutRightHalfDarts B P)
    (fun d hd => pathCutRightHalf_edgeInv_mem B P hd)
    (fun d hd => B.noMissingDarts d)
    (pathCutRightHalfDarts_nonempty B P)

/-- The inclusion of an edge-closed dart subset into the original map has the
unrooted induced-embedding fields: injectivity, flip and tail commutation, and
first-return rotation. Helper toward `lem-lr-ind` -/
theorem closedHalfEmbeddingFields {D : Type*} [Fintype D] [DecidableEq D]
    (B : DirectedMapWithMissing D) (S : Set D)
    [DecidablePred (fun d : D => d ∈ S)]
    (hclosed : ∀ d : D, d ∈ S → B.edgeInv d ∈ S)
    (hpresent : ∀ d : D, d ∈ S → ¬ B.missing d)
    (hne : ∃ d : D, d ∈ S) :
    Function.Injective (fun d : {d : D // d ∈ S} => d.1) ∧
      (∀ d : {d : D // d ∈ S},
        ((closedHalfDirectedMap B S hclosed hpresent hne).edgeInv d).1 =
          B.edgeInv d.1) ∧
      (∀ d : {d : D // d ∈ S},
        (closedHalfDirectedMap B S hclosed hpresent hne).tail d ↔ B.tail d.1) ∧
      (∀ d : {d : D // d ∈ S}, ∃ k : ℕ, 0 < k ∧
        (B.rot : D → D)^[k] d.1 =
          ((closedHalfDirectedMap B S hclosed hpresent hne).rot d).1 ∧
        ∀ j : ℕ, 0 < j → j < k →
          (B.rot : D → D)^[j] d.1 ∉ Set.range (fun e : {d : D // d ∈ S} => e.1)) := by
  refine ⟨fun _ _ h => Subtype.ext h, ?_, ?_, ?_⟩
  · intro d
    change (restrictedPerm B.edgeInv S hclosed d).1 = B.edgeInv d.1
    rw [restrictedPerm_apply]
  · intro d
    rfl
  · intro d
    have hchar := firstReturn_characterization B.rot S d
    refine ⟨firstReturnTime B.rot S d, (firstReturnTime_spec B.rot S d).1,
      ?_, ?_⟩
    · change (B.rot : D → D)^[firstReturnTime B.rot S d] d.1 =
        (firstReturn B.rot S d : D)
      exact hchar.1
    · intro j hj hjk hmem
      have hjS : (B.rot : D → D)^[j] d.1 ∈ S := by
        obtain ⟨e, he⟩ := hmem
        rw [← he]
        exact e.2
      exact hchar.2 j hj hjk hjS

/-- A dart and its base-face successor in a closed half have the same
face-successor step in the half map. Helper toward `lem-lr-ind` -/
theorem closedHalf_faceSucc_eq {D : Type*} [Fintype D] [DecidableEq D]
    (B : DirectedMapWithMissing D) (S : Set D)
    [DecidablePred (fun d : D => d ∈ S)]
    (hclosed : ∀ d : D, d ∈ S → B.edgeInv d ∈ S)
    (d : {d : D // d ∈ S})
    (hface : B.toCombinatorialMap.faceSucc d.1 ∈ S) :
    (closedHalfCombinatorialMap B S hclosed).faceSucc d =
      ⟨B.toCombinatorialMap.faceSucc d.1, hface⟩ := by
  apply Subtype.ext
  let e : {d : D // d ∈ S} := ⟨B.edgeInv d.1, hclosed d.1 d.2⟩
  have hprev : B.toCombinatorialMap.rot.symm e.1 ∈ S := by
    simpa [e, CombinatorialMap.faceSucc] using hface
  change ((firstReturnPerm B.rot S).symm
      (restrictedPerm B.edgeInv S hclosed d)).1 =
    B.toCombinatorialMap.faceSucc d.1
  rw [restrictedPerm_apply]
  change ((firstReturnPerm B.rot S).symm e).1 =
    B.toCombinatorialMap.rot.symm e.1
  exact firstReturnPerm_symm_apply_of_mem B.rot S e hprev

/-- The left half face-successor agrees with the original map whenever the
dart and its next dart lie in the left half. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalf_faceSucc_eq {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {d : D} (hd : d ∈ pathCutLeftHalfDarts B P)
    (hface : B.map.toCombinatorialMap.faceSucc d ∈ pathCutLeftHalfDarts B P) :
    (pathCutLeftHalfMap B P).faceSucc ⟨d, hd⟩ =
      ⟨B.map.toCombinatorialMap.faceSucc d, hface⟩ := by
  exact closedHalf_faceSucc_eq B.map (pathCutLeftHalfDarts B P)
    (fun x hx => pathCutLeftHalf_edgeInv_mem B P hx) ⟨d, hd⟩ hface

/-- The right half face-successor agrees with the original map whenever the
dart and its next dart lie in the right half. Helper toward `lem-lr-ind` -/
theorem pathCutRightHalf_faceSucc_eq {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {d : D} (hd : d ∈ pathCutRightHalfDarts B P)
    (hface : B.map.toCombinatorialMap.faceSucc d ∈ pathCutRightHalfDarts B P) :
    (pathCutRightHalfMap B P).faceSucc ⟨d, hd⟩ =
      ⟨B.map.toCombinatorialMap.faceSucc d, hface⟩ := by
  exact closedHalf_faceSucc_eq B.map (pathCutRightHalfDarts B P)
    (fun x hx => pathCutRightHalf_edgeInv_mem B P hx) ⟨d, hd⟩ hface

/-- On a subset containing an entire face cycle, iteration of the half-map
face permutation agrees with iteration of the original face permutation.
paper result. -/
theorem closedHalf_faceSucc_iterate_eq {D : Type*} [Fintype D]
    [DecidableEq D] (B : DirectedMapWithMissing D) (S : Set D)
    [DecidablePred (fun d : D => d ∈ S)]
    (hclosed : ∀ d : D, d ∈ S → B.edgeInv d ∈ S)
    (d : {d : D // d ∈ S})
    (hwhole : ∀ e : D,
      Equiv.Perm.SameCycle B.toCombinatorialMap.faceSucc d.1 e → e ∈ S)
    (k : ℕ) :
    ((closedHalfCombinatorialMap B S hclosed).faceSucc : _ → _)^[k] d =
      ⟨(B.toCombinatorialMap.faceSucc : D → D)^[k] d.1,
        hwhole _ (by
          refine ⟨(k : ℤ), ?_⟩
          simp only [zpow_natCast]
          rw [← perm_iterate_eq_pow])⟩ := by
  have hcycle (m : ℕ) :
      Equiv.Perm.SameCycle B.toCombinatorialMap.faceSucc d.1
        ((B.toCombinatorialMap.faceSucc : D → D)^[m] d.1) := by
    refine ⟨(m : ℤ), ?_⟩
    simp only [zpow_natCast]
    rw [← perm_iterate_eq_pow]
  induction k with
  | zero =>
      apply Subtype.ext
      rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      let e : {x : D // x ∈ S} :=
        ⟨(B.toCombinatorialMap.faceSucc : D → D)^[k] d.1, hwhole _ (hcycle k)⟩
      have hnext : B.toCombinatorialMap.faceSucc e.1 ∈ S := by
        simpa [e, Function.iterate_succ_apply'] using hwhole _ (hcycle (k + 1))
      rw [closedHalf_faceSucc_eq B S hclosed e hnext]
      apply Subtype.ext
      simp [e, Function.iterate_succ_apply']

/-- The complete face orbit of a left-half dart is the same in the left half
map and the original map whenever that entire original face lies in the left
half. With whole-face containment, no separate inner or off-seam assumption is
the paper result. -/
theorem pathCutLeftHalf_faceOrbit_iff {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P})
    (hwhole : ∀ e : D,
      Equiv.Perm.SameCycle B.map.toCombinatorialMap.faceSucc d.1 e →
        e ∈ pathCutLeftHalfDarts B P)
    (e : {e : D // e ∈ pathCutLeftHalfDarts B P}) :
    Equiv.Perm.SameCycle (pathCutLeftHalfMap B P).faceSucc d e ↔
      Equiv.Perm.SameCycle B.map.toCombinatorialMap.faceSucc d.1 e.1 := by
  constructor
  · intro h
    obtain ⟨k, hk, hpow⟩ := h.exists_pow_eq'
    have hiter : ((pathCutLeftHalfMap B P).faceSucc : _ → _)^[k] d = e := by
      simpa only [perm_iterate_eq_pow] using hpow
    have hval := congrArg Subtype.val hiter
    change (((closedHalfCombinatorialMap B.map (pathCutLeftHalfDarts B P)
      (fun x hx => pathCutLeftHalf_edgeInv_mem B P hx)).faceSucc : _ → _)^[k] d).1 =
        e.1 at hval
    rw [closedHalf_faceSucc_iterate_eq B.map (pathCutLeftHalfDarts B P)
      (fun x hx => pathCutLeftHalf_edgeInv_mem B P hx) d hwhole k] at hval
    have hcycle : Equiv.Perm.SameCycle B.map.toCombinatorialMap.faceSucc d.1
        ((B.map.toCombinatorialMap.faceSucc : D → D)^[k] d.1) := by
      refine ⟨(k : ℤ), ?_⟩
      simp only [zpow_natCast]
      rw [← perm_iterate_eq_pow]
    exact hcycle.trans (hval.sameCycle B.map.toCombinatorialMap.faceSucc)
  · intro h
    obtain ⟨k, hk, hpow⟩ := h.exists_pow_eq'
    have hiter : (B.map.toCombinatorialMap.faceSucc : D → D)^[k] d.1 = e.1 := by
      simpa only [perm_iterate_eq_pow] using hpow
    have hhalfIter := closedHalf_faceSucc_iterate_eq B.map
      (pathCutLeftHalfDarts B P)
      (fun x hx => pathCutLeftHalf_edgeInv_mem B P hx) d hwhole k
    have hiter' : ((pathCutLeftHalfMap B P).faceSucc : _ → _)^[k] d = e := by
      change ((closedHalfCombinatorialMap B.map (pathCutLeftHalfDarts B P)
        (fun x hx => pathCutLeftHalf_edgeInv_mem B P hx)).faceSucc : _ → _)^[k] d = e
      rw [hhalfIter]
      apply Subtype.ext
      exact hiter
    refine ⟨(k : ℤ), ?_⟩
    simp only [zpow_natCast]
    rw [← perm_iterate_eq_pow]
    exact hiter'

/-- The image of the left-half face orbit is exactly the original face orbit
when the whole original face lies in the left half. Helper toward `lem-lr-ind`,
not the paper result. -/
theorem pathCutLeftHalf_faceOrbit_image_eq {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P})
    (hwhole : ∀ e : D,
      Equiv.Perm.SameCycle B.map.toCombinatorialMap.faceSucc d.1 e →
        e ∈ pathCutLeftHalfDarts B P) :
    {e : D | Equiv.Perm.SameCycle B.map.toCombinatorialMap.faceSucc d.1 e} =
      {e : D | ∃ f : {x : D // x ∈ pathCutLeftHalfDarts B P},
        f.1 = e ∧ Equiv.Perm.SameCycle (pathCutLeftHalfMap B P).faceSucc d f} := by
  ext e
  constructor
  · intro he
    have heS : e ∈ pathCutLeftHalfDarts B P := hwhole e he
    refine ⟨⟨e, heS⟩, rfl, ?_⟩
    exact (pathCutLeftHalf_faceOrbit_iff B P d hwhole ⟨e, heS⟩).2 he
  · rintro ⟨f, rfl, hf⟩
    exact (pathCutLeftHalf_faceOrbit_iff B P d hwhole f).1 hf

/-- The left half inclusion satisfies the unrooted induced-embedding fields.
paper result. -/
theorem pathCutLeftHalf_embedding_fields {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    Function.Injective (fun d : {d : D // d ∈ pathCutLeftHalfDarts B P} => d.1) ∧
      (∀ d, ((pathCutLeftHalfDirectedMap B P).edgeInv d).1 =
        B.map.toCombinatorialMap.edgeInv d.1) ∧
      (∀ d, (pathCutLeftHalfDirectedMap B P).tail d ↔ B.map.tail d.1) ∧
      (∀ d, ∃ k : ℕ, 0 < k ∧
        (B.map.toCombinatorialMap.rot : D → D)^[k] d.1 =
          ((pathCutLeftHalfDirectedMap B P).rot d).1 ∧
        ∀ j : ℕ, 0 < j → j < k →
          (B.map.toCombinatorialMap.rot : D → D)^[j] d.1 ∉
            Set.range (fun e : {d : D // d ∈ pathCutLeftHalfDarts B P} => e.1)) := by
  exact closedHalfEmbeddingFields B.map (pathCutLeftHalfDarts B P)
    (fun d hd => pathCutLeftHalf_edgeInv_mem B P hd)
    (fun d hd => B.noMissingDarts d) (pathCutLeftHalfDarts_nonempty B P)

/-- The right half inclusion satisfies the unrooted induced-embedding fields.
paper result. -/
theorem pathCutRightHalf_embedding_fields {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    Function.Injective (fun d : {d : D // d ∈ pathCutRightHalfDarts B P} => d.1) ∧
      (∀ d, ((pathCutRightHalfDirectedMap B P).edgeInv d).1 =
        B.map.toCombinatorialMap.edgeInv d.1) ∧
      (∀ d, (pathCutRightHalfDirectedMap B P).tail d ↔ B.map.tail d.1) ∧
      (∀ d, ∃ k : ℕ, 0 < k ∧
        (B.map.toCombinatorialMap.rot : D → D)^[k] d.1 =
          ((pathCutRightHalfDirectedMap B P).rot d).1 ∧
        ∀ j : ℕ, 0 < j → j < k →
          (B.map.toCombinatorialMap.rot : D → D)^[j] d.1 ∉
            Set.range (fun e : {d : D // d ∈ pathCutRightHalfDarts B P} => e.1)) := by
  exact closedHalfEmbeddingFields B.map (pathCutRightHalfDarts B P)
    (fun d hd => pathCutRightHalf_edgeInv_mem B P hd)
    (fun d hd => B.noMissingDarts d) (pathCutRightHalfDarts_nonempty B P)

end DirectedDistances.PlanarMap
