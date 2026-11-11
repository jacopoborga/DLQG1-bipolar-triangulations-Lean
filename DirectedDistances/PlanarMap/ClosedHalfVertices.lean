/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlanarPathCutHalfMap

/-! # Vertex counts for closed halves

paper result. This module identifies the vertices of a closed half with the
original rotation cycles that meet its dart carrier. -/

public section
namespace DirectedDistances.PlanarMap

open Equiv

/-- First return preserves rotation-cycle equivalence on the restricted
not the paper result. -/
theorem firstReturnPerm_sameCycle_iff {α : Type*} [Fintype α]
    [DecidableEq α] (σ : Equiv.Perm α) (S : Set α)
    [DecidablePred (fun y : α => y ∈ S)] {x y : S} :
    Equiv.Perm.SameCycle (firstReturnPerm σ S) x y ↔
      Equiv.Perm.SameCycle σ x.1 y.1 := by
  constructor
  · intro hxy
    let ρ := firstReturnPerm σ S
    have hstep (z : S) : Equiv.Perm.SameCycle σ z.1 (ρ z).1 := by
      refine ⟨(firstReturnTime σ S z : ℤ), ?_⟩
      rw [zpow_natCast, ← perm_iterate_eq_pow]
      exact (firstReturn_characterization σ S z).1
    have hiter (k : ℕ) (z : S) :
        Equiv.Perm.SameCycle σ z.1 ((ρ : S → S)^[k] z).1 := by
      induction k with
      | zero => exact Equiv.Perm.SameCycle.refl _ _
      | succ k ih =>
          rw [Function.iterate_succ_apply']
          exact ih.trans (hstep ((ρ : S → S)^[k] z))
    obtain ⟨k, _hk, hpow⟩ := hxy.exists_pow_eq'
    have hiter_eq : (ρ ^ k) x = y := by
      simpa only [perm_iterate_eq_pow] using hpow
    have hval : ((ρ : S → S)^[k] x).1 = y.1 := congrArg Subtype.val hiter_eq
    have hlast : Equiv.Perm.SameCycle σ ((ρ : S → S)^[k] x).1 y.1 := by
      rw [hval]
    exact (hiter k x).trans hlast
  · intro hxy
    let ρ := firstReturnPerm σ S
    have hstrong : ∀ k : ℕ, ∀ x y : S,
        (σ : α → α)^[k] x.1 = y.1 →
          Equiv.Perm.SameCycle ρ x y := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
          intro x y hxy
          by_cases hk : k = 0
          · subst k
            have hval : x.1 = y.1 := by simpa using hxy
            have hsub : x = y := Subtype.ext hval
            simpa [hsub] using (Equiv.Perm.SameCycle.refl ρ x)
          · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
            have hret : (σ : α → α)^[k] x.1 ∈ S := by
              rw [hxy]
              exact y.2
            let t := firstReturnTime σ S x
            have htpos := (firstReturnTime_spec σ S x).1
            have htle : t ≤ k := firstReturnTime_min σ S x hkpos hret
            by_cases htk : t = k
            · have hreturn : (firstReturn σ S x).1 = y.1 := by
                calc
                  (firstReturn σ S x).1 = (σ : α → α)^[t] x.1 :=
                    (firstReturn_characterization σ S x).1.symm
                  _ = (σ : α → α)^[k] x.1 := by rw [htk]
                  _ = y.1 := hxy
              have hcycle : ρ x = y := Subtype.ext hreturn
              refine ⟨(1 : ℤ), ?_⟩
              simp [hcycle]
            · have htk' : t < k := Nat.lt_of_le_of_ne htle htk
              let z := firstReturn σ S x
              have hnext : (σ : α → α)^[k - t] z.1 = y.1 := by
                calc
                  (σ : α → α)^[k - t] z.1 =
                      (σ : α → α)^[k - t] ((σ : α → α)^[t] x.1) := by
                        exact congrArg (fun q : α => (σ : α → α)^[k - t] q)
                          (firstReturn_characterization σ S x).1.symm
                  _ = (σ : α → α)^[(k - t) + t] x.1 :=
                        (Function.iterate_add_apply (σ : α → α) (k - t) t x.1).symm
                  _ = (σ : α → α)^[k] x.1 := by
                        congr 1
                        omega
                  _ = y.1 := hxy
              have hrecursive := ih (k - t) (by omega) z y hnext
              have hstep : Equiv.Perm.SameCycle ρ x z := by
                refine ⟨(1 : ℤ), ?_⟩
                simp [ρ, z, firstReturnPerm]
              exact hstep.trans hrecursive
    obtain ⟨k, _hk, hpow⟩ := hxy.exists_pow_eq'
    have hiterEq : (σ : α → α)^[k] x.1 = y.1 := by
      simpa only [perm_iterate_eq_pow] using hpow
    change Equiv.Perm.SameCycle ρ x y
    exact hstrong k x y hiterEq

/-- The map from closed-half rotation cycles to original rotation cycles,
induced by dart inclusion. Helper toward `lem-lr-ind` -/
@[expose] noncomputable def closedHalfVertexMap {D : Type*}
    [Fintype D] [DecidableEq D] (B : DirectedMapWithMissing D)
    (S : Set D) [DecidablePred (fun d : D => d ∈ S)]
    (hclosed : ∀ d : D, d ∈ S → B.edgeInv d ∈ S) :
    CombinatorialMap.VertexQuotient (closedHalfCombinatorialMap B S hclosed) →
      CombinatorialMap.VertexQuotient B.toCombinatorialMap :=
  Quotient.map Subtype.val (by
    intro a b hab
    exact (firstReturnPerm_sameCycle_iff B.rot S).mp hab)

/-- Inclusion of a closed-half vertex quotient into the original vertex
quotient is injective. Helper toward `lem-lr-ind` -/
theorem closedHalfVertexMap_injective {D : Type*}
    [Fintype D] [DecidableEq D] (B : DirectedMapWithMissing D)
    (S : Set D) [DecidablePred (fun d : D => d ∈ S)]
    (hclosed : ∀ d : D, d ∈ S → B.edgeInv d ∈ S) :
    Function.Injective (closedHalfVertexMap B S hclosed) := by
  intro v w hvw
  revert hvw
  refine Quotient.inductionOn₂ v w ?_
  intro a b hab
  apply Quotient.sound
  apply (firstReturnPerm_sameCycle_iff B.rot S).2
  change Quotient.mk (Equiv.Perm.SameCycle.setoid B.rot) a.1 =
    Quotient.mk (Equiv.Perm.SameCycle.setoid B.rot) b.1 at hab
  exact Quotient.exact hab

/-- The image of the closed-half vertex map consists exactly of the original
vertices represented by a dart in `S`. Helper toward `lem-lr-ind` -/
theorem closedHalfVertexMap_range {D : Type*}
    [Fintype D] [DecidableEq D] (B : DirectedMapWithMissing D)
    (S : Set D) [DecidablePred (fun d : D => d ∈ S)]
    (hclosed : ∀ d : D, d ∈ S → B.edgeInv d ∈ S) :
    Set.range (closedHalfVertexMap B S hclosed) =
      {v : CombinatorialMap.VertexQuotient B.toCombinatorialMap |
        ∃ d : D, d ∈ S ∧
          Quotient.mk (Equiv.Perm.SameCycle.setoid B.rot) d = v} := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    refine Quotient.inductionOn w ?_
    intro d
    exact ⟨d.1, d.2, rfl⟩
  · rintro ⟨d, hd, hv⟩
    refine ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid
      (closedHalfCombinatorialMap B S hclosed).rot) ⟨d, hd⟩, ?_⟩
    change Quotient.mk (Equiv.Perm.SameCycle.setoid B.rot) d = v
    exact hv

/-- The closed-half vertex count is the number of original rotation cycles
meeting its dart carrier. Helper toward `lem-lr-ind` -/
theorem closedHalf_numVertices_eq_card {D : Type*}
    [Fintype D] [DecidableEq D] (B : DirectedMapWithMissing D)
    (S : Set D) [DecidablePred (fun d : D => d ∈ S)]
    (hclosed : ∀ d : D, d ∈ S → B.edgeInv d ∈ S)
    [DecidableRel (Equiv.Perm.SameCycle B.rot)]
    [DecidablePred (fun v : CombinatorialMap.VertexQuotient B.toCombinatorialMap =>
      ∃ d : D, d ∈ S ∧
        Quotient.mk (Equiv.Perm.SameCycle.setoid B.rot) d = v)] :
    (closedHalfCombinatorialMap B S hclosed).numVertices =
      Fintype.card {v : CombinatorialMap.VertexQuotient B.toCombinatorialMap //
        ∃ d : D, d ∈ S ∧
          Quotient.mk (Equiv.Perm.SameCycle.setoid B.rot) d = v} := by
  classical
  let f : CombinatorialMap.VertexQuotient (closedHalfCombinatorialMap B S hclosed) →
      {v : CombinatorialMap.VertexQuotient B.toCombinatorialMap //
        ∃ d : D, d ∈ S ∧
          Quotient.mk (Equiv.Perm.SameCycle.setoid B.rot) d = v} :=
    fun v => ⟨closedHalfVertexMap B S hclosed v, by
      have hm : closedHalfVertexMap B S hclosed v ∈
          Set.range (closedHalfVertexMap B S hclosed) := ⟨v, rfl⟩
      rw [closedHalfVertexMap_range B S hclosed] at hm
      exact hm⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w hvw
      apply closedHalfVertexMap_injective B S hclosed
      exact congrArg Subtype.val hvw
    · intro v
      obtain ⟨d, hdS, hdv⟩ := v.2
      refine ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid
        (closedHalfCombinatorialMap B S hclosed).rot) ⟨d, hdS⟩, ?_⟩
      apply Subtype.ext
      exact hdv
  calc
    (closedHalfCombinatorialMap B S hclosed).numVertices =
        Fintype.card (CombinatorialMap.VertexQuotient
          (closedHalfCombinatorialMap B S hclosed)) := rfl
    _ = Fintype.card {v : CombinatorialMap.VertexQuotient B.toCombinatorialMap //
        ∃ d : D, d ∈ S ∧
          Quotient.mk (Equiv.Perm.SameCycle.setoid B.rot) d = v} :=
      Fintype.card_congr (Equiv.ofBijective f hf)

/-- The left path-cut half has as many vertices as original rotation cycles
meeting its dart carrier. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalfMap_numVertices {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    [DecidableRel (Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot)]
    [DecidablePred (fun v : CombinatorialMap.VertexQuotient
      B.map.toCombinatorialMap => ∃ d : D,
        d ∈ pathCutLeftHalfDarts B P ∧
          Quotient.mk (Equiv.Perm.SameCycle.setoid
            B.map.toCombinatorialMap.rot) d = v)] :
    (pathCutLeftHalfMap B P).numVertices =
      Fintype.card {v : CombinatorialMap.VertexQuotient
        B.map.toCombinatorialMap // ∃ d : D,
          d ∈ pathCutLeftHalfDarts B P ∧
            Quotient.mk (Equiv.Perm.SameCycle.setoid
              B.map.toCombinatorialMap.rot) d = v} := by
  simpa [pathCutLeftHalfMap] using
    (closedHalf_numVertices_eq_card B.map (pathCutLeftHalfDarts B P)
      (fun d hd => pathCutLeftHalf_edgeInv_mem B P hd))

/-- The right path-cut half has as many vertices as original rotation cycles
meeting its dart carrier. Helper toward `lem-lr-ind` -/
theorem pathCutRightHalfMap_numVertices {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    [DecidableRel (Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot)]
    [DecidablePred (fun v : CombinatorialMap.VertexQuotient
      B.map.toCombinatorialMap => ∃ d : D,
        d ∈ pathCutRightHalfDarts B P ∧
          Quotient.mk (Equiv.Perm.SameCycle.setoid
            B.map.toCombinatorialMap.rot) d = v)] :
    (pathCutRightHalfMap B P).numVertices =
      Fintype.card {v : CombinatorialMap.VertexQuotient
        B.map.toCombinatorialMap // ∃ d : D,
          d ∈ pathCutRightHalfDarts B P ∧
            Quotient.mk (Equiv.Perm.SameCycle.setoid
              B.map.toCombinatorialMap.rot) d = v} := by
  simpa [pathCutRightHalfMap] using
    (closedHalf_numVertices_eq_card B.map (pathCutRightHalfDarts B P)
      (fun d hd => pathCutRightHalf_edgeInv_mem B P hd))

end DirectedDistances.PlanarMap
