/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Homeomorph.Defs

/-! # Complementary component transfer

Helpers toward Theorem 1.4 (Q-M0-repr drawing: complementary components transfer between
agreeing drawings); not a paper result. -/

public section

open Set Topology

namespace DirectedDistances.PlanarMap

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: complementary components transfer between
agreeing drawings); not a paper result. -/
theorem connectedComponentIn_compl_eq_of_agree {a : Type*} [TopologicalSpace a]
    [LocallyConnectedSpace a] {X Y A : Set a} (hX : IsClosed X)
    {z : a} (hz : z ∉ X) (hUA : connectedComponentIn Xᶜ z ⊆ A)
    (hXY : X ∩ closure A ⊆ Y) (hYX : Y ∩ A ⊆ X) :
    z ∉ Y ∧ connectedComponentIn Yᶜ z = connectedComponentIn Xᶜ z := by
  let U := connectedComponentIn Xᶜ z
  let V := connectedComponentIn Yᶜ z
  have hzX : z ∈ Xᶜ := by simpa using hz
  have hzU : z ∈ U := mem_connectedComponentIn hzX
  have hUopen : IsOpen U := by
    exact (isOpen_compl_iff.mpr hX).connectedComponentIn
  have hUY : Disjoint U Y := by
    apply disjoint_left.mpr
    intro x hxU hxY
    have hxA : x ∈ A := hUA hxU
    have hxX : x ∈ X := hYX ⟨hxY, hxA⟩
    exact (connectedComponentIn_subset Xᶜ z hxU) hxX
  have hUYc : U ⊆ Yᶜ := by
    intro x hxU
    simpa using (disjoint_left.mp hUY hxU)
  have hzY : z ∉ Y := by
    intro hzY
    exact (disjoint_left.mp hUY) hzU hzY
  have hUV : U ⊆ V := by
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hzU hUYc
  have hFront : frontier U ⊆ Y := by
    intro x hxFront
    have hxClosureU : x ∈ closure U := frontier_subset_closure hxFront
    have hxNotU : x ∉ U := by
      intro hxU
      have hxInterior : x ∈ interior U := by
        simpa [hUopen.interior_eq] using hxU
      exact (mem_frontier_iff_notMem_interior hxU).mp hxFront hxInterior
    have hxX : x ∈ X := by
      by_contra hxNotX
      have hxF : x ∈ Xᶜ := by simpa using hxNotX
      have hxSubtypeClosure :
          (⟨x, hxF⟩ : {x // x ∈ Xᶜ}) ∈
            closure (connectedComponent (⟨z, hzX⟩ : {x // x ∈ Xᶜ})) := by
        rw [closure_subtype]
        simpa [U, connectedComponentIn_eq_image hzX] using hxClosureU
      have hxSubtype :
          (⟨x, hxF⟩ : {x // x ∈ Xᶜ}) ∈
            connectedComponent (⟨z, hzX⟩ : {x // x ∈ Xᶜ}) :=
        isClosed_connectedComponent.closure_subset hxSubtypeClosure
      have hxU' : x ∈ U := by
        change x ∈ connectedComponentIn Xᶜ z
        rw [connectedComponentIn_eq_image hzX]
        exact ⟨⟨x, hxF⟩, hxSubtype, rfl⟩
      exact hxNotU hxU'
    have hxAclosure : x ∈ closure A := closure_mono hUA hxClosureU
    exact hXY ⟨hxX, hxAclosure⟩
  have hVY : V ⊆ Yᶜ := connectedComponentIn_subset Yᶜ z
  have hClosureV : closure U ∩ V ⊆ U := by
    intro x hx
    by_contra hxNotU
    have hxFront : x ∈ frontier U := by
      rw [← closure_sdiff_interior]
      refine ⟨hx.1, ?_⟩
      intro hxInterior
      exact hxNotU (by simpa [hUopen.interior_eq] using hxInterior)
    have hxY : x ∈ Y := hFront hxFront
    exact (hVY hx.2) hxY
  have hVU : V ⊆ U := by
    exact isPreconnected_connectedComponentIn.subset_of_closure_inter_subset
      hUopen ⟨z, mem_connectedComponentIn (by simpa using hzY), hzU⟩ hClosureV
  exact ⟨hzY, subset_antisymm hVU hUV⟩

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: complementary components transfer between
agreeing drawings); not a paper result. A homeomorphism transports components of complements. -/
theorem Homeomorph.image_connectedComponentIn_compl {a b : Type*}
    [TopologicalSpace a] [TopologicalSpace b] (T : a ≃ₜ b) (X : Set a) (z : a) :
    T '' connectedComponentIn Xᶜ z =
      connectedComponentIn (T '' X)ᶜ (T z) := by
  rw [← T.image_compl]
  by_cases hz : z ∈ Xᶜ
  · apply subset_antisymm
    · exact T.continuous.continuousOn.image_connectedComponentIn_subset hz
    · intro y hy
      have hy' : T.symm y ∈ T.symm '' connectedComponentIn (T '' Xᶜ) (T z) :=
        ⟨y, hy, rfl⟩
      have hback :
          T.symm '' connectedComponentIn (T '' Xᶜ) (T z) ⊆
            connectedComponentIn Xᶜ z := by
        have himage : T.symm '' (T '' Xᶜ) = Xᶜ := by
          ext x
          simp
        have h := T.symm.continuous.continuousOn.image_connectedComponentIn_subset
          (mem_image_of_mem T hz)
        simpa only [himage, T.symm_apply_apply] using h
      have hmem : T.symm y ∈ connectedComponentIn Xᶜ z := hback hy'
      exact ⟨T.symm y, hmem, T.apply_symm_apply y⟩
  · rw [connectedComponentIn_eq_empty hz]
    have hz' : T z ∉ T '' Xᶜ := by
      rintro ⟨x, hx, hxy⟩
      apply hz
      exact T.injective hxy ▸ hx
    rw [connectedComponentIn_eq_empty hz']
    simp

end DirectedDistances.PlanarMap
