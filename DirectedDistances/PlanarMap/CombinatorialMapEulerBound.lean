/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlanarFaceCycleSpace
public import DirectedDistances.PlanarMap.CombinatorialMap

/-! # Euler characteristic bound for connected combinatorial maps

bound for combinatorial maps; not the paper result.

The boundary and dimension facts in `PlanarFaceCycleSpace` are independent of
planarity except for its final range-equals-cycle-space result. The composite
`vertexBoundary_faceBoundary` vanishes and
`faceBoundary_range_le_cycleSpace` holds for every map.
`faceBoundary_eq_zero_iff_connected` and `faceBoundary_eq_iff` characterize
the face-boundary kernel for connected maps; the corresponding dimension
formula is `faceBoundary_finrank_range_connected`. The connected vertex-rank
facts are `coboundary_finrank_range_connected` and
`vertexBoundary_finrank_range_connected`. Finally,
`cycleSpace_finrank_connected` states the additive form of
`dim cycleSpace = E - V + 1` for connected maps with at least one dart. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]

noncomputable section ZModTwoField

local instance : Field (ZMod 2) :=
  Field.ofIsUnitOrEqZero (by
    intro a
    have hval : a.val = 0 ∨ a.val = 1 := by
      have hlt := ZMod.val_lt a
      omega
    rcases hval with hzero | hone
    · right
      apply ZMod.val_injective 2
      simpa using hzero
    · left
      have ha : a = 1 := by
        apply ZMod.val_injective 2
        rw [ZMod.val_one_eq_one_mod]
        omega
      rw [ha]
      exact isUnit_one
  )

/-- bound for combinatorial maps; not the paper result. A connected map with a
nonempty dart set has Euler characteristic at most two. -/
theorem eulerChar_le_two_of_isConnected (M : CombinatorialMap D)
    [Nonempty D] (hM : M.IsConnected) : M.eulerChar ≤ 2 := by
  classical
  have hrange :
      Module.finrank (ZMod 2) (LinearMap.range (faceBoundary M)) ≤
        Module.finrank (ZMod 2) (cycleSpace M) :=
    Submodule.finrank_mono (faceBoundary_range_le_cycleSpace M)
  have hface := faceBoundary_finrank_range_connected M hM
  have hcycle := cycleSpace_finrank_connected M hM ‹Nonempty D›
  have hFpos : 0 < M.numFaces := by
    obtain ⟨d⟩ := ‹Nonempty D›
    change 0 < Fintype.card (CombinatorialMap.FaceQuotient M)
    exact Fintype.card_pos_iff.mpr ⟨faceClass M d⟩
  have hF : M.numFaces =
      Module.finrank (ZMod 2) (LinearMap.range (faceBoundary M)) + 1 := by
    omega
  have hNat : M.numVertices + M.numFaces ≤ M.numEdges + 2 := by
    omega
  unfold CombinatorialMap.eulerChar
  omega

/-- bound for combinatorial maps; not the paper result. If two connected maps have
Euler characteristics summing to four, both are planar. -/
theorem isPlanar_of_eulerChar_sum
    {D₁ D₂ : Type*} [Fintype D₁] [DecidableEq D₁]
    [Fintype D₂] [DecidableEq D₂]
    (M₁ : CombinatorialMap D₁) (M₂ : CombinatorialMap D₂)
    [Nonempty D₁] [Nonempty D₂]
    (h₁ : M₁.IsConnected) (h₂ : M₂.IsConnected)
    (hsum : M₁.eulerChar + M₂.eulerChar = 4) :
    M₁.IsPlanar ∧ M₂.IsPlanar := by
  have hχ₁ := eulerChar_le_two_of_isConnected M₁ h₁
  have hχ₂ := eulerChar_le_two_of_isConnected M₂ h₂
  have hχ₁eq : M₁.eulerChar = 2 := by omega
  have hχ₂eq : M₂.eulerChar = 2 := by omega
  exact ⟨⟨h₁, hχ₁eq⟩, ⟨h₂, hχ₂eq⟩⟩

/-- bound for combinatorial maps; not the paper result. For a connected map with a
nonempty dart set, Euler characteristic two is equivalent to equality of the
face-boundary range and the cycle space. -/
theorem eulerChar_eq_two_iff_range_faceBoundary_eq_cycleSpace
    (M : CombinatorialMap D) [Nonempty D] (hM : M.IsConnected) :
    M.eulerChar = 2 ↔
      LinearMap.range (faceBoundary M) = cycleSpace M := by
  classical
  have hFpos : 0 < M.numFaces := by
    obtain ⟨d⟩ := ‹Nonempty D›
    change 0 < Fintype.card (CombinatorialMap.FaceQuotient M)
    exact Fintype.card_pos_iff.mpr ⟨faceClass M d⟩
  have hface := faceBoundary_finrank_range_connected M hM
  have hcycle := cycleSpace_finrank_connected M hM ‹Nonempty D›
  have hF : M.numFaces =
      Module.finrank (ZMod 2) (LinearMap.range (faceBoundary M)) + 1 := by
    omega
  constructor
  · intro hχ
    have hEuler : M.numVertices + M.numFaces = M.numEdges + 2 := by
      have hχ' : (M.numVertices : ℤ) - M.numEdges + M.numFaces = 2 := by
        simpa [CombinatorialMap.eulerChar] using hχ
      omega
    have hdim :
        Module.finrank (ZMod 2) (LinearMap.range (faceBoundary M)) =
          Module.finrank (ZMod 2) (cycleSpace M) := by
      omega
    exact Submodule.eq_of_le_of_finrank_eq
      (faceBoundary_range_le_cycleSpace M) hdim
  · intro hrange
    have hdim :
        Module.finrank (ZMod 2) (LinearMap.range (faceBoundary M)) =
          Module.finrank (ZMod 2) (cycleSpace M) :=
      congrArg (fun S : Submodule (ZMod 2) (EdgeSpace M) =>
        Module.finrank (ZMod 2) S) hrange
    have hEuler : M.numVertices + M.numFaces = M.numEdges + 2 := by
      omega
    unfold CombinatorialMap.eulerChar
    omega

end ZModTwoField

end DirectedDistances.PlanarMap
