/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.GeneralPlaneMap
public import DirectedDistances.PlanarMap.GeneralPlaneMapSideDegree

/-! # Finite support for plane-map degrees

Helpers toward Definitions 1.1 and 5.8: finite support of geometric edge
multiplicity reduces the supremum of finite partial sums to one finite sum. -/

public section

namespace DirectedDistances.PlanarMap

open scoped ENNReal

private theorem enat_iSup_finset_sum_eq_sum_of_support
    {E : Type*} (f : E → ℕ∞) (S : Finset E)
    (hzero : ∀ e, e ∉ S → f e = 0) :
    (⨆ s : Finset E, ∑ e ∈ s, f e) = ∑ e ∈ S, f e := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro s
    calc
      (∑ e ∈ s, f e) = ∑ e ∈ s ∩ S, f e := by
        symm
        apply Finset.sum_subset Finset.inter_subset_left
        intro e he hnot
        apply hzero e
        intro heS
        exact hnot (Finset.mem_inter.mpr ⟨he, heS⟩)
      _ ≤ ∑ e ∈ S, f e :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          (by intro e heS heNot; exact bot_le)
  · exact le_iSup_of_le S le_rfl

namespace PlaneGraphDrawing

variable {V E : Type*}

/-- Helper toward Definitions 1.1 and 5.8: if all edge multiplicities outside
a finite set vanish, the face degree is the sum over that set. -/
theorem faceDegree_eq_sum_of_support
    (D : PlaneGraphDrawing V E) (F : D.Face) (S : Finset E)
    (hzero : ∀ e, e ∉ S → D.faceMult e F = 0) :
    D.faceDegree F = ∑ e ∈ S, D.faceMult e F := by
  exact enat_iSup_finset_sum_eq_sum_of_support
    (fun e => D.faceMult e F) S hzero

/-- Helper toward Definitions 1.1 and 5.8: if each edge in a finite set has
multiplicity one and every other edge has multiplicity zero, the face degree
is the cardinality of that set. -/
theorem faceDegree_eq_finset_card
    [DecidableEq E] (D : PlaneGraphDrawing V E) (F : D.Face) (S : Finset E)
    (h : ∀ e : E, D.faceMult e F = if e ∈ S then (1 : ℕ∞) else 0) :
    D.faceDegree F = (S.card : ℕ∞) := by
  classical
  rw [D.faceDegree_eq_sum_of_support F S (by
    intro e he
    rw [h e]
    simp [he])]
  simp [h]

/-- Helper toward Definitions 1.1 and 5.8: three distinct edges of
multiplicity one, with all other edge multiplicities zero, give face degree
three. -/
theorem faceDegree_eq_three_of_injective
    [DecidableEq E] (D : PlaneGraphDrawing V E) (F : D.Face) (edges : Fin 3 → E)
    (hinj : Function.Injective edges)
    (h : ∀ e : E, D.faceMult e F =
      if ∃ i : Fin 3, edges i = e then (1 : ℕ∞) else 0) :
    D.faceDegree F = 3 := by
  classical
  let S := Finset.univ.image edges
  have hcard : S.card = 3 := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hmult : ∀ e : E, D.faceMult e F =
      if e ∈ S then (1 : ℕ∞) else 0 := by
    intro e
    simpa [S] using h e
  rw [D.faceDegree_eq_finset_card F S hmult, hcard]
  rfl









end PlaneGraphDrawing

end DirectedDistances.PlanarMap
