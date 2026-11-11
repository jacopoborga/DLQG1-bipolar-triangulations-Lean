/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.GeneralPlaneMapSides



















public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

variable {V E : Type*}

/-- Helper toward Definition 1.1: reversing a loop negates its winding
number, by reversing the continuous logarithm lift. -/
theorem hasWinding_symm {z : ℂ} (L : Path z z) (w : ℂ) (n : ℤ)
    (h : HasWinding L w n) : HasWinding L.symm w (-n) := by
  obtain ⟨φ, hφ, hinc⟩ := h
  refine ⟨φ.comp (⟨σ, unitInterval.continuous_symm⟩ : C(I, I)), ?_, ?_⟩
  · intro t
    change Complex.exp (φ (σ t)) = L (σ t) - w
    exact hφ (σ t)
  · change φ (σ 1) - φ (σ 0) = _
    rw [unitInterval.symm_one, unitInterval.symm_zero]
    calc
      φ 0 - φ 1 = -(φ 1 - φ 0) := by ring
      _ = -(2 * Real.pi * Complex.I * n) := congrArg Neg.neg hinc
      _ = 2 * Real.pi * Complex.I * ((-n : ℤ) : ℂ) := by
        push_cast
        ring

/-- Helper toward Definition 1.1: reparameterizing a loop by an endpoint-
fixing homeomorphism of the unit interval preserves its winding number. -/
theorem hasWinding_reparam_iff {z : ℂ} (L : Path z z) (w : ℂ) (n : ℤ)
    (e : I ≃ₜ I) (he0 : e 0 = 0) (he1 : e 1 = 1) :
    HasWinding (L.reparam e e.continuous_toFun he0 he1) w n ↔
      HasWinding L w n := by
  have hinv0 : e.symm 0 = 0 := by
    calc
      e.symm 0 = e.symm (e 0) := congrArg e.symm he0.symm
      _ = 0 := e.symm_apply_apply 0
  have hinv1 : e.symm 1 = 1 := by
    calc
      e.symm 1 = e.symm (e 1) := congrArg e.symm he1.symm
      _ = 1 := e.symm_apply_apply 1
  constructor
  · rintro ⟨φ, hφ, hinc⟩
    refine ⟨φ.comp (⟨e.symm, e.symm.continuous⟩ : C(I, I)), ?_, ?_⟩
    · intro t
      change Complex.exp (φ (e.symm t)) = L t - w
      have ht := hφ (e.symm t)
      dsimp [Path.reparam] at ht
      simpa only [Function.comp_apply, e.apply_symm_apply] using ht
    · change φ (e.symm 1) - φ (e.symm 0) = _
      rw [hinv1, hinv0]
      exact hinc
  · rintro ⟨φ, hφ, hinc⟩
    refine ⟨φ.comp (⟨e, e.continuous⟩ : C(I, I)), ?_, ?_⟩
    · intro t
      change Complex.exp (φ (e t)) = L (e t) - w
      have ht := hφ (e t)
      simpa only [Path.reparam, Function.comp_apply] using ht
    · change φ (e 1) - φ (e 0) = _
      rw [he1, he0]
      exact hinc

namespace PlaneGraphDrawing

variable (D : PlaneGraphDrawing V E)

/-- Helper toward Definition 1.1: a face is on the left of a geometric edge
when the winding-side test holds at every interior parameter of its stored
parameterization. -/
@[expose] def SideLeftOf (F : D.Face) (e : E) : Prop :=
  ∀ s : {t : I // t ∈ openParams}, LeftAtOn F.val (D.arc e) s

/-- Helper toward Definition 1.1: a face is on the right of a geometric edge
when the winding-side test holds at every interior parameter of its stored
parameterization. -/
@[expose] def SideRightOf (F : D.Face) (e : E) : Prop :=
  ∀ s : {t : I // t ∈ openParams}, RightAtOn F.val (D.arc e) s

/-- Helper toward Definition 1.1: count the left and right winding sides of a
geometric edge, with both sides counted when the same face borders both. -/
@[expose] noncomputable def sideMult (e : E) (F : D.Face) : ℕ∞ := by
  classical
  exact (if D.SideLeftOf F e then 1 else 0) +
    (if D.SideRightOf F e then 1 else 0)

/-- Helper toward Definition 1.1: the side degree is the supremum of the
finite partial sums of all geometric edge multiplicities. -/
@[expose] def sideDegree (F : D.Face) : ℕ∞ :=
  ⨆ s : Finset E, ∑ e ∈ s, D.sideMult e F

end PlaneGraphDrawing

/-- Helper toward Definition 1.1: every internal face has side degree three,
and the directed map is bipolar. -/
@[expose] def DirectedPlaneMap.IsBipolarTriangulationBySides
    (M : DirectedPlaneMap V E) : Prop :=
  M.IsBipolar ∧ ∀ F : M.toPlaneGraphDrawing.Face,
    M.toPlaneGraphDrawing.IsInternal F →
      M.toPlaneGraphDrawing.sideDegree F = 3

namespace PlaneGraphDrawing

/-- Helper toward Definition 1.1: one edge contributes at most two sides. -/
theorem sideMult_le_two (D : PlaneGraphDrawing V E) (e : E)
    (F : D.Face) : D.sideMult e F ≤ 2 := by
  classical
  unfold sideMult
  split_ifs <;> norm_num

/-- Helper toward Definition 1.1: side multiplicity is one of zero, one, or
two. -/
theorem sideMult_eq_zero_or_one_or_two (D : PlaneGraphDrawing V E)
    (e : E) (F : D.Face) :
    D.sideMult e F = 0 ∨ D.sideMult e F = 1 ∨ D.sideMult e F = 2 := by
  classical
  unfold sideMult
  by_cases hl : D.SideLeftOf F e <;> by_cases hr : D.SideRightOf F e <;>
    simp [hl, hr]; norm_num

end PlaneGraphDrawing

end DirectedDistances.PlanarMap

end
