/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.GeneralPlaneMapEndpointSwap
public import DirectedDistances.PlanarMap.GeneralPlaneMapSideReversal

/-! # Checks for winding-side degree -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval

variable {V E : Type*}

/-- Reversing the stored parameterization exchanges the left-side predicate.
Helper toward Definition 1.1. -/
theorem endpointSwap_sideLeftOf_iff (D : PlaneGraphDrawing V E)
    (swap : E → Bool) (F : D.Face) (e : E) :
    (D.endpointSwap swap).SideLeftOf (D.endpointSwapFace swap F) e ↔
      if swap e then D.SideRightOf F e else D.SideLeftOf F e := by
  by_cases hswap : swap e = true
  · simp only [PlaneGraphDrawing.SideLeftOf, PlaneGraphDrawing.SideRightOf,
      endpointSwapFace_val, PlaneGraphDrawing.endpointSwap,
      PlaneGraphDrawing.endpointSwapArc, dite_eq_left hswap, ite_eq_left hswap]
    constructor
    · intro h s
      let s' : {t : I // t ∈ openParams} :=
        ⟨σ s.1, symm_mem_openParams_iff.mpr s.2⟩
      have hcomp : (s'.1 : ℝ) + (s.1 : ℝ) = 1 := by
        simp only [s', unitInterval.coe_symm_eq]
        ring
      exact (leftAtOn_edge_reversal_iff D F e s s' hcomp).mp (h s')
    · intro h s'
      let s : {t : I // t ∈ openParams} :=
        ⟨σ s'.1, symm_mem_openParams_iff.mpr s'.2⟩
      have hcomp : (s'.1 : ℝ) + (s.1 : ℝ) = 1 := by
        simp only [s, unitInterval.coe_symm_eq]
        ring
      exact (leftAtOn_edge_reversal_iff D F e s s' hcomp).mpr (h s)
  · have hfalse : swap e = false := by
      cases h : swap e with
      | false => rfl
      | true => exact (hswap h).elim
    have hneq : ¬ ((false : Bool) = true) := by decide
    simp only [PlaneGraphDrawing.SideLeftOf, PlaneGraphDrawing.SideRightOf,
      endpointSwapFace_val, PlaneGraphDrawing.endpointSwap,
      PlaneGraphDrawing.endpointSwapArc, hfalse, dite_eq_right hneq,
      ite_eq_right hneq]
    change (∀ s : {t : I // t ∈ openParams}, LeftAtOn F.val (D.arc e) s) ↔ _
    rfl

/-- Reversing the stored parameterization exchanges the right-side predicate.
Helper toward Definition 1.1. -/
theorem endpointSwap_sideRightOf_iff (D : PlaneGraphDrawing V E)
    (swap : E → Bool) (F : D.Face) (e : E) :
    (D.endpointSwap swap).SideRightOf (D.endpointSwapFace swap F) e ↔
      if swap e then D.SideLeftOf F e else D.SideRightOf F e := by
  by_cases hswap : swap e = true
  · simp only [PlaneGraphDrawing.SideLeftOf, PlaneGraphDrawing.SideRightOf,
      endpointSwapFace_val, PlaneGraphDrawing.endpointSwap,
      PlaneGraphDrawing.endpointSwapArc, dite_eq_left hswap, ite_eq_left hswap]
    constructor
    · intro h s
      let s' : {t : I // t ∈ openParams} :=
        ⟨σ s.1, symm_mem_openParams_iff.mpr s.2⟩
      have hcomp : (s'.1 : ℝ) + (s.1 : ℝ) = 1 := by
        simp only [s', unitInterval.coe_symm_eq]
        ring
      have h' := rightAtOn_to_leftAtOn_symm F.val (D.arc e).symm s' s
        (by linarith [hcomp]) (h s')
      simpa only [Path.symm_symm] using h'
    · intro h s'
      let s : {t : I // t ∈ openParams} :=
        ⟨σ s'.1, symm_mem_openParams_iff.mpr s'.2⟩
      have hcomp : (s'.1 : ℝ) + (s.1 : ℝ) = 1 := by
        simp only [s, unitInterval.coe_symm_eq]
        ring
      have h' : LeftAtOn F.val ((D.arc e).symm).symm s := by
        simpa only [Path.symm_symm] using h s
      exact leftAtOn_symm_to_rightAtOn F.val (D.arc e).symm s' s
        (by linarith [hcomp]) h'
  · have hfalse : swap e = false := by
      cases h : swap e with
      | false => rfl
      | true => exact (hswap h).elim
    have hneq : ¬ ((false : Bool) = true) := by decide
    simp only [PlaneGraphDrawing.SideLeftOf, PlaneGraphDrawing.SideRightOf,
      endpointSwapFace_val, PlaneGraphDrawing.endpointSwap,
      PlaneGraphDrawing.endpointSwapArc, hfalse, dite_eq_right hneq,
      ite_eq_right hneq]
    change (∀ s : {t : I // t ∈ openParams}, RightAtOn F.val (D.arc e) s) ↔ _
    rfl

/-- Endpoint storage does not change an edge's side multiplicity. Helper
toward Definition 1.1. -/
theorem endpointSwap_sideMult (D : PlaneGraphDrawing V E) (swap : E → Bool)
    (e : E) (F : D.Face) :
    (D.endpointSwap swap).sideMult e (D.endpointSwapFace swap F) =
      D.sideMult e F := by
  classical
  unfold PlaneGraphDrawing.sideMult
  cases hswap : swap e <;>
    simp [hswap, endpointSwap_sideLeftOf_iff, endpointSwap_sideRightOf_iff,
      add_comm]

/-- Endpoint storage does not change side degree. Helper toward Definition
1.1. -/
theorem endpointSwap_sideDegree (D : PlaneGraphDrawing V E)
    (swap : E → Bool) (F : D.Face) :
    D.sideDegree F =
      (D.endpointSwap swap).sideDegree (D.endpointSwapFace swap F) := by
  classical
  unfold PlaneGraphDrawing.sideDegree
  apply iSup_congr
  intro s
  apply Finset.sum_congr rfl
  intro e he
  exact (endpointSwap_sideMult D swap e F).symm

/-- Bipolarity and internal face side degree three are invariant under
endpoint storage swaps. Helper toward Definition 1.1. -/
theorem endpointSwap_isBipolarTriangulationBySides_iff
    (M : DirectedPlaneMap V E) (swap : E → Bool) :
    (M.endpointSwap swap).IsBipolarTriangulationBySides ↔
      M.IsBipolarTriangulationBySides := by
  constructor
  · intro h
    refine ⟨(DirectedPlaneMap.endpointSwap_isBipolar_iff M swap).mp h.1, ?_⟩
    intro F hF
    have hF' :=
      (endpointSwap_isInternal_iff M.toPlaneGraphDrawing swap F).2 hF
    exact (endpointSwap_sideDegree M.toPlaneGraphDrawing swap F).trans (h.2
      (M.toPlaneGraphDrawing.endpointSwapFace swap F) hF')
  · intro h
    refine ⟨(DirectedPlaneMap.endpointSwap_isBipolar_iff M swap).mpr h.1, ?_⟩
    let D := M.toPlaneGraphDrawing
    let e := D.endpointSwapFaceEquiv swap
    intro F' hF'
    let F := e.symm F'
    have hFace : D.endpointSwapFace swap F = F' := e.apply_symm_apply F'
    have hF : D.IsInternal F := by
      have hF'' :
          (M.endpointSwap swap).toPlaneGraphDrawing.IsInternal
            (D.endpointSwapFace swap F) := by
        simpa [hFace] using hF'
      exact (endpointSwap_isInternal_iff D swap F).mp hF''
    calc
      (M.endpointSwap swap).toPlaneGraphDrawing.sideDegree F' =
          (M.endpointSwap swap).toPlaneGraphDrawing.sideDegree
            (D.endpointSwapFace swap F) := by rw [hFace]
      _ = D.sideDegree F := (endpointSwap_sideDegree D swap F).symm
      _ = 3 := h.2 F hF











end DirectedDistances.PlanarMap

end
