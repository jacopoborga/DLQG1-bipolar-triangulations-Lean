/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodJ1WindowCircComplete
public import DirectedDistances.Probability.SkorokhodJ1WindowDCircReverseBound
public import DirectedDistances.Probability.SkorokhodJ1WindowSeparable

import Mathlib.Basic.ENNReal.Real

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/

@[expose] public section
namespace DirectedDistances.Probability




structure J1WindowD (T : ℝ) (_hT : 0 < T) where
  path : CadlagWindow T




@[instance_reducible] noncomputable instance j1WindowDMetricSpace
    {T : ℝ} (hT : 0 < T) : MetricSpace (J1WindowD T hT) where
  dist x y := j1WindowDist hT x.path y.path
  dist_self x := j1WindowDist_self hT x.path
  dist_comm x y := j1WindowDist_symm hT x.path y.path
  dist_triangle x y z := j1WindowDist_triangle hT x.path y.path z.path
  eq_of_dist_eq_zero := by
    intro x y h
    cases x with
    | mk x =>
      cases y with
      | mk y =>
        have hxy : x = y := (j1WindowDist_eq_zero_iff hT x y).mp h
        cases hxy
        rfl




def toJ1WindowD {T : ℝ} {hT : 0 < T} (f : CadlagWindow T) :
    J1WindowD T hT := ⟨f⟩




def ofJ1WindowD {T : ℝ} {hT : 0 < T} (f : J1WindowD T hT) : CadlagWindow T :=
  f.path




def j1WindowCircToD {T : ℝ} (hT : 0 < T) :
    J1WindowCirc T hT → J1WindowD T hT :=
  fun f => toJ1WindowD (ofJ1WindowCirc hT f)




def j1WindowDToCirc {T : ℝ} (hT : 0 < T) :
    J1WindowD T hT → J1WindowCirc T hT :=
  fun f => toJ1WindowCirc hT (ofJ1WindowD f)

private theorem j1WindowDContinuityBound_continuous (T : ℝ) :
    Continuous (fun r : ℝ => max (T * (Real.exp r - 1)) r) :=
  (continuous_const.mul (Real.continuous_exp.sub continuous_const)).max continuous_id




theorem j1WindowCircToD_small {T : ℝ} (hT : 0 < T)
    (x : J1WindowCirc T hT) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y : J1WindowCirc T hT,
      dist y x < δ → dist (j1WindowCircToD hT y) (j1WindowCircToD hT x) < ε := by
  let b : ℝ → ℝ := fun r => max (T * (Real.exp r - 1)) r
  have hbcont : Continuous b := j1WindowDContinuityBound_continuous T
  have hb0 : b 0 = 0 := by simp [b]
  obtain ⟨δ, hδ, hnear⟩ :=
    (Metric.continuousAt_iff.mp hbcont.continuousAt) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  let r := dist y x
  have hr : 0 ≤ r := dist_nonneg
  have hnear' : dist (b r) (b 0) < ε := hnear (by simpa [r] using hy)
  have hbnonneg : 0 ≤ b r := by
    apply le_max_of_le_right
    exact hr
  have hb_lt : b r < ε := by
    rw [hb0] at hnear'
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hbnonneg] using hnear'
  have hbound : j1WindowDist hT
      (ofJ1WindowCirc hT y) (ofJ1WindowCirc hT x) ≤ b r := by
    simpa only [j1WindowCirc_dist_eq, b, r] using
      j1WindowDist_le_dCirc hT (ofJ1WindowCirc hT y) (ofJ1WindowCirc hT x)
  calc
    dist (j1WindowCircToD hT y) (j1WindowCircToD hT x) =
        j1WindowDist hT (ofJ1WindowCirc hT y) (ofJ1WindowCirc hT x) := rfl
    _ ≤ b r := hbound
    _ < ε := hb_lt




theorem j1WindowDToCirc_small {T : ℝ} (hT : 0 < T)
    (x : J1WindowD T hT) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y : J1WindowD T hT,
      dist y x < δ → dist (j1WindowDToCirc hT y) (j1WindowDToCirc hT x) < ε := by
  obtain ⟨δ, hδ, hsmall⟩ :=
    j1WindowDist_small_implies_dCirc_small hT x.path hε
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  have hdist : j1WindowDist hT x.path y.path < δ := by
    have hy' : j1WindowDist hT y.path x.path < δ := by
      change j1WindowDist hT y.path x.path < δ at hy
      exact hy
    rw [j1WindowDist_symm] at hy'
    exact hy'
  have hbound := hsmall y.path hdist
  have hfinite := j1WindowDCirc_lt_top hT x.path y.path
  have hreal : (j1WindowDCirc hT x.path y.path).toReal < ε :=
    (ENNReal.lt_ofReal_iff_toReal_lt hfinite.ne).mp hbound
  change (j1WindowDCirc hT y.path x.path).toReal < ε
  rw [j1WindowDCirc_symm]
  exact hreal




theorem j1WindowCircToD_continuous {T : ℝ} (hT : 0 < T) :
    Continuous (j1WindowCircToD hT) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  obtain ⟨δ, hδ, hsmall⟩ := j1WindowCircToD_small hT x hε
  exact ⟨δ, hδ, hsmall⟩




theorem j1WindowDToCirc_continuous {T : ℝ} (hT : 0 < T) :
    Continuous (j1WindowDToCirc hT) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  obtain ⟨δ, hδ, hsmall⟩ := j1WindowDToCirc_small hT x hε
  exact ⟨δ, hδ, hsmall⟩





def j1WindowCircHomeomorphD {T : ℝ} (hT : 0 < T) :
    J1WindowCirc T hT ≃ₜ J1WindowD T hT where
  toEquiv :=
    { toFun := j1WindowCircToD hT
      invFun := j1WindowDToCirc hT
      left_inv := by intro x; cases x; rfl
      right_inv := by intro x; cases x; rfl }
  continuous_toFun := j1WindowCircToD_continuous hT
  continuous_invFun := j1WindowDToCirc_continuous hT

end DirectedDistances.Probability
