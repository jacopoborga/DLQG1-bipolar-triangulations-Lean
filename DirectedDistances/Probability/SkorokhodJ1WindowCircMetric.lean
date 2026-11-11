/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodJ1WindowDCirc
public import DirectedDistances.Probability.SkorokhodJ1WindowMetric

import Mathlib.Analysis.SpecialFunctions.Exp

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/

/-! # Metric structure for Billingsley's complete J1 window distance -/

@[expose] public section
namespace DirectedDistances.Probability

open Filter
open scoped Topology






def J1WindowCirc (T : ℝ) (_hT : 0 < T) := CadlagWindow T




def toJ1WindowCirc {T : ℝ} (hT : 0 < T) (f : CadlagWindow T) :
    J1WindowCirc T hT := f




def ofJ1WindowCirc {T : ℝ} (hT : 0 < T) (f : J1WindowCirc T hT) :
    CadlagWindow T := f




def j1WindowCircEquiv {T : ℝ} (hT : 0 < T) :
    J1WindowCirc T hT ≃ CadlagWindow T where
  toFun := ofJ1WindowCirc (T := T) hT
  invFun := toJ1WindowCirc (T := T) hT
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl




@[simp] theorem ofJ1WindowCirc_toJ1WindowCirc {T : ℝ} {hT : 0 < T}
    (f : CadlagWindow T) :
    ofJ1WindowCirc (T := T) hT (toJ1WindowCirc (T := T) hT f) = f := rfl




@[simp] theorem toJ1WindowCirc_ofJ1WindowCirc {T : ℝ} {hT : 0 < T}
    (f : J1WindowCirc T hT) :
    toJ1WindowCirc (T := T) hT (ofJ1WindowCirc (T := T) hT f) = f := rfl

private theorem j1WindowCirc_dCirc_eq_zero_of_toReal_eq_zero {T : ℝ}
    (hT : 0 < T) (f g : CadlagWindow T)
    (h : (j1WindowDCirc hT f g).toReal = 0) :
    j1WindowDCirc hT f g = 0 := by
  rcases (ENNReal.toReal_eq_zero_iff _).mp h with hzero | htop
  · exact hzero
  · exact False.elim ((j1WindowDCirc_lt_top hT f g).ne htop)




theorem j1WindowCirc_eq_of_dCirc_eq_zero {T : ℝ} (hT : 0 < T)
    (f g : J1WindowCirc T hT)
    (h : j1WindowDCirc hT (ofJ1WindowCirc (T := T) hT f) (ofJ1WindowCirc (T := T) hT g) = 0) :
    f = g := by
  have hdist :
      j1WindowDist hT (ofJ1WindowCirc (T := T) hT f)
        (ofJ1WindowCirc (T := T) hT g) = 0 := by
    have hcmp := j1WindowDist_le_dCirc hT (ofJ1WindowCirc (T := T) hT f)
      (ofJ1WindowCirc (T := T) hT g)
    rw [h] at hcmp
    have hle :
        j1WindowDist hT (ofJ1WindowCirc (T := T) hT f) (ofJ1WindowCirc (T := T) hT g) ≤ 0 := by
      simpa using hcmp
    exact le_antisymm hle
      (j1WindowDist_nonneg hT (ofJ1WindowCirc (T := T) hT f) (ofJ1WindowCirc (T := T) hT g))
  exact (j1WindowCircEquiv hT).injective
    ((j1WindowDist_eq_zero_iff hT _ _).mp hdist)





@[instance_reducible] noncomputable instance j1WindowCircMetricSpace {T : ℝ} (hT : 0 < T) :
    MetricSpace (J1WindowCirc T hT) where
  dist f g :=
    (j1WindowDCirc hT (ofJ1WindowCirc (T := T) hT f)
      (ofJ1WindowCirc (T := T) hT g)).toReal
  dist_self f := by simp [j1WindowDCirc_self]
  dist_comm f g := by
    rw [j1WindowDCirc_symm]
  dist_triangle f g h := by
    let a := j1WindowDCirc hT (ofJ1WindowCirc (T := T) hT f) (ofJ1WindowCirc (T := T) hT g)
    let b := j1WindowDCirc hT (ofJ1WindowCirc (T := T) hT g) (ofJ1WindowCirc (T := T) hT h)
    have ha : a < ⊤ := j1WindowDCirc_lt_top hT _ _
    have hb : b < ⊤ := j1WindowDCirc_lt_top hT _ _
    have hab : a + b < ⊤ := ENNReal.add_lt_top.mpr ⟨ha, hb⟩
    calc
      _ ≤ (a + b).toReal := by
        apply ENNReal.toReal_mono hab.ne
        exact j1WindowDCirc_triangle hT _ _ _
      _ = a.toReal + b.toReal := ENNReal.toReal_add ha.ne hb.ne
  eq_of_dist_eq_zero := by
    intro f g h
    apply j1WindowCirc_eq_of_dCirc_eq_zero hT
    exact j1WindowCirc_dCirc_eq_zero_of_toReal_eq_zero hT _ _ h




theorem j1WindowCirc_dist_eq {T : ℝ} (hT : 0 < T)
    (f g : J1WindowCirc T hT) :
    dist f g =
      (j1WindowDCirc hT (ofJ1WindowCirc (T := T) hT f)
        (ofJ1WindowCirc (T := T) hT g)).toReal := rfl




theorem j1WindowDist_tendsto_zero_of_j1WindowCirc_dist_tendsto_zero
    {T : ℝ} (hT : 0 < T) (x : ℕ → J1WindowCirc T hT)
    (y : J1WindowCirc T hT)
    (hx : Tendsto (fun n => dist (x n) y) atTop (𝓝 0)) :
    Tendsto (fun n => j1WindowDist hT (ofJ1WindowCirc (T := T) hT (x n))
      (ofJ1WindowCirc (T := T) hT y)) atTop (𝓝 0) := by
  let d : ℕ → ℝ := fun n =>
    (j1WindowDCirc hT (ofJ1WindowCirc (T := T) hT (x n)) (ofJ1WindowCirc (T := T) hT y)).toReal
  have hd : Tendsto d atTop (𝓝 0) := by
    simpa only [d, j1WindowCirc_dist_eq] using hx
  let bound : ℝ → ℝ := fun r => max (T * (Real.exp r - 1)) r
  have hbound_cont : Continuous bound := by
    dsimp [bound]
    exact (continuous_const.mul (Real.continuous_exp.sub continuous_const)).max
      continuous_id
  have hbound_zero : bound 0 = 0 := by simp [bound]
  have hlimit : Tendsto (fun n => bound (d n)) atTop (𝓝 0) := by
    have htemp : Tendsto (fun n => bound (d n)) atTop (𝓝 (bound 0)) := by
      exact hbound_cont.continuousAt.tendsto.comp hd
    rw [← hbound_zero]
    exact htemp
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hlimit ε hε] with n hn
  have hbound_nonneg : 0 ≤ bound (d n) := by
    apply le_max_of_le_right
    exact ENNReal.toReal_nonneg
  have hbound_lt : bound (d n) < ε := by
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg hbound_nonneg] using hn
  calc
    dist (j1WindowDist hT (ofJ1WindowCirc (T := T) hT (x n)) (ofJ1WindowCirc (T := T) hT y)) 0 =
        j1WindowDist hT (ofJ1WindowCirc (T := T) hT (x n)) (ofJ1WindowCirc (T := T) hT y) := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (j1WindowDist_nonneg hT _ _)]
    _ ≤ bound (d n) := by
      simpa only [bound, d] using
        j1WindowDist_le_dCirc hT (ofJ1WindowCirc (T := T) hT (x n)) (ofJ1WindowCirc (T := T) hT y)
    _ < ε := hbound_lt

end DirectedDistances.Probability
