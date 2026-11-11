/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith

/-! # Passing from uniform cutoff approximations to a limit

Generic analytic infrastructure used by the revised Appendix A.4 proof.
This file proves the double-limit transfer itself; the actual compact-interval
limit and uniform oscillatory-tail estimate are separate mathematical inputs
to be proved for each application. -/

public section
namespace DirectedDistances.Tauberian

open Set Filter
open scoped Topology

/-- A cutoff approximation with an error tending uniformly to zero transfers
its limiting value to the original family. -/
theorem tendsto_of_uniform_cutoff_bound {F : ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    {H b : ℝ → ℝ} {L : ℝ}
    (hH : Tendsto H atTop (𝓝 L)) (hb : Tendsto b atTop (𝓝 0))
    (hG : ∀ A : ℝ, 0 < A → Tendsto (G A) (𝓝[>] (0 : ℝ)) (𝓝 (H A)))
    (hbound : ∀ t : ℝ, 0 < t → ∀ A : ℝ, 0 < A → ‖F t - G A t‖ ≤ b A) :
    Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  apply Metric.tendsto_nhds.2
  intro δ hδ
  have hδ3 : 0 < δ / 3 := div_pos hδ (by norm_num)
  have hbsmall := hb.eventually (gt_mem_nhds hδ3)
  have hHclose := (Metric.tendsto_nhds.1 hH) (δ / 3) hδ3
  obtain ⟨A, hA, hsmall, hclose⟩ :=
    ((eventually_ge_atTop (1 : ℝ)).and (hbsmall.and hHclose)).exists
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hGclose := (Metric.tendsto_nhds.1 (hG A hApos)) (δ / 3) hδ3
  filter_upwards [eventually_mem_nhdsWithin, hGclose] with t ht htg
  have he : dist (F t) (G A t) ≤ b A := by
    rw [dist_eq_norm]
    exact hbound t ht A hApos
  calc
    dist (F t) L ≤ dist (F t) (G A t) +
        (dist (G A t) (H A) + dist (H A) L) :=
      (dist_triangle _ _ _).trans (add_le_add le_rfl (dist_triangle _ _ _))
    _ < δ := by linarith only [he, hsmall, htg, hclose]

/-- The power-decaying uniform-tail form needed for A.4. One coefficient must
work for every positive scale and cutoff. -/
theorem tendsto_of_uniform_rpow_cutoff_bound {ν c J : ℝ} (hν : 0 < ν)
    {F : ℝ → ℝ} {G : ℝ → ℝ → ℝ} {H : ℝ → ℝ}
    (hH : Tendsto H atTop (𝓝 J))
    (hG : ∀ A : ℝ, 0 < A → Tendsto (G A) (𝓝[>] (0 : ℝ)) (𝓝 (c * H A)))
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ A : ℝ, 0 < A →
      ‖F t - G A t‖ ≤ C * A ^ (-ν)) :
    Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (c * J)) := by
  obtain ⟨C, _hC, hbound⟩ := hbound
  apply tendsto_of_uniform_cutoff_bound (hH.const_mul c) _ hG hbound
  simpa only [mul_zero] using (tendsto_rpow_neg_atTop hν).const_mul C

end DirectedDistances.Tauberian
