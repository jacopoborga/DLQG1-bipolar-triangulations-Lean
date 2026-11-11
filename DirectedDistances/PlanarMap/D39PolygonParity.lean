/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PolygonalSeparation
public import DirectedDistances.PlanarMap.HasWindingTransfer
import Mathlib.Topology.MetricSpace.HausdorffDistance








public section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

/-- Helper toward Proposition 5.16: a known logarithmic winding value persists
for all basepoints sufficiently close to a point outside the loop image. -/
theorem hasWinding_stable_nearby {z : ℂ} (L : Path z z) (w : ℂ) (n : ℤ)
    (havoid : ∀ t : unitInterval, L t ≠ w) (hw : HasWinding L w n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w' : ℂ, dist w' w < ε → HasWinding L w' n := by
  let S : Set ℂ := Set.range L
  have hSclosed : IsClosed S := isCompact_range L.continuous |>.isClosed
  have hSne : S.Nonempty := ⟨L 0, ⟨0, rfl⟩⟩
  have hwS : w ∉ S := by
    rintro ⟨t, rfl⟩
    exact havoid t rfl
  have hd : 0 < Metric.infDist w S :=
    hSclosed.notMem_iff_infDist_pos hSne |>.mp hwS
  have hdist (t : unitInterval) : Metric.infDist w S ≤ dist w (L t) :=
    Metric.infDist_le_dist_of_mem ⟨t, rfl⟩
  refine ⟨Metric.infDist w S, hd, ?_⟩
  intro w' hnear
  have havoid' : ∀ t : unitInterval, L t ≠ w' := by
    intro t ht
    have hlt : dist w (L t) < Metric.infDist w S := by
      calc
        dist w (L t) = dist w w' := by rw [ht]
        _ = dist w' w := dist_comm _ _
        _ < Metric.infDist w S := hnear
    exact (not_lt_of_ge (hdist t)) hlt
  let L' : Path (z + (w - w')) (z + (w - w')) :=
    L.map (continuous_id.add continuous_const)
  have hshift (t : unitInterval) : L' t - w = L t - w' := by
    simp [L']
    ring
  have havoidLoop' : ∀ t : unitInterval, L' t ≠ w := by
    intro t ht
    have hzero : L t - w' = 0 := by rw [← hshift t, ht]; simp
    exact havoid' t (sub_eq_zero.mp hzero)
  have hratio : ∀ t : unitInterval,
      (L' t - w) / (L t - w) ∈ Complex.slitPlane := by
    intro t
    have hden : L t - w ≠ 0 := sub_ne_zero.mpr (havoid t)
    have hdenNorm : 0 < ‖L t - w‖ := norm_pos_iff.mpr hden
    have hdistLower : Metric.infDist w S ≤ ‖L t - w‖ := by
      simpa only [dist_eq_norm, norm_sub_rev] using hdist t
    have hnum : ‖w - w'‖ < ‖L t - w‖ := by
      calc
        ‖w - w'‖ = dist w' w := by simp [dist_eq_norm, norm_sub_rev]
        _ < Metric.infDist w S := hnear
        _ ≤ ‖L t - w‖ := hdistLower
    have hquot : (L' t - w) / (L t - w) - 1 = (w - w') / (L t - w) := by
      rw [hshift t]
      field_simp [hden]
      ring
    have hquotNorm : ‖(L' t - w) / (L t - w) - 1‖ < 1 := by
      rw [hquot, norm_div]
      exact (div_lt_one hdenNorm).2 hnum
    have hball : (L' t - w) / (L t - w) ∈ Metric.ball 1 1 := by
      change dist ((L' t - w) / (L t - w)) 1 < 1
      rw [dist_eq_norm]
      exact hquotNorm
    exact Complex.ball_one_subset_slitPlane hball
  have hwshift : HasWinding L' w n :=
    hasWinding_of_ratio_mem_slitPlane L L' w n havoid havoidLoop' hratio hw
  obtain ⟨φ, hφ, hφinc⟩ := hwshift
  refine ⟨φ, ?_, hφinc⟩
  intro t
  rw [← hshift t]
  exact hφ t

/-- Helper toward Proposition 5.16: wherever a winding integer exists, its
value is locally constant on the complement of the loop image. -/
theorem hasWinding_value_eq_of_nearby {z : ℂ} (L : Path z z) (w : ℂ) (n : ℤ)
    (havoid : ∀ t : unitInterval, L t ≠ w) (hw : HasWinding L w n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w' : ℂ, dist w' w < ε →
      ∀ m : ℤ, HasWinding L w' m → m = n := by
  obtain ⟨ε, hε, hstable⟩ := hasWinding_stable_nearby L w n havoid hw
  refine ⟨ε, hε, ?_⟩
  intro w' hnear m hm
  exact hasWinding_unique hm (hstable w' hnear)

/-- Helper toward Proposition 5.16: the parity of an existing winding number
is locally constant on the complement of a loop. -/
theorem hasWinding_parity_eq_of_nearby {z : ℂ} (L : Path z z) (w : ℂ) (n : ℤ)
    (havoid : ∀ t : unitInterval, L t ≠ w) (hw : HasWinding L w n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w' : ℂ, dist w' w < ε →
      ∀ m : ℤ, HasWinding L w' m → m % 2 = n % 2 := by
  obtain ⟨ε, hε, hvalue⟩ := hasWinding_value_eq_of_nearby L w n havoid hw
  refine ⟨ε, hε, ?_⟩
  intro w' hnear m hm
  rw [hvalue w' hnear m hm]
























end DirectedDistances.PlanarMap

end
