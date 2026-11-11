/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact12
import DirectedDistances.PlanarMap.D39PLSimpleArcInOpen3







public section
noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval Set

/-- Helper toward Definition 3.2: the segment from a point on the diameter
into a half-disk lies in the face away from its boundary endpoint. The
half-plane functional abstracts the chosen side of the straight edge. -/
theorem segment_from_halfDisk_boundary_mem
    {U : Set ℂ} (z x : ℂ) (r : ℝ) (side : ℂ →ₗ[ℝ] ℝ)
    (hhalf : ∀ w : ℂ, ‖w - z‖ < r → 0 < side (w - z) → w ∈ U)
    (hxball : ‖x - z‖ < r) (hxside : 0 < side (x - z))
    {w : ℂ} (hw : w ∈ segment ℝ z x) (hwz : w ≠ z) : w ∈ U := by
  rw [segment_eq_image'] at hw
  obtain ⟨t, ht, hwt⟩ := hw
  have htne : t ≠ 0 := by
    intro ht0
    apply hwz
    rw [← hwt, ht0]
    simp
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
  have hnorm : ‖w - z‖ ≤ ‖x - z‖ := by
    rw [← hwt]
    rw [show z + t • (x - z) - z = t • (x - z) by module]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc
      t * ‖x - z‖ ≤ 1 * ‖x - z‖ :=
        mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
      _ = ‖x - z‖ := one_mul _
  have hside : side (w - z) = t * side (x - z) := by
    rw [← hwt]
    rw [show z + t • (x - z) - z = t • (x - z) by module]
    simp only [map_smul]
    rfl
  apply hhalf w (lt_of_le_of_lt hnorm hxball)
  rw [hside]
  exact mul_pos htpos hxside

/-- Helper toward Definition 3.2: a boundary point and a point of an open
half-disk are joined by a simple two-vertex polyline whose open traversal is
inside the half-disk's face. -/
theorem exists_simple_polyline_halfDisk_connector
    {U : Set ℂ} (z x : ℂ) (r : ℝ) (side : ℂ →ₗ[ℝ] ℝ)
    (hhalf : ∀ w : ℂ, ‖w - z‖ < r → 0 < side (w - z) → w ∈ U)
    (hxball : ‖x - z‖ < r) (hxside : 0 < side (x - z)) :
    ∃ q : Polyline, q.IsSimple ∧ q.start = z ∧ q.finish = x ∧
      ∀ t : I, t ∈ openParams → q.toPath t ∈ U := by
  have hzx : z ≠ x := by
    intro h
    subst x
    simp at hxside
  let q : Polyline := ⟨[z, x], by simp⟩
  have hqsimple : q.IsSimple := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have hi0 : i = 0 := by change i + 1 < 2 at hi; omega
      subst i
      simpa [q, Polyline.point, Polyline.start] using hzx
    · intro i hi
      change i + 2 < 2 at hi
      omega
    · intro i j hi hj hij
      change i + 1 < 2 at hi
      change j + 1 < 2 at hj
      omega
  have hqaffine (t : I) :
      q.toPath t = z + (((t : ℝ) : ℂ) * (x - z)) := by
    simp only [q, Polyline.toPath, Polyline.listPath, Path.cast]
    change Path.segment z x t = _
    rw [Path.segment_apply, AffineMap.lineMap_apply_module']
    simp
    ring
  refine ⟨q, hqsimple, ?_, ?_, ?_⟩
  · simp [q, Polyline.start]
  · simp [q, Polyline.finish]
  · intro t ht
    have hdiff : q.toPath t - z = (((t : ℝ) : ℂ) * (x - z)) := by
      rw [hqaffine]
      module
    have hnorm : ‖q.toPath t - z‖ ≤ ‖x - z‖ := by
      rw [hdiff]
      rw [show (((t : ℝ) : ℂ) * (x - z)) = (t : ℝ) • (x - z) by simp]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt ht.1)]
      calc
        (t : ℝ) * ‖x - z‖ ≤ 1 * ‖x - z‖ :=
          mul_le_mul_of_nonneg_right (le_of_lt ht.2) (norm_nonneg _)
        _ = ‖x - z‖ := one_mul _
    have hside : side (q.toPath t - z) = (t : ℝ) * side (x - z) := by
      rw [hdiff]
      rw [show (((t : ℝ) : ℂ) * (x - z)) = (t : ℝ) • (x - z) by simp]
      simp only [map_smul]
      rfl
    apply hhalf (q.toPath t) (lt_of_le_of_lt hnorm hxball)
    rw [hside]
    exact mul_pos ht.1 hxside
































































































































end DirectedDistances.PlanarMap

end
