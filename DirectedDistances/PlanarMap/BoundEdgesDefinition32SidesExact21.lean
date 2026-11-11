/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact20
import DirectedDistances.PlanarMap.D39PolygonWindingBridge2







public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set
open scoped Topology

/-- Helper toward Definition 3.2: for a cyclically simple polygon, winding
one on the left side of an oriented edge is equivalent to winding zero on
its right side, sufficiently near an interior point of that edge. -/
theorem Polyline.exists_winding_one_iff_zero_across_cyclic_edge32
    (p : Polyline) (hp : p.IsCyclicSimple)
    (i : ℕ) (hi : i + 1 < p.points.length) (x a b : ℂ)
    (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1))
    (hai : p.point i = a) (ha1 : p.point (i + 1) = b) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u v : ℂ,
      u ∉ p.image → v ∉ p.image → dist u x < ε → dist v x < ε →
      0 < (star (b - a) * (u - x)).im →
      (star (b - a) * (v - x)).im < 0 →
      (HasWinding (p.toPath.cast rfl (by
          rw [← Polyline.point_zero_eq_start, ← Polyline.point_last_eq_finish]
          exact hp.2.1)) u 1 ↔
        HasWinding (p.toPath.cast rfl (by
          rw [← Polyline.point_zero_eq_start, ← Polyline.point_last_eq_finish]
          exact hp.2.1)) v 0) := by
  have hclosed : p.start = p.finish := by
    rw [← Polyline.point_zero_eq_start, ← Polyline.point_last_eq_finish]
    exact hp.2.1
  obtain ⟨ε, hε, hjump⟩ :=
    p.exists_signed_angleSum_edge_jump_cyclic32 hp i hi x hx hxi hxi1
  refine ⟨ε, hε, ?_⟩
  intro u v hu hv hux hvx huLeft hvRight
  have huLeft' :
      0 < (star (p.point (i + 1) - p.point i) * (u - x)).im := by
    rw [hai, ha1]
    exact huLeft
  have hvRight' :
      (star (p.point (i + 1) - p.point i) * (v - x)).im < 0 := by
    rw [hai, ha1]
    exact hvRight
  have hangleJump := hjump u v hu hv hux hvx huLeft' hvRight'
  constructor
  · intro hwindu
    have hangleuInt : p.angleSum u = ((1 : ℤ) : ℝ) :=
      (hasWinding_iff_angleSum_eq_int p hclosed u 1 hu).mp hwindu
    have hangleu : p.angleSum u = (1 : ℝ) := by
      simpa only [Int.cast_one] using hangleuInt
    have hanglev : p.angleSum v = (0 : ℝ) := by linarith
    have hanglevInt : p.angleSum v = ((0 : ℤ) : ℝ) := by
      simpa only [Int.cast_zero] using hanglev
    exact (hasWinding_iff_angleSum_eq_int p hclosed v 0 hv).mpr hanglevInt
  · intro hwindv
    have hanglevInt : p.angleSum v = ((0 : ℤ) : ℝ) :=
      (hasWinding_iff_angleSum_eq_int p hclosed v 0 hv).mp hwindv
    have hanglev : p.angleSum v = (0 : ℝ) := by
      simpa only [Int.cast_zero] using hanglevInt
    have hangleu : p.angleSum u = (1 : ℝ) := by linarith
    have hangleuInt : p.angleSum u = ((1 : ℤ) : ℝ) := by
      simpa only [Int.cast_one] using hangleu
    exact (hasWinding_iff_angleSum_eq_int p hclosed u 1 hu).mpr hangleuInt

/-- Helper toward Definition 3.2: wrong-side winding accumulation is
transferred from a cyclic polygon's logarithmic winding to its signed angle
sum at an interior point of an oriented edge. -/
theorem Polyline.not_mem_closure_wrong_side_winding_cyclic32
    (p : Polyline) (hp : p.IsCyclicSimple)
    (i : ℕ) (hi : i + 1 < p.points.length) (x : ℂ)
    (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1)) :
    x ∉ closure {w : ℂ | w ∉ p.image ∧
        HasWinding (p.toPath.cast rfl (by
          rw [← Polyline.point_zero_eq_start, ← Polyline.point_last_eq_finish]
          exact hp.2.1)) w 1 ∧
        (star (p.point (i + 1) - p.point i) * (w - x)).im < 0} ∧
    x ∉ closure {w : ℂ | w ∉ p.image ∧
        HasWinding (p.toPath.cast rfl (by
          rw [← Polyline.point_zero_eq_start, ← Polyline.point_last_eq_finish]
          exact hp.2.1)) w (-1) ∧
        0 < (star (p.point (i + 1) - p.point i) * (w - x)).im} := by
  have hclosed : p.start = p.finish := by
    rw [← Polyline.point_zero_eq_start, ← Polyline.point_last_eq_finish]
    exact hp.2.1
  have hset1 :
      {w : ℂ | w ∉ p.image ∧
        HasWinding (p.toPath.cast rfl hclosed) w 1 ∧
        (star (p.point (i + 1) - p.point i) * (w - x)).im < 0} =
      {w : ℂ | w ∉ p.image ∧ p.angleSum w = (1 : ℝ) ∧
        (star (p.point (i + 1) - p.point i) * (w - x)).im < 0} := by
    ext w
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hw, hwind, hside⟩
      have hangleInt := (hasWinding_iff_angleSum_eq_int p hclosed w 1 hw).mp hwind
      have hangle : p.angleSum w = (1 : ℝ) := by
        simpa only [Int.cast_one] using hangleInt
      exact ⟨hw, hangle, hside⟩
    · rintro ⟨hw, hangle, hside⟩
      have hangleInt : p.angleSum w = ((1 : ℤ) : ℝ) := by
        simpa only [Int.cast_one] using hangle
      exact ⟨hw, (hasWinding_iff_angleSum_eq_int p hclosed w 1 hw).mpr hangleInt, hside⟩
  have hsetm :
      {w : ℂ | w ∉ p.image ∧
        HasWinding (p.toPath.cast rfl hclosed) w (-1) ∧
        0 < (star (p.point (i + 1) - p.point i) * (w - x)).im} =
      {w : ℂ | w ∉ p.image ∧ p.angleSum w = (-1 : ℝ) ∧
        0 < (star (p.point (i + 1) - p.point i) * (w - x)).im} := by
    ext w
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hw, hwind, hside⟩
      have hangleInt := (hasWinding_iff_angleSum_eq_int p hclosed w (-1) hw).mp hwind
      have hangle : p.angleSum w = (-1 : ℝ) := by
        simpa only [Int.cast_neg, Int.cast_one] using hangleInt
      exact ⟨hw, hangle, hside⟩
    · rintro ⟨hw, hangle, hside⟩
      have hangleInt : p.angleSum w = ((-1 : ℤ) : ℝ) := by
        simpa only [Int.cast_neg, Int.cast_one] using hangle
      exact ⟨hw, (hasWinding_iff_angleSum_eq_int p hclosed w (-1) hw).mpr hangleInt, hside⟩
  have hangle := p.not_mem_closure_wrong_side_angleSum_cyclic32
    hp i hi x hx hxi hxi1
  rw [hset1, hsetm]
  exact hangle




























































































end DirectedDistances.PlanarMap

end
