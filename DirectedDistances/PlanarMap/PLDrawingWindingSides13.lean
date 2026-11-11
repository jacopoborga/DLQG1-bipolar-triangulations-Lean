/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingWindingSides12

/-! # Winding sides at PL drawing bends -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

namespace Polyline

/-- Helper toward Definition 3.2: an internal bend has parameters on both
incident segments, strictly before and after the bend. -/
theorem bend_neighbor_parameters {n i : ℕ} (hi : i + 2 < n) :
    ∃ a b : I,
      0 < (a : ℝ) ∧
      (a : ℝ) < segmentParameterStart (i + 1) ∧
      segmentParameterStart (i + 1) < (b : ℝ) ∧
      (b : ℝ) < 1 := by
  let aVal := (segmentParameterStart i + segmentParameterEnd n i) / 2
  let bVal := (segmentParameterStart (i + 1) +
    segmentParameterEnd n (i + 1)) / 2
  have hnotlast : i + 2 ≠ n := by omega
  have hend : segmentParameterEnd n i = segmentParameterStart (i + 1) :=
    segmentParameterEnd_eq_start_succ hnotlast
  have haI : 0 ≤ aVal ∧ aVal ≤ 1 := by
    have hs := segmentParameterStart_mem_Icc i
    have he := segmentParameterEnd_mem_Icc n i
    dsimp [aVal]
    constructor <;> linarith
  have hbI : 0 ≤ bVal ∧ bVal ≤ 1 := by
    have hs := segmentParameterStart_mem_Icc (i + 1)
    have he := segmentParameterEnd_mem_Icc n (i + 1)
    dsimp [bVal]
    constructor <;> linarith
  have ha0 : 0 < aVal := by
    have hs := segmentParameterStart_mem_Icc i
    have he := segmentParameterStart_lt_end n i
    rw [hend] at he
    dsimp [aVal]
    linarith
  have habend : aVal < segmentParameterStart (i + 1) := by
    have hs := segmentParameterStart_lt_end n i
    rw [hend] at hs
    dsimp [aVal]
    linarith
  have hstartend : segmentParameterStart (i + 1) <
      segmentParameterEnd n (i + 1) := segmentParameterStart_lt_end n (i + 1)
  have hbend : segmentParameterStart (i + 1) < bVal := by
    dsimp [bVal]
    linarith
  have hb1 : bVal < 1 := by
    have he := segmentParameterEnd_mem_Icc n (i + 1)
    dsimp [bVal]
    linarith
  exact ⟨⟨aVal, haI⟩, ⟨bVal, hbI⟩, ha0, habend, hbend, hb1⟩

/-- Helper toward Definition 3.2: parameters can be chosen on either side
of a specified internal bend. -/
theorem bend_neighbor_parameters_at {n i : ℕ} (hi : i + 2 < n)
    (s : I) (hs : (s : ℝ) = segmentParameterStart (i + 1)) :
    ∃ a b : I, 0 < (a : ℝ) ∧ (a : ℝ) < (s : ℝ) ∧
      (s : ℝ) < (b : ℝ) ∧ (b : ℝ) < 1 := by
  obtain ⟨a, b, ha, has, hsb, hb⟩ := bend_neighbor_parameters hi
  refine ⟨a, b, ha, ?_, ?_, hb⟩
  · calc
      (a : ℝ) < segmentParameterStart (i + 1) := has
      _ = (s : ℝ) := hs.symm
  · calc
      (s : ℝ) = segmentParameterStart (i + 1) := hs
      _ < (b : ℝ) := hsb

end Polyline

namespace PLDrawing

/-- Helper toward Definition 3.2: the bordering face accumulates at the
geometric vertex of an internal bend. -/
theorem dartBorders_bend_vertex_mem_closure_face
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (s : {t : I // t ∈ openParams}) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (hbend : (s.1 : ℝ) = Polyline.segmentParameterStart (i + 1)) :
    (P.arc d).point (i + 1) ∈ closure F.val := by
  have hcl := P.dartBorders_toPath_mem_closure hvert d F hborder s
  rw [P.toPath_eq_vertex_at_bend d s hi hbend] at hcl
  exact hcl

/-- Helper toward Definition 3.2: points with winding number one around a
left semicircle loop accumulate at its center. -/
theorem semicircleLoop_center_mem_closure_winding (b u : ℂ) (hu : u ≠ 0) :
    b ∈ closure {w : ℂ | HasWinding (semicircleLoop b u) w 1} := by
  rw [Metric.mem_closure_iff]
  intro η hη
  let τ := min (1 / 2) (η / (2 * (‖u‖ + 1)))
  have hτ : 0 < τ := lt_min (by norm_num) (div_pos hη (by positivity))
  have hτ1 : τ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hτη : τ * (2 * (‖u‖ + 1)) ≤ η :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  let w := b + u * (τ * Complex.I)
  have hwind : HasWinding (semicircleLoop b u) w 1 := by
    simpa only [w, mul_comm] using hasWinding_semicircleLoop b u hu τ hτ hτ1
  refine ⟨w, hwind, ?_⟩
  rw [dist_comm, dist_eq_norm]
  change ‖b + u * (τ * Complex.I) - b‖ < η
  rw [add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hτ, Complex.norm_I, mul_one]
  nlinarith [norm_nonneg u, hτη]


























end PLDrawing

end DirectedDistances.PlanarMap

end
