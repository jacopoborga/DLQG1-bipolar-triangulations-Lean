/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingWindingSides4

/-! # Segment parameters for PL winding-side arguments -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

namespace Polyline

/-- Helper toward Definition 3.2: the initial parameter of segment `i` in
the recursively halved traversal of a polyline. -/
@[expose] def segmentParameterStart (i : ℕ) : ℝ := 1 - (1 / 2 : ℝ) ^ i

/-- Helper toward Definition 3.2: the terminal parameter of segment `i`.
The final segment uses the whole remaining interval. -/
@[expose] def segmentParameterEnd (n i : ℕ) : ℝ :=
  if i + 2 = n then 1 else 1 - (1 / 2 : ℝ) ^ (i + 1)

/-- Helper toward Definition 3.2: the first segment starts at parameter zero. -/
@[simp] theorem segmentParameterStart_zero : segmentParameterStart 0 = 0 := by
  simp [segmentParameterStart]

/-- Helper toward Definition 3.2: every segment starts in the unit interval. -/
theorem segmentParameterStart_mem_Icc (i : ℕ) :
    0 ≤ segmentParameterStart i ∧ segmentParameterStart i ≤ 1 := by
  have hpow_nonneg : 0 ≤ (1 / 2 : ℝ) ^ i := pow_nonneg (by norm_num) _
  have hpow_le : (1 / 2 : ℝ) ^ i ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  simp only [segmentParameterStart]
  constructor <;> linarith

/-- Helper toward Definition 3.2: a segment's terminal parameter is the
next segment's initial parameter, unless this is the final segment. -/
theorem segmentParameterEnd_eq_start_succ {n i : ℕ} (h : i + 2 ≠ n) :
    segmentParameterEnd n i = segmentParameterStart (i + 1) := by
  simp [segmentParameterEnd, h, segmentParameterStart]

/-- Helper toward Definition 3.2: the final segment ends at parameter one. -/
theorem segmentParameterEnd_last {n i : ℕ} (h : i + 2 = n) :
    segmentParameterEnd n i = 1 := by
  simp [segmentParameterEnd, h]

/-- Helper toward Definition 3.2: adjacent segment parameter intervals are
ordered for every valid segment index. -/
theorem segmentParameterStart_le_end (n i : ℕ) :
    segmentParameterStart i ≤ segmentParameterEnd n i := by
  by_cases hlast : i + 2 = n
  · rw [segmentParameterEnd_last hlast]
    exact (segmentParameterStart_mem_Icc i).2
  · rw [segmentParameterEnd_eq_start_succ hlast]
    simp only [segmentParameterStart]
    rw [pow_succ]
    have hpow_nonneg : 0 ≤ (1 / 2 : ℝ) ^ i := pow_nonneg (by norm_num) _
    nlinarith [hpow_nonneg]

/-- Helper toward Definition 3.2: a valid segment's terminal parameter is
in the unit interval. -/
theorem segmentParameterEnd_mem_Icc (n i : ℕ) :
    0 ≤ segmentParameterEnd n i ∧ segmentParameterEnd n i ≤ 1 := by
  by_cases hlast : i + 2 = n
  · rw [segmentParameterEnd_last hlast]
    norm_num
  · rw [segmentParameterEnd_eq_start_succ hlast]
    exact segmentParameterStart_mem_Icc (i + 1)

/-- Helper toward Definition 3.2: the first segment of a polyline with at
least three vertices is traversed affinely on the first half of the parameter
interval. -/
theorem toPath_firstSegment_affine_apply (p : Polyline)
    (hlen : 2 < p.points.length) (t : I) (ht : (t : ℝ) ≤ 1 / 2) :
    p.toPath t = p.point 0 + (((2 * (t : ℝ) : ℝ) : ℂ) *
      (p.point 1 - p.point 0)) := by
  obtain ⟨pts, hpts⟩ := p
  cases pts with
  | nil => exact False.elim (hpts rfl)
  | cons a tail =>
    cases tail with
    | nil => simp at hlen
    | cons b rest =>
      cases rest with
      | nil => simp at hlen
      | cons c rest =>
        simp only [Polyline.toPath, Path.cast]
        change ((Path.segment a b).trans (Polyline.listPath b (c :: rest))) t =
          a + (((2 * (t : ℝ) : ℝ) : ℂ) * (b - a))
        change (if (t : ℝ) ≤ 1 / 2 then
          (Path.segment a b).extend (2 * (t : ℝ)) else
          (Polyline.listPath b (c :: rest)).extend (2 * (t : ℝ) - 1)) = _
        rw [if_pos ht]
        have hmem : 2 * (t : ℝ) ∈ I := by
          constructor <;> linarith [t.2.1, ht]
        rw [Path.extend_apply _ hmem]
        rw [Path.segment_apply]
        rw [AffineMap.lineMap_apply_module']
        rw [Complex.real_smul]
        push_cast
        ring

end Polyline




























end DirectedDistances.PlanarMap

end
