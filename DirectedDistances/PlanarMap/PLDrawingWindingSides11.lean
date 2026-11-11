/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingWindingSides10







public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

namespace PLDrawing

/-- Helper toward Definition 3.2: a polyline takes the value of its shared
vertex at the parameter where a nonfinal segment ends. -/
theorem toPath_eq_vertex_at_segment_bend (p : Polyline) {i : ℕ}
    (hi : i + 2 < p.points.length) :
    p.toPath
        ⟨Polyline.segmentParameterStart (i + 1),
          Polyline.segmentParameterStart_mem_Icc (i + 1)⟩ =
      p.point (i + 1) := by
  have hi' : i + 1 < p.points.length := by omega
  have hnotlast : i + 2 ≠ p.points.length := by omega
  have hend := Polyline.segmentParameterEnd_eq_start_succ hnotlast
  let t : I := ⟨Polyline.segmentParameterStart (i + 1),
    Polyline.segmentParameterStart_mem_Icc (i + 1)⟩
  have hseg := Polyline.toPath_segment_affine_apply p hi'
  have hstart : Polyline.segmentParameterStart i ≤ (t : ℝ) := by
    change Polyline.segmentParameterStart i ≤ Polyline.segmentParameterStart (i + 1)
    rw [← hend]
    exact Polyline.segmentParameterStart_le_end p.points.length i
  have hterm : (t : ℝ) = Polyline.segmentParameterEnd p.points.length i := by
    change Polyline.segmentParameterStart (i + 1) = _
    exact hend.symm
  have hform := hseg t hstart (le_of_eq hterm)
  change p.toPath t = p.point i +
    (((((t : ℝ) - Polyline.segmentParameterStart i) /
      (Polyline.segmentParameterEnd p.points.length i -
        Polyline.segmentParameterStart i) : ℝ) : ℂ) *
      (p.point (i + 1) - p.point i)) at hform
  have hden : Polyline.segmentParameterEnd p.points.length i -
      Polyline.segmentParameterStart i ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Polyline.segmentParameterStart_lt_end
      p.points.length i))
  have hratio : ((t : ℝ) - Polyline.segmentParameterStart i) /
      (Polyline.segmentParameterEnd p.points.length i -
        Polyline.segmentParameterStart i) = 1 := by
    rw [hterm]
    exact div_self hden
  rw [hratio] at hform
  change p.toPath t = p.point (i + 1)
  rw [hform]
  rw [show ((1 : ℝ) : ℂ) = 1 by norm_num, one_mul]
  abel

/-- Helper toward Definition 3.2: at a bend parameter, the PL drawing
path is exactly the shared vertex. -/
theorem toPath_eq_vertex_at_bend
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) (s : {t : I // t ∈ openParams})
    {i : ℕ} (hi : i + 2 < (P.arc d).points.length)
    (hbend : (s.1 : ℝ) = Polyline.segmentParameterStart (i + 1)) :
    (P.arc d).toPath s.1 = (P.arc d).point (i + 1) := by
  have hs : s.1 =
      ⟨Polyline.segmentParameterStart (i + 1),
        Polyline.segmentParameterStart_mem_Icc (i + 1)⟩ := by
    apply Subtype.ext
    exact hbend
  rw [hs]
  exact toPath_eq_vertex_at_segment_bend (P.arc d) hi
















end PLDrawing

end DirectedDistances.PlanarMap

end
