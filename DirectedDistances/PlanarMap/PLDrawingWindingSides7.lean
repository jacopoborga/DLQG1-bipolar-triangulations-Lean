/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingWindingSides6

/-! # Paused subarcs on PL winding-side segments -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

namespace PLDrawing

/-- Helper toward Definition 3.2: pausing a polyline at the dyadic interval
of one segment traverses the endpoint chord with the clamped affine parameter. -/
theorem toPath_segment_paused_subarc
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length) :
    let a : I := ⟨Polyline.segmentParameterStart i,
      Polyline.segmentParameterStart_mem_Icc i⟩
    let b : I := ⟨Polyline.segmentParameterEnd (P.arc d).points.length i,
      Polyline.segmentParameterEnd_mem_Icc (P.arc d).points.length i⟩
    ∀ t : I,
      edgeSubarc (P.arc d).toPath a b
        (le_of_lt (by
          change Polyline.segmentParameterStart i <
            Polyline.segmentParameterEnd (P.arc d).points.length i
          exact Polyline.segmentParameterStart_lt_end (P.arc d).points.length i)) t =
        Path.segment ((P.arc d).toPath a) ((P.arc d).toPath b)
          ⟨(((min (max t a) b : I) : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)), by
            have hca : a ≤ min (max t a) b :=
              le_min (le_max_right _ _) (le_of_lt (by
                change Polyline.segmentParameterStart i <
                  Polyline.segmentParameterEnd (P.arc d).points.length i
                exact Polyline.segmentParameterStart_lt_end
                  (P.arc d).points.length i))
            have hcb : min (max t a) b ≤ b := min_le_right _ _
            constructor
            · exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hca))
                (sub_nonneg.mpr (by exact_mod_cast
                  (le_of_lt (by
                    change Polyline.segmentParameterStart i <
                      Polyline.segmentParameterEnd (P.arc d).points.length i
                    exact Polyline.segmentParameterStart_lt_end
                      (P.arc d).points.length i))))
            · rw [div_le_one (sub_pos.mpr (by
                change Polyline.segmentParameterStart i <
                  Polyline.segmentParameterEnd (P.arc d).points.length i
                exact Polyline.segmentParameterStart_lt_end
                  (P.arc d).points.length i))]
              exact sub_le_sub_right (by exact_mod_cast hcb) _⟩ := by
  dsimp only
  let p := P.arc d
  let a : I := ⟨Polyline.segmentParameterStart i,
    Polyline.segmentParameterStart_mem_Icc i⟩
  let b : I := ⟨Polyline.segmentParameterEnd p.points.length i,
    Polyline.segmentParameterEnd_mem_Icc p.points.length i⟩
  have hab : a < b := by
    change Polyline.segmentParameterStart i < Polyline.segmentParameterEnd p.points.length i
    exact Polyline.segmentParameterStart_lt_end p.points.length i
  have hseg := Polyline.toPath_segment_affine_apply p hi
  dsimp only at hseg
  have ha : p.toPath a = p.point i := by
    have h := hseg a le_rfl
      (by exact_mod_cast hab.le)
    simpa [a] using h
  have hb : p.toPath b = p.point (i + 1) := by
    have h := hseg b (by exact_mod_cast hab.le)
      (by change Polyline.segmentParameterEnd p.points.length i ≤ _; exact le_rfl)
    have hden : Polyline.segmentParameterEnd p.points.length i -
        Polyline.segmentParameterStart i ≠ 0 :=
      ne_of_gt (sub_pos.mpr (Polyline.segmentParameterStart_lt_end p.points.length i))
    simpa [b, hden] using h
  have hline : ∀ u : I, a ≤ u → u ≤ b →
      p.toPath u = p.toPath a +
        (((((u : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)) : ℝ) : ℂ) *
          (p.toPath b - p.toPath a)) := by
    intro u hau hub
    have hu := hseg u hau hub
    have hparam : ((u : ℝ) - Polyline.segmentParameterStart i) /
        (Polyline.segmentParameterEnd p.points.length i -
          Polyline.segmentParameterStart i) =
      ((u : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)) := by
      simp [a, b]
    calc
      p.toPath u = p.point i +
          (((((u : ℝ) - Polyline.segmentParameterStart i) /
            (Polyline.segmentParameterEnd p.points.length i -
              Polyline.segmentParameterStart i) : ℝ) : ℂ) *
            (p.point (i + 1) - p.point i)) := hu
      _ = p.toPath a +
          (((((u : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)) : ℝ) : ℂ) *
            (p.toPath b - p.toPath a)) := by
        rw [ha, hb, ← hparam]
  intro t
  have hpaused := edgeSubarc_affine_apply p.toPath hab hline t
  rw [hpaused, ha, hb]
  rw [Path.segment_apply, AffineMap.lineMap_apply_module']
  simp only [Complex.real_smul]
  ring











end PLDrawing

end DirectedDistances.PlanarMap

end
