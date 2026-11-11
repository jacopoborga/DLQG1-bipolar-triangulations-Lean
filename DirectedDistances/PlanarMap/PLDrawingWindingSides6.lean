/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingWindingSides5

/-! # Affine parameterization of PL winding-side arcs -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

namespace Polyline

/-- Helper toward Definition 3.2: successive segment starts are related by
the parameter-halving recursion for `Polyline.toPath`. -/
theorem segmentParameterStart_succ (i : ℕ) :
    segmentParameterStart (i + 1) = (1 + segmentParameterStart i) / 2 := by
  simp only [segmentParameterStart]
  rw [pow_succ]
  ring

/-- Helper toward Definition 3.2: segment ends obey the same affine
parameter-halving recursion, including the final segment. -/
theorem segmentParameterEnd_succ (n i : ℕ) :
    segmentParameterEnd (n + 1) (i + 1) =
      (1 + segmentParameterEnd n i) / 2 := by
  by_cases hlast : i + 2 = n
  · have hlast' : (i + 1) + 2 = n + 1 := by omega
    rw [segmentParameterEnd_last hlast', segmentParameterEnd_last hlast]
    norm_num
  · have hlast' : (i + 1) + 2 ≠ n + 1 := by omega
    rw [segmentParameterEnd_eq_start_succ hlast',
      segmentParameterEnd_eq_start_succ hlast,
      segmentParameterStart_succ]

/-- Helper toward Definition 3.2: each segment parameter interval has
positive length. -/
theorem segmentParameterStart_lt_end (n i : ℕ) :
    segmentParameterStart i < segmentParameterEnd n i := by
  by_cases hlast : i + 2 = n
  · rw [segmentParameterEnd_last hlast]
    simp only [segmentParameterStart]
    exact sub_lt_self 1 (pow_pos (by norm_num) _)
  · rw [segmentParameterEnd_eq_start_succ hlast]
    simp only [segmentParameterStart]
    rw [pow_succ]
    have hp : 0 < (1 / 2 : ℝ) ^ i := pow_pos (by norm_num) _
    nlinarith only [hp]

/-- Helper toward Definition 3.2: the first segment of a two-vertex
polyline is traversed affinely on the whole parameter interval. -/
theorem toPath_twoPoint_affine_apply (p : Polyline)
    (hlen : p.points.length = 2) (t : I) :
    p.toPath t = p.point 0 + (((t : ℝ) : ℂ) * (p.point 1 - p.point 0)) := by
  obtain ⟨pts, hpts⟩ := p
  cases pts with
  | nil => simp at hlen
  | cons a tail =>
    cases tail with
    | nil => simp at hlen
    | cons b rest =>
      cases rest with
      | nil =>
        simp only [Polyline.toPath, Polyline.listPath, Path.cast]
        change Path.segment a b t = _
        rw [Path.segment_apply, AffineMap.lineMap_apply_module']
        simp [Polyline.point, Polyline.start]
        ring
      | cons c rest => simp at hlen

/-- Helper toward Definition 3.2: the first segment of any polyline with at
least two vertices has the affine formula on its parameter interval. -/
theorem toPath_firstSegment_parameter_affine_apply (p : Polyline)
    (hlen : 2 ≤ p.points.length) (t : I)
    (ht : (t : ℝ) ≤ segmentParameterEnd p.points.length 0) :
    p.toPath t = p.point 0 +
      (((((t : ℝ) - segmentParameterStart 0) /
        (segmentParameterEnd p.points.length 0 - segmentParameterStart 0) : ℝ) : ℂ) *
        (p.point 1 - p.point 0)) := by
  rw [segmentParameterStart_zero]
  by_cases htwo : p.points.length = 2
  · have hend : segmentParameterEnd p.points.length 0 = 1 := by
      simp [segmentParameterEnd, htwo]
    have hformula := toPath_twoPoint_affine_apply p htwo t
    rw [hend]
    simpa using hformula
  · have hlen' : 2 < p.points.length := by omega
    have hne : 2 ≠ p.points.length := by omega
    have hend : segmentParameterEnd p.points.length 0 = 1 / 2 := by
      norm_num [segmentParameterEnd, hne]
    have ht' : (t : ℝ) ≤ 1 / 2 := by simpa [hend] using ht
    have hformula := toPath_firstSegment_affine_apply p hlen' t ht'
    rw [hend]
    have hcoeff : (t : ℝ) / (1 / 2 : ℝ) = 2 * (t : ℝ) := by
      norm_num
      ring
    simp only [sub_zero]
    rw [hcoeff]
    exact hformula

/-- Helper toward Definition 3.2: every segment of a polyline is traversed
affinely on its recursively halved parameter interval. -/
theorem toPath_segment_affine_apply (p : Polyline) {i : ℕ}
    (hi : i + 1 < p.points.length) :
    let a : ℝ := segmentParameterStart i
    let b : ℝ := segmentParameterEnd p.points.length i
    ∀ t : I, a ≤ (t : ℝ) → (t : ℝ) ≤ b →
      p.toPath t = p.point i +
        (((((t : ℝ) - a) / (b - a) : ℝ) : ℂ) *
          (p.point (i + 1) - p.point i)) := by
  change ∀ t : I, segmentParameterStart i ≤ (t : ℝ) →
    (t : ℝ) ≤ segmentParameterEnd p.points.length i →
      p.toPath t = p.point i +
        (((((t : ℝ) - segmentParameterStart i) /
          (segmentParameterEnd p.points.length i - segmentParameterStart i) : ℝ) : ℂ) *
          (p.point (i + 1) - p.point i))
  induction i generalizing p with
  | zero =>
    intro t hstart hend
    have hformula := toPath_firstSegment_parameter_affine_apply p (by omega) t hend
    simpa [segmentParameterStart_zero] using hformula
  | succ i ih =>
    obtain ⟨pts, hpts⟩ := p
    cases pts with
    | nil => simp at hi
    | cons a tail =>
      cases tail with
      | nil => simp at hi
      | cons b tail =>
        cases tail with
        | nil => simp at hi
        | cons c rest =>
          intro t hstart hend
          let p' : Polyline := ⟨a :: b :: c :: rest, hpts⟩
          change p'.toPath t = p'.point (i + 1) +
            (((((t : ℝ) - segmentParameterStart (i + 1)) /
              (segmentParameterEnd p'.points.length (i + 1) -
                segmentParameterStart (i + 1)) : ℝ) : ℂ) *
              (p'.point (i + 2) - p'.point (i + 1)))
          let q : Polyline := ⟨b :: c :: rest, by simp⟩
          have hlenrel : q.points.length + 1 = p'.points.length := by
            simp [q, p']
          have hiq : i + 1 < q.points.length := by
            simp [q] at hi ⊢
            omega
          have hend' : segmentParameterEnd p'.points.length (i + 1) =
              (1 + segmentParameterEnd q.points.length i) / 2 := by
            rw [← hlenrel]
            exact segmentParameterEnd_succ q.points.length i
          rw [segmentParameterStart_succ i] at hstart
          rw [hend'] at hend
          have hstart' : segmentParameterStart i ≤ 2 * (t : ℝ) - 1 := by
            linarith
          have hend'' : 2 * (t : ℝ) - 1 ≤ segmentParameterEnd q.points.length i := by
            linarith
          have hstart_nonneg : 0 ≤ segmentParameterStart i :=
            (segmentParameterStart_mem_Icc i).1
          have hend_le_one : segmentParameterEnd q.points.length i ≤ 1 :=
            (segmentParameterEnd_mem_Icc q.points.length i).2
          have ht' : 0 ≤ 2 * (t : ℝ) - 1 ∧ 2 * (t : ℝ) - 1 ≤ 1 :=
            ⟨le_trans hstart_nonneg hstart', le_trans hend'' hend_le_one⟩
          let t' : I := ⟨2 * (t : ℝ) - 1, ht'⟩
          have hIH := ih q hiq t' hstart' hend''
          have hpoint0 : p'.point (i + 1) = q.point i := by
            simpa [q, Polyline.ofHead] using
              (point_ofHead_succ a b (c :: rest) i (by simp [q] at hiq ⊢; omega))
          have hpoint1 : p'.point (i + 2) = q.point (i + 1) := by
            simpa [q, Polyline.ofHead] using
              (point_ofHead_succ a b (c :: rest) (i + 1)
                (by simp [q] at hiq ⊢; omega))
          by_cases hhalf : (t : ℝ) ≤ 1 / 2
          · cases i with
            | zero =>
              have htv : (t : ℝ) = 1 / 2 := by
                rw [segmentParameterStart_zero] at hstart
                norm_num [segmentParameterStart_zero] at hstart
                linarith
              have hfirstEnd : segmentParameterEnd p'.points.length 0 = 1 / 2 := by
                have hn : 2 ≠ p'.points.length := by omega
                norm_num [segmentParameterEnd, hn]
              have hfirst := toPath_firstSegment_parameter_affine_apply p'
                (by omega) t (by simpa [hfirstEnd] using (le_of_eq htv))
              rw [hfirstEnd, segmentParameterStart_zero, htv] at hfirst
              have hval : p'.toPath t = p'.point 1 := by
                calc
                  p'.toPath t = p'.point 0 +
                      (((((1 / 2 : ℝ) - 0) / ((1 / 2 : ℝ) - 0) : ℝ) : ℂ) *
                        (p'.point 1 - p'.point 0)) := hfirst
                  _ = p'.point 1 := by norm_num
              rw [hval, htv, hpoint0, hpoint1]
              have hs1 : segmentParameterStart 1 = 1 / 2 := by
                norm_num [segmentParameterStart]
              rw [hs1]
              have hn : (1 / 2 : ℝ) - (1 / 2 : ℝ) = 0 := by ring
              rw [hn]
              simp
            | succ j =>
              have hpow : (1 / 2 : ℝ) ^ (j + 1) ≤ 1 / 2 := by
                rw [pow_succ]
                have hpow' : (1 / 2 : ℝ) ^ j ≤ 1 :=
                  pow_le_one₀ (by norm_num) (by norm_num)
                nlinarith [hpow']
              have hs : 1 / 2 ≤ segmentParameterStart (j + 1) := by
                simp only [segmentParameterStart]
                linarith
              linarith
          · let t' : I := ⟨2 * (t : ℝ) - 1, ht'⟩
            have hpath : p'.toPath t = q.toPath t' := by
              change ((Path.segment a b).trans (Polyline.listPath b (c :: rest))) t =
                q.toPath t'
              rw [Path.trans_apply]
              split
              · rename_i h
                exact (hhalf h).elim
              · simp only [Polyline.toPath, Path.cast]
                rfl
            have hcoeff :
                ((2 * (t : ℝ) - 1 - segmentParameterStart i) /
                    (segmentParameterEnd q.points.length i - segmentParameterStart i)) =
                  (((t : ℝ) - segmentParameterStart (i + 1)) /
                    (segmentParameterEnd p'.points.length (i + 1) -
                      segmentParameterStart (i + 1))) := by
              rw [segmentParameterStart_succ i, hend']
              have hden : segmentParameterEnd q.points.length i -
                  segmentParameterStart i ≠ 0 :=
                ne_of_gt (sub_pos.mpr (segmentParameterStart_lt_end q.points.length i))
              field_simp [hden]
              ring
            rw [hpath, hIH, hpoint0, hpoint1, hcoeff]

































end Polyline

end DirectedDistances.PlanarMap

end
