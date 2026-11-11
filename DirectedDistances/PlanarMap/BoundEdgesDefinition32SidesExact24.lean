/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact23
import DirectedDistances.PlanarMap.D39PLCornerAccessArc







public section
noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval Set Metric
open scoped Topology

/-- Helper toward Definition 3.2: a subinterval contained in one segment
has a simple two-vertex extraction with the same image, and its first
oriented edge lies on that original segment. -/
theorem Polyline.exists_simple_polyline_image_edgeSubarc_within_segment32
    (p : Polyline) (hp : p.IsSimple) (hlen : 2 ≤ p.points.length)
    (i : ℕ) (hi : i + 1 < p.points.length) (a b : I) (hab : a < b)
    (ha : Polyline.segmentParameterStart i ≤ (a : ℝ))
    (hb : (b : ℝ) ≤ Polyline.segmentParameterEnd p.points.length i) :
    ∃ r : Polyline, r.IsSimple ∧ r.start = p.toPath a ∧
      r.finish = p.toPath b ∧ 2 ≤ r.points.length ∧
      r.points = [p.toPath a, p.toPath b] ∧
      r.image = Set.range (edgeSubarc p.toPath a b hab.le) ∧
      r.segmentAt 0 ⊆ p.segmentAt i := by
  have hpi : Function.Injective p.toPath := p.toPath_injective hlen hp
  have habR : (a : ℝ) < b := hab
  have hstartEnd : Polyline.segmentParameterStart i <
      Polyline.segmentParameterEnd p.points.length i :=
    Polyline.segmentParameterStart_lt_end p.points.length i
  have hden : Polyline.segmentParameterEnd p.points.length i -
      Polyline.segmentParameterStart i ≠ 0 :=
    ne_of_gt (sub_pos.mpr hstartEnd)
  have hpoint_mem (t : I) (ht0 : Polyline.segmentParameterStart i ≤ (t : ℝ))
      (ht1 : (t : ℝ) ≤ Polyline.segmentParameterEnd p.points.length i) :
      p.toPath t ∈ p.segmentAt i := by
    let u : ℝ := ((t : ℝ) - Polyline.segmentParameterStart i) /
      (Polyline.segmentParameterEnd p.points.length i - Polyline.segmentParameterStart i)
    have hu0 : 0 ≤ u := div_nonneg (sub_nonneg.mpr ht0) (sub_nonneg.mpr hstartEnd.le)
    have hu1 : u ≤ 1 := by
      dsimp [u]
      apply (div_le_one (sub_pos.mpr hstartEnd)).2
      linarith
    rw [Polyline.segmentAt, segment_eq_image']
    refine ⟨u, ⟨hu0, hu1⟩, ?_⟩
    have hparam := Polyline.toPath_segment_affine_apply p hi t ht0 ht1
    rw [hparam]
    simp only [u, Complex.real_smul]
  have haend : (a : ℝ) ≤ Polyline.segmentParameterEnd p.points.length i :=
    le_trans (by exact_mod_cast hab.le) hb
  have hbstart : Polyline.segmentParameterStart i ≤ (b : ℝ) :=
    le_trans ha (by exact_mod_cast hab.le)
  have hpa := hpoint_mem a ha haend
  have hpb := hpoint_mem b hbstart hb
  have hxy : p.toPath a ≠ p.toPath b := by
    intro heq
    exact hab.ne (hpi heq)
  let δ : Path (p.toPath a) (p.toPath b) := Path.segment (p.toPath a) (p.toPath b)
  have hδinj : Function.Injective δ := by
    intro s t hst
    have hmul : ((s : ℝ) : ℂ) * (p.toPath b - p.toPath a) =
        ((t : ℝ) : ℂ) * (p.toPath b - p.toPath a) := by
      change Path.segment (p.toPath a) (p.toPath b) s =
        Path.segment (p.toPath a) (p.toPath b) t at hst
      have h := congrArg (fun z : ℂ => z - p.toPath a) hst
      simp only [Path.segment_apply, AffineMap.lineMap_apply_module',
        Complex.real_smul] at h
      simp only [add_sub_cancel_right] at h
      exact h
    have hstval : ((s : ℝ) : ℂ) = ((t : ℝ) : ℂ) :=
      mul_right_cancel₀ (sub_ne_zero.mpr hxy.symm) hmul
    exact Subtype.ext (by exact_mod_cast hstval)
  have hδsub : Set.range δ ⊆ Set.range p.toPath := by
    change Set.range (Path.segment (p.toPath a) (p.toPath b)) ⊆ Set.range p.toPath
    rw [Path.range_segment, p.range_toPath]
    intro z hz
    exact p.segmentAt_subset_image hi
      ((convex_segment _ _).segment_subset hpa hpb hz)
  have him := range_injective_path_subset_arc_eq_image_Icc32
    p.toPath hpi a b hab.le δ hδinj hδsub
  have hδedge : Set.range δ = Set.range (edgeSubarc p.toPath a b hab.le) := by
    rw [range_edgeSubarc_eq_image_Icc32]
    exact him
  let r : Polyline := Polyline.cornerSegment (p.toPath a) (p.toPath b)
  have hrs : r.start = p.toPath a := (Polyline.cornerSegment_data _ _).1
  have hrf : r.finish = p.toPath b := (Polyline.cornerSegment_data _ _).2.1
  have hrlen : 2 ≤ r.points.length := by simp [r, Polyline.cornerSegment]
  have hrim : r.image = Set.range δ := by
    change r.image = Set.range (Path.segment (p.toPath a) (p.toPath b))
    rw [Path.range_segment]
    exact Polyline.image_cornerSegment _ _
  have hfirst : r.segmentAt 0 = segment ℝ (p.toPath a) (p.toPath b) := by
    simp [r, Polyline.cornerSegment, Polyline.segmentAt, Polyline.point,
      Polyline.start]
  refine ⟨r, Polyline.isSimple_cornerSegment hxy, hrs, hrf, hrlen,
    ?_, hrim.trans hδedge, ?_⟩
  · simp [r, Polyline.cornerSegment]
  · rw [hfirst]
    exact (convex_segment _ _).segment_subset hpa hpb














































































end DirectedDistances.PlanarMap

end
