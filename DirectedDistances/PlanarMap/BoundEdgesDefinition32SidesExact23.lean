/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact22

/-! # Constructive oriented edge extraction toward Definition 3.2

This file strengthens the image-only extraction in SidesExact20 at the
indexed-edge case needed by SidesExact21. The witness has a constructive
two-vertex list, so the original oriented edge is its first edge. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval Set Metric
open scoped Topology

/-- Helper toward Definition 3.2: when the selected subarc has the two
endpoints of an original oriented edge, it has a simple polygonal witness
whose vertex list is exactly those endpoints and whose first edge is the
original edge. -/
theorem Polyline.exists_simple_polyline_image_edgeSubarc_contains_original_edge32
    (p : Polyline) (hp : p.IsSimple) (hlen : 2 ≤ p.points.length)
    (a b : I) (hab : a < b) (i : ℕ)
    (ha : p.toPath a = p.point i)
    (hb : p.toPath b = p.point (i + 1))
    (hi : i + 1 < p.points.length) (x : ℂ)
    (hx : x ∈ p.segmentAt i)
    (hxi : x ≠ p.point i) (hxi1 : x ≠ p.point (i + 1)) :
    ∃ r : Polyline, r.IsSimple ∧ r.start = p.toPath a ∧
      r.finish = p.toPath b ∧ 2 ≤ r.points.length ∧
      r.points = [p.point i, p.point (i + 1)] ∧
      r.image = Set.range (edgeSubarc p.toPath a b hab.le) ∧
      ∃ j : ℕ, j + 1 < r.points.length ∧
        r.point j = p.point i ∧ r.point (j + 1) = p.point (i + 1) ∧
        x ∈ r.segmentAt j := by
  have hpi : Function.Injective p.toPath := p.toPath_injective hlen hp
  have hxy : p.point i ≠ p.point (i + 1) := hp.1 i hi
  let a₀ : I := ⟨Polyline.segmentParameterStart i,
    Polyline.segmentParameterStart_mem_Icc i⟩
  let b₀ : I := ⟨Polyline.segmentParameterEnd p.points.length i,
    Polyline.segmentParameterEnd_mem_Icc p.points.length i⟩
  have hparam := Polyline.toPath_segment_affine_apply p hi
  have ha₀ : p.toPath a₀ = p.point i := by
    have h := hparam a₀ le_rfl (by
      exact_mod_cast (Polyline.segmentParameterStart_le_end p.points.length i))
    simpa only [a₀, sub_self, zero_div, Complex.ofReal_zero, zero_mul, add_zero] using h
  have hb₀ : p.toPath b₀ = p.point (i + 1) := by
    have h := hparam b₀ (by
      exact_mod_cast (Polyline.segmentParameterStart_le_end p.points.length i))
      le_rfl
    have hden : Polyline.segmentParameterEnd p.points.length i -
        Polyline.segmentParameterStart i ≠ 0 :=
      ne_of_gt (sub_pos.mpr (Polyline.segmentParameterStart_lt_end p.points.length i))
    have h' : p.toPath b₀ = p.point i +
        (p.point (i + 1) - p.point i) := by
      simpa only [b₀, div_self hden, Complex.ofReal_one, one_mul] using h
    calc
      p.toPath b₀ = p.point i + (p.point (i + 1) - p.point i) := h'
      _ = p.point (i + 1) := by abel
  have ha_eq : a = a₀ := hpi (ha.trans ha₀.symm)
  have hb_eq : b = b₀ := hpi (hb.trans hb₀.symm)
  have ha_val : (a : ℝ) = Polyline.segmentParameterStart i := by
    exact congrArg Subtype.val ha_eq
  have hb_val : (b : ℝ) = Polyline.segmentParameterEnd p.points.length i := by
    exact congrArg Subtype.val hb_eq
  have hline : ∀ u : I, a ≤ u → u ≤ b →
      p.toPath u = p.toPath a +
        (((((u : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)) : ℝ) : ℂ) *
          (p.toPath b - p.toPath a)) := by
    intro u hau hub
    have hauR : Polyline.segmentParameterStart i ≤ (u : ℝ) := by
      rw [← ha_val]
      exact_mod_cast hau
    have hubR : (u : ℝ) ≤ Polyline.segmentParameterEnd p.points.length i := by
      rw [← hb_val]
      exact_mod_cast hub
    have hu := hparam u hauR hubR
    rw [ha, hb, ha_val, hb_val]
    exact hu
  have hsegment : segment ℝ (p.toPath a) (p.toPath b) = p.segmentAt i := by
    rw [ha, hb]
    rfl
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
      mul_right_cancel₀
        (sub_ne_zero.mpr (by simpa only [ha, hb] using hxy.symm)) hmul
    exact Subtype.ext (by exact_mod_cast hstval)
  have hδsub : Set.range δ ⊆ Set.range p.toPath := by
    change Set.range (Path.segment (p.toPath a) (p.toPath b)) ⊆ Set.range p.toPath
    rw [Path.range_segment, p.range_toPath, hsegment]
    exact p.segmentAt_subset_image hi
  have him := range_injective_path_subset_arc_eq_image_Icc32
    p.toPath hpi a b hab.le δ hδinj hδsub
  have hδedge : Set.range δ = Set.range (edgeSubarc p.toPath a b hab.le) := by
    rw [range_edgeSubarc_eq_image_Icc32]
    exact him
  have hxy' : p.toPath a ≠ p.toPath b := by
    intro h
    apply hxy
    rw [← ha, ← hb]
    exact h
  let r : Polyline := ⟨[p.toPath a, p.toPath b], by simp⟩
  have hrs : r.start = p.toPath a := by simp [r, Polyline.start]
  have hrf : r.finish = p.toPath b := by simp [r, Polyline.finish]
  have hrimage : r.image = segment ℝ (p.toPath a) (p.toPath b) := by
    ext z
    constructor
    · intro hz
      change z = r.start ∨ ∃ j, j + 1 < r.points.length ∧ z ∈ r.segmentAt j at hz
      rcases hz with hz | ⟨j, hj, hz⟩
      · subst z
        rw [hrs]
        exact left_mem_segment ℝ _ _
      · have hj0 : j = 0 := by simp [r] at hj; omega
        subst j
        simpa [r, Polyline.segmentAt, Polyline.point, Polyline.start] using hz
    · intro hz
      refine Or.inr ⟨0, by simp [r], ?_⟩
      simpa [r, Polyline.segmentAt, Polyline.point, Polyline.start] using hz
  have hrim : r.image = Set.range δ := by
    change r.image = Set.range (Path.segment (p.toPath a) (p.toPath b))
    rw [Path.range_segment]
    exact hrimage
  have hrsimple : r.IsSimple := by
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      have hj0 : j = 0 := by simp [r] at hj; omega
      subst j
      simpa [r, Polyline.point, Polyline.start] using hxy'
    · intro j hj
      simp [r] at hj
    · intro j k hj hk hjk
      have hj' : j + 1 < 2 := by simpa [r] using hj
      have hk' : k + 1 < 2 := by simpa [r] using hk
      omega
  refine ⟨r, hrsimple,
    hrs, hrf, ?_, ?_, hrim.trans hδedge, 0, ?_, ?_, ?_, ?_⟩
  · simp [r]
  · simp only [r, ha, hb]
  · simp [r]
  · change p.toPath a = p.point i
    exact ha
  · change p.toPath b = p.point (i + 1)
    exact hb
  · change x ∈ segment ℝ (p.toPath a) (p.toPath b)
    rw [ha, hb]
    exact hx

end DirectedDistances.PlanarMap

end
