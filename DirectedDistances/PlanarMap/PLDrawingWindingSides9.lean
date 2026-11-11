/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingWindingSides8
import DirectedDistances.PlanarMap.GeneralPlaneMapOrientedSideTransport

/-! # Winding sides at PL segment contacts

Helpers toward Definition 3.2. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

namespace PLDrawing

/-- Helper toward Definition 3.2: an open segment point has a unique
strictly interior affine coordinate. -/
private theorem openSegment_affine_coordinate (a b x : ℂ)
    (hx : x ∈ openSegment ℝ a b) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ x = a + (r : ℂ) * (b - a) := by
  rw [openSegment_eq_image_lineMap] at hx
  obtain ⟨r, hr, hx⟩ := hx
  refine ⟨r, hr.1, hr.2, ?_⟩
  rw [AffineMap.lineMap_apply_module] at hx
  rw [Complex.real_smul] at hx
  calc
    x = ((1 - r : ℝ) : ℂ) * a + (r : ℂ) * b := hx.symm
    _ = a + (r : ℂ) * (b - a) := by push_cast; ring

/-- Helper toward Definition 3.2: affine coordinates on a nondegenerate
segment are unique. -/
private theorem affine_coordinate_unique {a u : ℂ} (hu : u ≠ 0)
    {r t : ℝ} (h : a + (r : ℂ) * u = a + (t : ℂ) * u) : r = t := by
  have hmul : ((r : ℂ) - (t : ℂ)) * u = 0 := by
    have hc := congrArg (fun z : ℂ => z - a) h
    simp only [add_sub_cancel_left] at hc
    rw [sub_mul, hc, sub_self]
  rcases mul_eq_zero.mp hmul with hrt | hzero
  · exact_mod_cast sub_eq_zero.mp hrt
  · exact (hu hzero).elim

/-- Helper toward Definition 3.2: each strict interior affine coordinate
selects a parameter in the corresponding recursively halved PL segment. -/
private def parameterAtSegmentFraction (p : Polyline) (i : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (hr' : r ≤ 1) : I :=
  ⟨Polyline.segmentParameterStart i + r *
      (Polyline.segmentParameterEnd p.points.length i -
        Polyline.segmentParameterStart i), by
    have hs := Polyline.segmentParameterStart_mem_Icc i
    have he := Polyline.segmentParameterEnd_mem_Icc p.points.length i
    have hlen := Polyline.segmentParameterStart_le_end p.points.length i
    constructor
    · have hprod : 0 ≤ r *
          (Polyline.segmentParameterEnd p.points.length i -
            Polyline.segmentParameterStart i) :=
        mul_nonneg hr (sub_nonneg.mpr hlen)
      linarith
    · have hprod : 0 ≤ (1 - r) *
          (1 - Polyline.segmentParameterStart i) :=
        mul_nonneg (sub_nonneg.mpr hr') (sub_nonneg.mpr hs.2)
      have hprod' : 0 ≤ r *
          (1 - Polyline.segmentParameterEnd p.points.length i) :=
        mul_nonneg hr (sub_nonneg.mpr he.2)
      change Polyline.segmentParameterStart i + r *
          (Polyline.segmentParameterEnd p.points.length i -
            Polyline.segmentParameterStart i) ≤ 1
      nlinarith [hprod, hprod']⟩

/-- Helper toward Definition 3.2: the parameter selected by an affine
coordinate evaluates to that same point on the PL segment. -/
private theorem toPath_parameterAtSegmentFraction (p : Polyline) {i : ℕ}
    (hi : i + 1 < p.points.length) (r : ℝ) (hr : 0 ≤ r) (hr' : r ≤ 1) :
    p.toPath (parameterAtSegmentFraction p i r hr hr') =
      p.point i + (r : ℂ) * (p.point (i + 1) - p.point i) := by
  have hparam := Polyline.toPath_segment_affine_apply p hi
  have hstart : Polyline.segmentParameterStart i ≤
      (parameterAtSegmentFraction p i r hr hr' : ℝ) := by
    simp only [parameterAtSegmentFraction]
    have hlen := Polyline.segmentParameterStart_le_end p.points.length i
    nlinarith
  have hend : (parameterAtSegmentFraction p i r hr hr' : ℝ) ≤
      Polyline.segmentParameterEnd p.points.length i := by
    simp only [parameterAtSegmentFraction]
    have hlen := Polyline.segmentParameterStart_le_end p.points.length i
    nlinarith
  have h := hparam (parameterAtSegmentFraction p i r hr hr') hstart hend
  change p.toPath (parameterAtSegmentFraction p i r hr hr') = _
  rw [h]
  have hlen : 0 < Polyline.segmentParameterEnd p.points.length i -
      Polyline.segmentParameterStart i :=
    sub_pos.mpr (Polyline.segmentParameterStart_lt_end p.points.length i)
  have hratio :
      (((parameterAtSegmentFraction p i r hr hr' : ℝ) -
          Polyline.segmentParameterStart i) /
        (Polyline.segmentParameterEnd p.points.length i -
          Polyline.segmentParameterStart i)) = r := by
    simp only [parameterAtSegmentFraction]
    field_simp
    ring
  rw [hratio]

/-- Helper toward Definition 3.2: the local left return loop is attached to
the PL arc at every parameter strictly inside one of its segments. -/
theorem dartBorders_toPath_leftAtOn_of_parameter_in_segment
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (s : {t : I // t ∈ openParams}) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length)
    (hstart : Polyline.segmentParameterStart i < (s.1 : ℝ))
    (hend : (s.1 : ℝ) < Polyline.segmentParameterEnd (P.arc d).points.length i) :
    LeftAtOn F.val (P.arc d).toPath s := by
  let p := P.arc d
  let u := p.point (i + 1) - p.point i
  let x := p.toPath s.1
  have hx := Polyline.toPath_mem_openSegment_of_parameter p hi s.1 hstart hend
  obtain ⟨r, hr0, hr1, hxcoord⟩ :=
    openSegment_affine_coordinate (p.point i) (p.point (i + 1)) x hx
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i hi).symm
  have hform := Polyline.toPath_segment_affine_apply p hi
  dsimp only at hform
  have hform' := hform s.1 (le_of_lt hstart) (le_of_lt hend)
  let θ : ℝ := ((s.1 : ℝ) - Polyline.segmentParameterStart i) /
    (Polyline.segmentParameterEnd p.points.length i -
      Polyline.segmentParameterStart i)
  have hpath : p.toPath s.1 = p.point i + (θ : ℂ) * u := by
    simpa only [u, θ] using hform'
  have hratio : θ = r := by
    apply affine_coordinate_unique hu
    calc
      p.point i + (θ : ℂ) * u = p.toPath s.1 := hpath.symm
      _ = x := rfl
      _ = p.point i + (r : ℂ) * u := hxcoord
  have hratio' :
      (((s.1 : ℝ) - Polyline.segmentParameterStart i) /
        (Polyline.segmentParameterEnd p.points.length i -
          Polyline.segmentParameterStart i)) = r := hratio
  obtain ⟨ε, hε, hleft, hright, hinj, hopen, hcl⟩ :=
    P.dartBorders_openSegment_semicircleLoop hvert d F hborder hi x hx
  obtain ⟨rl, hrl0, hrl1, hleftcoord⟩ :=
    openSegment_affine_coordinate (p.point i) (p.point (i + 1))
      (x - ε • u) hleft
  obtain ⟨rr, hrr0, hrr1, hrightcoord⟩ :=
    openSegment_affine_coordinate (p.point i) (p.point (i + 1))
      (x + ε • u) hright
  have hleftformula : x - ε • u =
      p.point i + ((r - ε : ℝ) : ℂ) * u := by
    rw [hxcoord, Complex.real_smul]
    push_cast
    ring
  have hrightformula : x + ε • u =
      p.point i + ((r + ε : ℝ) : ℂ) * u := by
    rw [hxcoord, Complex.real_smul]
    push_cast
    ring
  have hrl : rl = r - ε :=
    affine_coordinate_unique hu (hleftcoord.symm.trans hleftformula)
  have hrr : rr = r + ε :=
    affine_coordinate_unique hu (hrightcoord.symm.trans hrightformula)
  let a := parameterAtSegmentFraction p i (r - ε) (by linarith) (by linarith)
  let b := parameterAtSegmentFraction p i (r + ε) (by linarith) (by linarith)
  have haEval : p.toPath a = x - ε • u := by
    have h := toPath_parameterAtSegmentFraction p hi (r - ε) (by linarith) (by linarith)
    change p.toPath (parameterAtSegmentFraction p i (r - ε) _ _) = _
    rw [h, hleftformula]
  have hbEval : p.toPath b = x + ε • u := by
    have h := toPath_parameterAtSegmentFraction p hi (r + ε) (by linarith) (by linarith)
    change p.toPath (parameterAtSegmentFraction p i (r + ε) _ _) = _
    rw [h, hrightformula]
  have hlen : 0 < Polyline.segmentParameterEnd p.points.length i -
      Polyline.segmentParameterStart i :=
    sub_pos.mpr (Polyline.segmentParameterStart_lt_end p.points.length i)
  have hsval : (s.1 : ℝ) = Polyline.segmentParameterStart i + r *
      (Polyline.segmentParameterEnd p.points.length i -
        Polyline.segmentParameterStart i) := by
    have hratio'' := (div_eq_iff (ne_of_gt hlen)).mp hratio'
    linarith
  have hab : a < b := by
    change (a : ℝ) < (b : ℝ)
    dsimp [a, b, parameterAtSegmentFraction]
    nlinarith [mul_pos hε hlen]
  have has : a < s.1 := by
    change (a : ℝ) < (s.1 : ℝ)
    dsimp [a, parameterAtSegmentFraction]
    rw [hsval]
    nlinarith [mul_pos hε hlen]
  have hsb : s.1 < b := by
    change (s.1 : ℝ) < (b : ℝ)
    dsimp [b, parameterAtSegmentFraction]
    rw [hsval]
    nlinarith [mul_pos hε hlen]
  have hfracA : 0 < r - ε := by rw [← hrl]; exact hrl0
  have hfracB : r + ε < 1 := by rw [← hrr]; exact hrr1
  have ha : 0 < (a : ℝ) := by
    change 0 < Polyline.segmentParameterStart i + (r - ε) *
      (Polyline.segmentParameterEnd p.points.length i -
        Polyline.segmentParameterStart i)
    exact lt_of_le_of_lt (Polyline.segmentParameterStart_mem_Icc i).1
      (by nlinarith [mul_pos hfracA hlen])
  have hb : (b : ℝ) < 1 := by
    have hbend : (b : ℝ) < Polyline.segmentParameterEnd p.points.length i := by
      change Polyline.segmentParameterStart i + (r + ε) *
        (Polyline.segmentParameterEnd p.points.length i -
          Polyline.segmentParameterStart i) < _
      exact (by nlinarith [mul_pos (sub_pos.mpr hfracB) hlen])
    exact lt_of_lt_of_le hbend (Polyline.segmentParameterEnd_mem_Icc
      p.points.length i).2
  have hstartA : Polyline.segmentParameterStart i ≤ (a : ℝ) := by
    change Polyline.segmentParameterStart i ≤ Polyline.segmentParameterStart i +
      (r - ε) * (Polyline.segmentParameterEnd p.points.length i -
        Polyline.segmentParameterStart i)
    exact le_add_of_nonneg_right (mul_nonneg (le_of_lt hfracA) hlen.le)
  have hBend : (b : ℝ) ≤ Polyline.segmentParameterEnd p.points.length i := by
    change Polyline.segmentParameterStart i + (r + ε) *
      (Polyline.segmentParameterEnd p.points.length i -
        Polyline.segmentParameterStart i) ≤ _
    have hmul := mul_le_mul_of_nonneg_right (le_of_lt hfracB) hlen.le
    nlinarith [hmul]
  have hline : ∀ t : I, a ≤ t → t ≤ b →
      p.toPath t = p.toPath a +
        (((((t : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)) : ℝ) : ℂ) *
          (p.toPath b - p.toPath a)) := by
    intro t hta htb
    have ht0 := hform t
      (le_trans hstartA (by exact_mod_cast hta))
      (le_trans (by exact_mod_cast htb) hBend)
    have hdenab : (b : ℝ) - (a : ℝ) = 2 * ε *
        (Polyline.segmentParameterEnd p.points.length i -
          Polyline.segmentParameterStart i) := by
      dsimp [a, b, parameterAtSegmentFraction]
      ring
    have hratio_t :
        ((t : ℝ) - Polyline.segmentParameterStart i) /
            (Polyline.segmentParameterEnd p.points.length i -
              Polyline.segmentParameterStart i) =
          (r - ε) + (((t : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))) * (2 * ε) := by
      rw [hdenab]
      dsimp [a, b, parameterAtSegmentFraction]
      field_simp [ne_of_gt hlen, hε.ne']
      ring
    have hratioC :
        (((((t : ℝ) - Polyline.segmentParameterStart i) /
          (Polyline.segmentParameterEnd p.points.length i -
            Polyline.segmentParameterStart i)) : ℝ) : ℂ) =
          (((r - ε) + (((t : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))) *
            (2 * ε) : ℝ) : ℂ) := by
      exact congrArg (fun z : ℝ => (z : ℂ)) hratio_t
    rw [ht0, haEval, hbEval, hleftformula, hrightformula]
    rw [hratioC]
    dsimp [u]
    push_cast
    ring_nf
  let φ : I → I := fun t => ⟨
    (((min (max t a) b : I) : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)), by
      have hca : a ≤ min (max t a) b := le_min (le_max_right _ _) hab.le
      have hcb : min (max t a) b ≤ b := min_le_right _ _
      constructor
      · exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hca))
          (sub_nonneg.mpr (by exact_mod_cast hab.le))
      · rw [div_le_one (sub_pos.mpr (by exact_mod_cast hab))]
        exact sub_le_sub_right (by exact_mod_cast hcb) _⟩
  have hφc : Continuous φ := by
    dsimp [φ]
    fun_prop
  have hφ0 : φ 0 = 0 := by
    apply Subtype.ext
    simp [φ, min_eq_left hab.le]
  have hφ1 : φ 1 = 1 := by
    apply Subtype.ext
    have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    have hden : (b : ℝ) - (a : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hab')
    change (((min (max (1 : I) a) b : I) : ℝ) - (a : ℝ)) /
      ((b : ℝ) - (a : ℝ)) = 1
    rw [max_eq_left (show a ≤ (1 : I) from a.property.2)]
    have hmin : min (1 : I) b = b := min_eq_right b.property.2
    rw [hmin]
    exact div_self hden
  have hEdgeFun : ∀ t : I,
      (edgeSubarc p.toPath a b (le_of_lt hab)).cast
        haEval.symm hbEval.symm t =
          Path.segment (x - ε • u) (x + ε • u) (φ t) := by
    intro t
    change edgeSubarc p.toPath a b (le_of_lt hab) t = _
    rw [edgeSubarc_affine_apply p.toPath hab hline t]
    rw [Path.segment_apply, AffineMap.lineMap_apply_module']
    simp only [Complex.real_smul]
    rw [haEval, hbEval]
    dsimp [φ]
    push_cast
    ring_nf
  have hEdge :
      (edgeSubarc p.toPath a b (le_of_lt hab)).cast haEval.symm hbEval.symm =
        (Path.segment (x - ε • u) (x + ε • u)).reparam φ hφc hφ0 hφ1 := by
    apply Path.ext
    funext t
    exact hEdgeFun t
  let q : Path (p.toPath b) (p.toPath a) :=
    (leftSemicircle x (ε • u)).cast hbEval haEval
  have hqinj : Function.Injective q := by
    intro t t' htt'
    exact hinj htt'
  have hqF : ∀ t : I, t ∈ openParams → q t ∈ F.val := by
    intro t ht
    exact hopen t ht
  let α : Path (x - ε • u) (x + ε • u) := Path.segment _ _
  let β : Path (x + ε • u) (x - ε • u) := leftSemicircle x (ε • u)
  let E : Path (x - ε • u) (x + ε • u) :=
    (edgeSubarc p.toPath a b (le_of_lt hab)).cast haEval.symm hbEval.symm
  let L : Path (p.toPath a) (p.toPath a) :=
    (edgeSubarc p.toPath a b (le_of_lt hab)).trans q
  let M : Path (x - ε • u) (x - ε • u) := E.trans β
  let N : Path (x - ε • u) (x - ε • u) :=
    ((Path.segment (x - ε • u) (x + ε • u)).reparam φ hφc hφ0 hφ1).trans β
  have hMN : M = N := by
    dsimp [M, N, E, α, β]
    exact congrArg (fun γ : Path _ _ => γ.trans (leftSemicircle x (ε • u))) hEdge
  have hLM : ∀ t : I, L t = M t := by
    intro t
    change ((edgeSubarc p.toPath a b (le_of_lt hab)).trans q) t =
      (((edgeSubarc p.toPath a b (le_of_lt hab)).cast
        haEval.symm hbEval.symm).trans β) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs <;> rfl
  have hwind : ∀ w : ℂ,
      HasWinding (semicircleLoop x (ε • u)) w 1 → HasWinding L w 1 := by
    intro w hw
    have hn : HasWinding N w 1 := by
      have h' := HasWinding.trans_reparam_left hw φ hφc hφ0 hφ1
      simpa [N, semicircleLoop, β] using h'
    have hm : HasWinding M w 1 :=
      (hasWinding_congr_fun M N w 1
        (fun t => congrArg (fun γ : Path _ _ => γ t) hMN)).mpr hn
    exact (hasWinding_congr_fun L M w 1 hLM).mpr hm
  have hsubset :
      {w : ℂ | w ∈ F.val ∧ HasWinding (semicircleLoop x (ε • u)) w 1} ⊆
        {w : ℂ | w ∈ F.val ∧ HasWinding L w 1} := by
    intro w hw
    exact ⟨hw.1, hwind w hw.2⟩
  have hcl' := closure_mono hsubset hcl
  refine ⟨a, b, ha, has, hsb, hb, q, hqinj, hqF, ?_⟩
  exact hcl'

























end PLDrawing

end DirectedDistances.PlanarMap

end
