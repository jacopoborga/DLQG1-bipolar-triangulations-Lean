/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PLDrawingWindingSides16
public import DirectedDistances.PlanarMap.HasWindingTriangle
import DirectedDistances.PlanarMap.GeneralPlaneMapOrientedSideTransport

/-! # Triangle winding at a left turn -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology ComplexConjugate

/-- Helper toward Definition 3.2: positive cross products at a point give
winding one for a triangular loop. -/
theorem hasWinding_triangle_of_cross_pos {a b c w : ℂ}
    (hab : 0 < (conj (a - w) * (b - w)).im)
    (hbc : 0 < (conj (b - w) * (c - w)).im)
    (hca : 0 < (conj (c - w) * (a - w)).im) :
    HasWinding (((Path.segment a b).trans
      (Path.segment b c)).trans (Path.segment c a)) w 1 := by
  have ha : a - w ≠ 0 := by intro h; simp [h] at hab
  let A := Complex.log (a - w)
  let B := A + Complex.log ((b - w) / (a - w))
  let C := B + Complex.log ((c - w) / (b - w))
  have hA : Complex.exp A = a - w := Complex.exp_log ha
  obtain ⟨α, hα⟩ := exists_segment_log_lift hab hA
  have hB : Complex.exp B = b - w := by
    simpa only [Path.target] using hα 1
  obtain ⟨β, hβ⟩ := exists_segment_log_lift hbc hB
  have hC : Complex.exp C = c - w := by
    simpa only [Path.target] using hβ 1
  obtain ⟨γ, hγ⟩ := exists_segment_log_lift hca hC
  let Ψ : C(I, ℂ) := ((α.trans β).trans γ).toContinuousMap
  refine ⟨Ψ, exp_trans_of_exp_eq (exp_trans_of_exp_eq hα hβ) hγ, ?_⟩
  change ((α.trans β).trans γ) 1 - ((α.trans β).trans γ) 0 = _
  simp only [Path.target, Path.source, Int.cast_one, mul_one]
  calc
    C + Complex.log ((a - w) / (c - w)) - A =
        Complex.log ((b - w) / (a - w)) + Complex.log ((c - w) / (b - w)) +
          Complex.log ((a - w) / (c - w)) := by dsimp [C, B]; ring
    _ = 2 * Real.pi * Complex.I := triangle_log_ratio_sum hab hbc hca

/-- Helper toward Definition 3.2: cross products of a triangle cut from
two incident rays, evaluated on the interior bisector. -/
theorem bend_triangle_cross (b u v : ℂ) (r τ : ℝ) :
    (conj ((b - r • u) - (b + τ • (-u + v))) *
      (b - (b + τ • (-u + v)))).im = r * τ * (conj u * v).im ∧
    (conj (b - (b + τ • (-u + v))) *
      ((b + r • v) - (b + τ • (-u + v)))).im = r * τ * (conj u * v).im ∧
    (conj ((b + r • v) - (b + τ • (-u + v))) *
      ((b - r • u) - (b + τ • (-u + v)))).im =
      r * (r - 2 * τ) * (conj u * v).im := by
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.neg_re, Complex.neg_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  constructor
  · ring
  constructor <;> ring

namespace PLDrawing

/-- Helper toward Definition 3.2: at a strict left turn, the small
intersection of the two left half-disks belongs to the bordering face. -/
theorem dartBorders_bend_left_wedge_subset_face
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (hturn : 0 < (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im) :
    let b := (P.arc d).point (i + 1)
    let u := b - (P.arc d).point i
    let v := (P.arc d).point (i + 2) - b
    ∃ r : ℝ, 0 < r ∧ ∀ y : ℂ, y ∈ Metric.ball b r →
      0 < (star u * (y - b)).im → 0 < (star v * (y - b)).im → y ∈ F.val := by
  dsimp only
  let b := (P.arc d).point (i + 1)
  let u := b - (P.arc d).point i
  let v := (P.arc d).point (i + 2) - b
  obtain ⟨r, hr, hlocal⟩ := P.bend_contact_local_image hvert d hi
  let W := {y : ℂ | y ∈ Metric.ball b r ∧ 0 < (star u * (y - b)).im} ∩
    {y : ℂ | y ∈ Metric.ball b r ∧ 0 < (star v * (y - b)).im}
  have hWc : Convex ℝ W := by
    simpa only [one_mul] using
      (signed_halfDisk_convex b u r 1).inter (signed_halfDisk_convex b v r 1)
  have hWsafe : W ⊆ P.imageᶜ := by
    intro y hy hyP
    rcases (hlocal y hy.1.1).mp hyP with hleft | hright
    · have hz := segment_contact_side_eq_zero ((P.arc d).point i) b b y
        (right_mem_segment ℝ _ _) hleft
      exact (ne_of_gt hy.1.2) hz
    · have hz := segment_contact_side_eq_zero b ((P.arc d).point (i + 2)) b y
        (left_mem_segment ℝ _ _) hright
      exact (ne_of_gt hy.2.2) hz
  obtain ⟨δ, hδ, hface⟩ := P.dartBorders_bend_left_offsets_mem_face hvert d F hborder hi
  have hc : Continuous (fun ε : ℝ => (star u * v).im + ε * (star u * v).re) := by
    fun_prop
  have hn : (fun ε : ℝ => (star u * v).im + ε * (star u * v).re) ⁻¹'
      Set.Ioi 0 ∈ 𝓝 0 := hc.continuousAt.preimage_mem_nhds
        (isOpen_Ioi.mem_nhds (by
          simpa only [Set.mem_Ioi, zero_mul, add_zero, u, v, b] using hturn))
  obtain ⟨e, he, hepos⟩ := Metric.mem_nhds_iff.mp hn
  let ε := min (δ / 2) (e / 2)
  have hε : 0 < ε := lt_min (half_pos hδ) (half_pos he)
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hεe : ε < e := (min_le_right _ _).trans_lt (half_lt_self he)
  have hother : 0 < (star u * v).im + ε * (star u * v).re := by
    apply hepos
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε] using hεe
  let f : ℝ → ℂ := fun t => b + t • (-u + ε • (Complex.I * u))
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hfn : f ⁻¹' Metric.ball b r ∈ 𝓝 0 :=
    hf.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds
      (by simpa only [f, zero_smul, add_zero] using Metric.mem_ball_self hr))
  obtain ⟨e', he', hball⟩ := Metric.mem_nhds_iff.mp hfn
  let t := min (δ / 2) (e' / 2)
  have ht : 0 < t := lt_min (half_pos hδ) (half_pos he')
  have htδ : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hte : t < e' := (min_le_right _ _).trans_lt (half_lt_self he')
  have hfr : f t ∈ Metric.ball b r := by
    apply hball
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using hte
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i (by omega)).symm
  have hfu : 0 < (star u * (f t - b)).im := by
    have h := (bend_offset_sides u v 1 t ε).1
    simp only [one_smul, one_mul, one_pow, mul_one] at h
    dsimp only [f]
    rw [add_sub_cancel_left, h]
    exact mul_pos (mul_pos ht hε) (Complex.normSq_pos.mpr hu)
  have hfv : 0 < (star v * (f t - b)).im := by
    have h := (bend_offset_sides u v 1 t ε).2.2.1
    simp only [one_smul, one_mul, one_pow, mul_one] at h
    dsimp only [f]
    rw [add_sub_cancel_left, h]
    exact mul_pos ht hother
  have hfW : f t ∈ W := ⟨⟨hfr, hfu⟩, ⟨hfr, hfv⟩⟩
  have hfF : f t ∈ F.val := (hface t ε ht htδ hε hεδ).1
  have hWF : W ⊆ F.val := by
    obtain ⟨z, _, hF⟩ := F.property
    rw [hF] at hfF ⊢
    rw [connectedComponentIn_eq hfF]
    exact hWc.isPreconnected.subset_connectedComponentIn hfW hWsafe
  exact ⟨r, hr, fun y hyr hyu hyv => hWF ⟨⟨hyr, hyu⟩, ⟨hyr, hyv⟩⟩⟩

/-- Helper toward Definition 3.2: winding-one points of the bordering
face accumulate at a strict left bend for every positive triangle scale. -/
theorem dartBorders_bend_triangle_mem_closure_winding
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (hturn : 0 < (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im)
    (r : ℝ) (hr : 0 < r) :
    let b := (P.arc d).point (i + 1)
    let u := b - (P.arc d).point i
    let v := (P.arc d).point (i + 2) - b
    b ∈ closure {w : ℂ | w ∈ F.val ∧
      HasWinding (((Path.segment (b - r • u) b).trans
        (Path.segment b (b + r • v))).trans
        (Path.segment (b + r • v) (b - r • u))) w 1} := by
  dsimp only
  let b := (P.arc d).point (i + 1)
  let u := b - (P.arc d).point i
  let v := (P.arc d).point (i + 2) - b
  obtain ⟨R, hR, hface⟩ :=
    P.dartBorders_bend_left_wedge_subset_face hvert d F hborder hi hturn
  rw [Metric.mem_closure_iff]
  intro η hη
  let τ := min (r / 4) (min (R / (2 * (‖-u + v‖ + 1)))
    (η / (2 * (‖-u + v‖ + 1))))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτr : 2 * τ < r := by
    have h := min_le_left (r / 4) (min (R / (2 * (‖-u + v‖ + 1)))
      (η / (2 * (‖-u + v‖ + 1))))
    change τ ≤ r / 4 at h
    linarith only [h, hr]
  have hτR : τ * (2 * (‖-u + v‖ + 1)) ≤ R := by
    apply (le_div_iff₀ (by positivity)).mp
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hτη : τ * (2 * (‖-u + v‖ + 1)) ≤ η := by
    apply (le_div_iff₀ (by positivity)).mp
    exact (min_le_right _ _).trans (min_le_right _ _)
  let w := b + τ • (-u + v)
  have hdist : dist w b = τ * ‖-u + v‖ := by
    dsimp only [w]
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
  have hwR : w ∈ Metric.ball b R := by
    rw [Metric.mem_ball, hdist]
    nlinarith only [hτR, hτ, norm_nonneg (-u + v)]
  have hwu : (star u * (w - b)).im = τ * (star u * v).im := by
    dsimp only [w]
    simp only [add_sub_cancel_left, Complex.star_def, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.smul_re, Complex.smul_im,
      smul_eq_mul, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]
    ring
  have hwv : (star v * (w - b)).im = τ * (star u * v).im := by
    dsimp only [w]
    simp only [add_sub_cancel_left, Complex.star_def, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.smul_re, Complex.smul_im,
      smul_eq_mul, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]
    ring
  have hc : 0 < (star u * v).im := hturn
  have hwF : w ∈ F.val := hface w hwR
    (hwu.symm ▸ mul_pos hτ hc) (hwv.symm ▸ mul_pos hτ hc)
  obtain ⟨hab, hbc, hca⟩ := bend_triangle_cross b u v r τ
  have hwinding : HasWinding (((Path.segment (b - r • u) b).trans
      (Path.segment b (b + r • v))).trans
      (Path.segment (b + r • v) (b - r • u))) w 1 := by
    apply hasWinding_triangle_of_cross_pos
    · rw [show w = b + τ • (-u + v) from rfl, hab]
      exact mul_pos (mul_pos hr hτ) hc
    · rw [show w = b + τ • (-u + v) from rfl, hbc]
      exact mul_pos (mul_pos hr hτ) hc
    · rw [show w = b + τ • (-u + v) from rfl, hca]
      exact mul_pos (mul_pos hr (sub_pos.mpr hτr)) hc
  refine ⟨w, ⟨hwF, hwinding⟩, ?_⟩
  rw [dist_comm, hdist]
  nlinarith only [hτη, hτ, norm_nonneg (-u + v)]

/-- Helper toward Definition 3.2: a strict left bend admits a small
injective straight return chord in its bordering face, with winding-one
face points accumulating at the bend for the resulting triangle. -/
theorem dartBorders_bend_exists_triangle_return
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (hturn : 0 < (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im) :
    let b := (P.arc d).point (i + 1)
    let u := b - (P.arc d).point i
    let v := (P.arc d).point (i + 2) - b
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      Function.Injective (Path.segment (b + r • v) (b - r • u)) ∧
      (∀ t : I, t ∈ openParams →
        Path.segment (b + r • v) (b - r • u) t ∈ F.val) ∧
      b ∈ closure {w : ℂ | w ∈ F.val ∧
        HasWinding (((Path.segment (b - r • u) b).trans
          (Path.segment b (b + r • v))).trans
          (Path.segment (b + r • v) (b - r • u))) w 1} := by
  dsimp only
  let b := (P.arc d).point (i + 1)
  let u := b - (P.arc d).point i
  let v := (P.arc d).point (i + 2) - b
  obtain ⟨R, hR, hface⟩ :=
    P.dartBorders_bend_left_wedge_subset_face hvert d F hborder hi hturn
  let r := min (1 / 2 : ℝ) (R / (2 * (‖u‖ + ‖v‖ + 1)))
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hprod : r * (2 * (‖u‖ + ‖v‖ + 1)) ≤ R :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have haR : b - r • u ∈ Metric.ball b R := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg,
      norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith only [hprod, hr, norm_nonneg u, norm_nonneg v]
  have hcR : b + r • v ∈ Metric.ball b R := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith only [hprod, hr, norm_nonneg u, norm_nonneg v]
  have hc : 0 < (star u * v).im := hturn
  have hcrossu (t : I) :
      (star u * (Path.segment (b + r • v) (b - r • u) t - b)).im =
        r * (1 - (t : ℝ)) * (star u * v).im := by
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module,
      Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring
  have hcrossv (t : I) :
      (star v * (Path.segment (b + r • v) (b - r • u) t - b)).im =
        r * (t : ℝ) * (star u * v).im := by
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module,
      Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring
  have hinj : Function.Injective (Path.segment (b + r • v) (b - r • u)) := by
    intro s t heq
    have he := congrArg (fun z : ℂ => (star u * (z - b)).im) heq
    rw [hcrossu, hcrossu] at he
    have he' : (r * (star u * v).im) * (s : ℝ) =
        (r * (star u * v).im) * (t : ℝ) := by nlinarith only [he]
    exact Subtype.ext (mul_left_cancel₀ (ne_of_gt (mul_pos hr hc)) he')
  refine ⟨r, hr, hr1, hinj, ?_,
    P.dartBorders_bend_triangle_mem_closure_winding hvert d F hborder hi hturn r hr⟩
  intro t ht
  have ht0 : 0 < (t : ℝ) := ht.1
  have ht1 : (t : ℝ) < 1 := ht.2
  have htR : Path.segment (b + r • v) (b - r • u) t ∈ Metric.ball b R :=
    (convex_ball b R).segment_subset hcR haR (by
      rw [Path.segment_apply]
      exact lineMap_mem_segment ℝ _ _ t.2)
  apply hface _ htR
  · rw [hcrossu]
    exact mul_pos (mul_pos hr (sub_pos.mpr ht1)) hc
  · rw [hcrossv]
    exact mul_pos (mul_pos hr ht0) hc

end PLDrawing

/-- Helper toward Definition 3.2: a path affine on both sides of an
interior parameter has a paused subarc obtained by reparameterizing its
two straight segments. -/
theorem edgeSubarc_two_segments_reparam {x y : ℂ} (γ : Path x y)
    (a s b : I) (has : a < s) (hsb : s < b)
    (hleft : ∀ t : I, a ≤ t → t ≤ s →
      γ t = γ a + ((((t : ℝ) - a) / ((s : ℝ) - a) : ℝ) : ℂ) * (γ s - γ a))
    (hright : ∀ t : I, s ≤ t → t ≤ b →
      γ t = γ s + ((((t : ℝ) - s) / ((b : ℝ) - s) : ℝ) : ℂ) * (γ b - γ s)) :
    ∃ f : I → I, ∃ hc : Continuous f, ∃ h0 : f 0 = 0, ∃ h1 : f 1 = 1,
      edgeSubarc γ a b (has.trans hsb).le =
        ((Path.segment (γ a) (γ s)).trans (Path.segment (γ s) (γ b))).reparam f hc h0 h1 := by
  let c : I → I := fun t => min (max t a) b
  have has' : (a : ℝ) < (s : ℝ) := has
  have hsb' : (s : ℝ) < (b : ℝ) := hsb
  have hsa : (s : ℝ) - a ≠ 0 := sub_ne_zero.mpr has'.ne'
  have hbs : (b : ℝ) - s ≠ 0 := sub_ne_zero.mpr hsb'.ne'
  have hca (t : I) : a ≤ c t := le_min (le_max_right _ _) (has.trans hsb).le
  have hcb (t : I) : c t ≤ b := min_le_right _ _
  let l : I → ℝ := fun t => (((min (c t) s : I) : ℝ) - a) / ((s : ℝ) - a)
  let r : I → ℝ := fun t => (((max (c t) s : I) : ℝ) - s) / ((b : ℝ) - s)
  have hl (t : I) : 0 ≤ l t ∧ l t ≤ 1 := by
    dsimp only [l]
    constructor
    · exact div_nonneg (sub_nonneg.mpr (le_min (hca t) has.le)) (sub_pos.mpr has').le
    · rw [div_le_one (sub_pos.mpr has')]
      exact sub_le_sub_right (min_le_right _ _) _
  have hr (t : I) : 0 ≤ r t ∧ r t ≤ 1 := by
    dsimp only [r]
    constructor
    · exact div_nonneg (sub_nonneg.mpr (le_max_right _ _)) (sub_pos.mpr hsb').le
    · rw [div_le_one (sub_pos.mpr hsb')]
      exact sub_le_sub_right
        (show max (c t : ℝ) (s : ℝ) ≤ (b : ℝ) from max_le (hcb t) hsb.le) _
  let f : I → I := fun t => ⟨(l t + r t) / 2, by
    constructor <;> linarith only [(hl t).1, (hl t).2, (hr t).1, (hr t).2]⟩
  have hc : Continuous f := by dsimp [f, l, r, c]; fun_prop
  have h0 : f 0 = 0 := by
    apply Subtype.ext
    simp only [f, l, r, c, max_eq_right (show (0 : I) ≤ a from a.2.1),
      min_eq_left (has.trans hsb).le, min_eq_left has.le, max_eq_right has.le,
      sub_self, zero_div, add_zero]
    rfl
  have h1 : f 1 = 1 := by
    apply Subtype.ext
    simp only [f, l, r, c, max_eq_left (show a ≤ (1 : I) from a.2.2),
      min_eq_right (show b ≤ (1 : I) from b.2.2), min_eq_right hsb.le,
      max_eq_left hsb.le, div_self hsa, div_self hbs]
    norm_num
  refine ⟨f, hc, h0, h1, ?_⟩
  apply Path.ext
  funext t
  rw [edgeSubarc_apply_clamp]
  change γ (c t) = ((Path.segment (γ a) (γ s)).trans
    (Path.segment (γ s) (γ b))) (f t)
  rw [Path.trans_apply]
  by_cases hcs : c t ≤ s
  · have hcs' : (c t : ℝ) ≤ (s : ℝ) := hcs
    have hr0 : r t = 0 := by dsimp [r]; rw [max_eq_right hcs']; simp only [sub_self, zero_div]
    have hf : (f t : ℝ) ≤ 1 / 2 := by
      change (l t + r t) / 2 ≤ 1 / 2
      rw [hr0]
      linarith only [(hl t).2]
    rw [dite_eq_left hf, Path.segment_apply, AffineMap.lineMap_apply_module]
    rw [hleft (c t) (hca t) hcs]
    have hparam : (2 * (f t : ℝ)) = ((c t : ℝ) - a) / ((s : ℝ) - a) := by
      change 2 * ((l t + r t) / 2) = _
      rw [hr0]
      dsimp [l]
      rw [min_eq_left hcs']
      ring
    simp only [hparam, Complex.real_smul]
    push_cast
    ring
  · have hsc : s < c t := lt_of_not_ge hcs
    have hsc' : (s : ℝ) < (c t : ℝ) := hsc
    have hl1 : l t = 1 := by
      dsimp [l]
      rw [min_eq_right hsc'.le, div_self hsa]
    have hrpos : 0 < r t := by
      dsimp [r]
      rw [max_eq_left hsc'.le]
      exact div_pos (sub_pos.mpr (show (s : ℝ) < (c t : ℝ) from hsc)) (sub_pos.mpr hsb')
    have hf : ¬ (f t : ℝ) ≤ 1 / 2 := by
      change ¬ (l t + r t) / 2 ≤ 1 / 2
      rw [hl1]
      linarith only [hrpos]
    rw [dite_eq_right hf, Path.segment_apply, AffineMap.lineMap_apply_module]
    rw [hright (c t) hsc.le (hcb t)]
    have hparam : (2 * (f t : ℝ) - 1) = ((c t : ℝ) - s) / ((b : ℝ) - s) := by
      change 2 * ((l t + r t) / 2) - 1 = _
      rw [hl1]
      dsimp [r]
      rw [max_eq_left hsc'.le]
      ring
    simp only [hparam, Complex.real_smul]
    push_cast
    ring

namespace Polyline

/-- Helper toward Definition 3.2: restricting a polyline's affine segment
to a smaller parameter interval preserves its endpoint affine formula. -/
theorem toPath_affine_on_segment_subinterval (p : Polyline) {i : ℕ}
    (hi : i + 1 < p.points.length) (a b : I) (hab : a < b)
    (ha : segmentParameterStart i ≤ (a : ℝ))
    (hb : (b : ℝ) ≤ segmentParameterEnd p.points.length i) :
    ∀ t : I, a ≤ t → t ≤ b →
      p.toPath t = p.toPath a +
        ((((t : ℝ) - a) / ((b : ℝ) - a) : ℝ) : ℂ) * (p.toPath b - p.toPath a) := by
  intro t hat htb
  have hab' : (a : ℝ) < (b : ℝ) := hab
  have hat' : (a : ℝ) ≤ (t : ℝ) := hat
  have htb' : (t : ℝ) ≤ (b : ℝ) := htb
  have hden : segmentParameterEnd p.points.length i - segmentParameterStart i ≠ 0 :=
    (sub_pos.mpr (segmentParameterStart_lt_end p.points.length i)).ne'
  have hdenab : (b : ℝ) - a ≠ 0 := (sub_pos.mpr hab').ne'
  have hform := toPath_segment_affine_apply p hi
  dsimp only at hform
  rw [hform t (ha.trans hat') (htb'.trans hb), hform a ha (hab'.le.trans hb),
    hform b (ha.trans hab'.le) hb]
  have hratio : ((t : ℝ) - segmentParameterStart i) /
      (segmentParameterEnd p.points.length i - segmentParameterStart i) =
      ((a : ℝ) - segmentParameterStart i) /
        (segmentParameterEnd p.points.length i - segmentParameterStart i) +
      (((t : ℝ) - a) / ((b : ℝ) - a)) *
        (((b : ℝ) - segmentParameterStart i) /
          (segmentParameterEnd p.points.length i - segmentParameterStart i) -
        ((a : ℝ) - segmentParameterStart i) /
          (segmentParameterEnd p.points.length i - segmentParameterStart i)) := by
    field_simp
    ring
  rw [hratio]
  push_cast
  ring

end Polyline

namespace PLDrawing

/-- Helper toward Definition 3.2: a bordering face satisfies the winding
left-side test at a bend with strictly positive turn cross product. -/
theorem dartBorders_toPath_leftAtOn_of_bend_left_turn
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (s : {t : I // t ∈ openParams}) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (hbend : (s.1 : ℝ) = Polyline.segmentParameterStart (i + 1))
    (hturn : 0 < (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im) :
    LeftAtOn F.val (P.arc d).toPath s := by
  let p := P.arc d
  change i + 2 < p.points.length at hi
  let B := p.point (i + 1)
  let u := B - p.point i
  let v := p.point (i + 2) - B
  obtain ⟨r, hr, hr1, hinj, hqface, hcl⟩ :=
    P.dartBorders_bend_exists_triangle_return hvert d F hborder hi hturn
  let L := Polyline.segmentParameterStart i
  let M := Polyline.segmentParameterStart (i + 1)
  let H := Polyline.segmentParameterEnd p.points.length (i + 1)
  have hend : Polyline.segmentParameterEnd p.points.length i = M :=
    Polyline.segmentParameterEnd_eq_start_succ (by omega)
  have hLM : L < M := by
    rw [← hend]
    exact Polyline.segmentParameterStart_lt_end p.points.length i
  have hMH : M < H := Polyline.segmentParameterStart_lt_end p.points.length (i + 1)
  have hL0 : 0 ≤ L := (Polyline.segmentParameterStart_mem_Icc i).1
  have hH1 : H ≤ 1 := (Polyline.segmentParameterEnd_mem_Icc p.points.length (i + 1)).2
  let av := M - r * (M - L)
  let bv := M + r * (H - M)
  have hLa : L < av := by
    dsimp only [av]
    nlinarith only [mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hLM)]
  have haM : av < M := by
    dsimp only [av]
    linarith only [mul_pos hr (sub_pos.mpr hLM)]
  have hMb : M < bv := by
    dsimp only [bv]
    linarith only [mul_pos hr (sub_pos.mpr hMH)]
  have hbH : bv < H := by
    dsimp only [bv]
    nlinarith only [mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hMH)]
  let a : I := ⟨av, ⟨hL0.trans hLa.le, haM.le.trans (hMH.le.trans hH1)⟩⟩
  let b : I := ⟨bv, ⟨(hL0.trans hLM.le).trans hMb.le, hbH.le.trans hH1⟩⟩
  have ha : (0 : I) < a := hL0.trans_lt hLa
  have hb : b < (1 : I) := hbH.trans_le hH1
  have has : a < s.1 := by change av < (s.1 : ℝ); rw [hbend]; exact haM
  have hsb : s.1 < b := by change (s.1 : ℝ) < bv; rw [hbend]; exact hMb
  have hsEval : p.toPath s.1 = B := P.toPath_eq_vertex_at_bend d s hi hbend
  have haEval : p.toPath a = B - r • u := by
    have hf := Polyline.toPath_segment_affine_apply p (i := i) (by omega)
      a hLa.le (by rw [hend]; exact haM.le)
    rw [hend] at hf
    have hratio : ((a : ℝ) - L) / (M - L) = 1 - r := by
      change (M - r * (M - L) - L) / (M - L) = 1 - r
      field_simp
      ring
    change p.toPath a = p.point i + (((((a : ℝ) - L) / (M - L)) : ℝ) : ℂ) * u at hf
    rw [hratio] at hf
    rw [hf]
    dsimp only [u, B]
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hbEval : p.toPath b = B + r • v := by
    have hf := Polyline.toPath_segment_affine_apply p (i := i + 1) (by omega)
      b hMb.le hbH.le
    have hratio : ((b : ℝ) - M) / (H - M) = r := by
      change (M + r * (H - M) - M) / (H - M) = r
      field_simp
      ring
    change p.toPath b = B + (((((b : ℝ) - M) / (H - M)) : ℝ) : ℂ) * v at hf
    rw [hratio] at hf
    exact hf
  have hleft := Polyline.toPath_affine_on_segment_subinterval p (i := i) (by omega)
    a s.1 has hLa.le (by rw [hend]; exact hbend.le)
  have hright := Polyline.toPath_affine_on_segment_subinterval p (i := i + 1) (by omega)
    s.1 b hsb hbend.ge hbH.le
  obtain ⟨f, hc, h0, h1, hedge⟩ := edgeSubarc_two_segments_reparam p.toPath a s.1 b
    has hsb hleft hright
  let q := Path.segment (p.toPath b) (p.toPath a)
  have hqinj : Function.Injective q := by
    dsimp only [q]
    rw [haEval, hbEval]
    exact hinj
  have hqF : ∀ t : I, t ∈ openParams → q t ∈ F.val := by
    dsimp only [q]
    rw [haEval, hbEval]
    exact hqface
  have hwind (w : ℂ) (hw : HasWinding (((Path.segment (B - r • u) B).trans
      (Path.segment B (B + r • v))).trans (Path.segment (B + r • v) (B - r • u))) w 1) :
      HasWinding ((edgeSubarc p.toPath a b (has.trans hsb).le).trans q) w 1 := by
    have hw' : HasWinding (((Path.segment (p.toPath a) (p.toPath s.1)).trans
        (Path.segment (p.toPath s.1) (p.toPath b))).trans q) w 1 := by
      dsimp only [q]
      rw [haEval, hbEval, hsEval]
      exact hw
    have ht := hw'.trans_reparam_left f hc h0 h1
    rw [← hedge] at ht
    exact ht
  refine ⟨a, b, ha, has, hsb, hb, q, hqinj, hqF, ?_⟩
  rw [hsEval]
  have hsubset : {w : ℂ | w ∈ F.val ∧
      HasWinding (((Path.segment (B - r • u) B).trans (Path.segment B (B + r • v))).trans
        (Path.segment (B + r • v) (B - r • u))) w 1} ⊆
      {w : ℂ | w ∈ F.val ∧
        HasWinding ((edgeSubarc p.toPath a b (has.trans hsb).le).trans q) w 1} :=
    fun w hw => ⟨hw.1, hwind w hw.2⟩
  exact closure_mono hsubset hcl

end PLDrawing

/-- Helper toward Definition 3.2: four positive principal-log increments
around four vectors sum to one full turn. -/
theorem quadrilateral_log_ratio_sum {u v r z : ℂ}
    (huv : 0 < (conj u * v).im) (hvr : 0 < (conj v * r).im)
    (hrz : 0 < (conj r * z).im) (hzu : 0 < (conj z * u).im) :
    Complex.log (v / u) + Complex.log (r / v) + Complex.log (z / r) +
      Complex.log (u / z) = 2 * Real.pi * Complex.I := by
  have hu : u ≠ 0 := by intro h; simp [h] at huv
  have hv : v ≠ 0 := by intro h; simp [h] at hvr
  have hr : r ≠ 0 := by intro h; simp [h] at hrz
  have hz : z ≠ 0 := by intro h; simp [h] at hzu
  have h₁ := log_im_mem_Ioo_of_im_pos (im_div_pos_of_conj_mul_im_pos huv)
  have h₂ := log_im_mem_Ioo_of_im_pos (im_div_pos_of_conj_mul_im_pos hvr)
  have h₃ := log_im_mem_Ioo_of_im_pos (im_div_pos_of_conj_mul_im_pos hrz)
  have h₄ := log_im_mem_Ioo_of_im_pos (im_div_pos_of_conj_mul_im_pos hzu)
  have he : Complex.exp (Complex.log (v / u) + Complex.log (r / v) +
      Complex.log (z / r) + Complex.log (u / z)) = 1 := by
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_add,
      Complex.exp_log (div_ne_zero hv hu), Complex.exp_log (div_ne_zero hr hv),
      Complex.exp_log (div_ne_zero hz hr), Complex.exp_log (div_ne_zero hu hz)]
    field_simp
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp he
  have him := congrArg Complex.im hk
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re,
    Complex.I_im, zero_mul, mul_zero, mul_one, add_zero,
    Complex.re_ofNat, Complex.im_ofNat, sub_zero] at him
  have hkpos : (0 : ℝ) < k := by
    nlinarith only [him, h₁.1, h₂.1, h₃.1, h₄.1, Real.pi_pos]
  have hklt : (k : ℝ) < 2 := by
    nlinarith only [him, h₁.2, h₂.2, h₃.2, h₄.2, Real.pi_pos]
  have hkpos' : (0 : ℤ) < k := by exact_mod_cast hkpos
  have hklt' : k < (2 : ℤ) := by exact_mod_cast hklt
  have hkone : k = 1 := by omega
  simpa only [hkone, Int.cast_one, one_mul] using hk

/-- Helper toward Definition 3.2: positive successive cross products at
a point give winding one for a four-segment loop, including a reflex bend. -/
theorem hasWinding_quadrilateral_of_cross_pos {a b c d w : ℂ}
    (hab : 0 < (conj (a - w) * (b - w)).im)
    (hbc : 0 < (conj (b - w) * (c - w)).im)
    (hcd : 0 < (conj (c - w) * (d - w)).im)
    (hda : 0 < (conj (d - w) * (a - w)).im) :
    HasWinding (((Path.segment a b).trans (Path.segment b c)).trans
      ((Path.segment c d).trans (Path.segment d a))) w 1 := by
  have ha : a - w ≠ 0 := by intro h; simp [h] at hab
  let A := Complex.log (a - w)
  let B := A + Complex.log ((b - w) / (a - w))
  let C := B + Complex.log ((c - w) / (b - w))
  let E := C + Complex.log ((d - w) / (c - w))
  obtain ⟨α, hα⟩ := exists_segment_log_lift hab (Complex.exp_log ha)
  have hB : Complex.exp B = b - w := by simpa only [Path.target] using hα 1
  obtain ⟨β, hβ⟩ := exists_segment_log_lift hbc hB
  have hC : Complex.exp C = c - w := by simpa only [Path.target] using hβ 1
  obtain ⟨γ, hγ⟩ := exists_segment_log_lift hcd hC
  have hE : Complex.exp E = d - w := by simpa only [Path.target] using hγ 1
  obtain ⟨δ, hδ⟩ := exists_segment_log_lift hda hE
  let Ψ : C(I, ℂ) := ((α.trans β).trans (γ.trans δ)).toContinuousMap
  refine ⟨Ψ, exp_trans_of_exp_eq (exp_trans_of_exp_eq hα hβ)
    (exp_trans_of_exp_eq hγ hδ), ?_⟩
  change ((α.trans β).trans (γ.trans δ)) 1 - ((α.trans β).trans (γ.trans δ)) 0 = _
  simp only [Path.target, Path.source, Int.cast_one, mul_one]
  calc
    E + Complex.log ((a - w) / (d - w)) - A =
        Complex.log ((b - w) / (a - w)) + Complex.log ((c - w) / (b - w)) +
          Complex.log ((d - w) / (c - w)) + Complex.log ((a - w) / (d - w)) := by
      dsimp [E, C, B, A]
      ring
    _ = 2 * Real.pi * Complex.I := quadrilateral_log_ratio_sum hab hbc hcd hda

/-- Helper toward Definition 3.2: a reflex left-side quadrilateral has
winding one at nearby points on the ray opposite the two incident edges. -/
theorem hasWinding_bend_reflex_quadrilateral {b u v : ℂ} {r τ : ℝ}
    (hturn : (conj u * v).im < 0) (hr : 0 < r) (hτ : 0 < τ) (hτr : τ < r) :
    HasWinding (((Path.segment (b - r • u) b).trans (Path.segment b (b + r • v))).trans
      ((Path.segment (b + r • v) (b + r • (u - v))).trans
        (Path.segment (b + r • (u - v)) (b - r • u))))
      (b + τ • (u - v)) 1 := by
  have hcross :
      (conj ((b - r • u) - (b + τ • (u - v))) *
        (b - (b + τ • (u - v)))).im = -r * τ * (conj u * v).im ∧
      (conj (b - (b + τ • (u - v))) *
        ((b + r • v) - (b + τ • (u - v)))).im = -r * τ * (conj u * v).im ∧
      (conj ((b + r • v) - (b + τ • (u - v))) *
        ((b + r • (u - v)) - (b + τ • (u - v)))).im =
          -r * (r - τ) * (conj u * v).im ∧
      (conj ((b + r • (u - v)) - (b + τ • (u - v))) *
        ((b - r • u) - (b + τ • (u - v)))).im =
          -r * (r - τ) * (conj u * v).im := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul]
    constructor
    · ring
    constructor
    · ring
    constructor <;> ring
  apply hasWinding_quadrilateral_of_cross_pos
  · rw [hcross.1]
    exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (neg_neg_of_pos hr) hτ) hturn
  · rw [hcross.2.1]
    exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (neg_neg_of_pos hr) hτ) hturn
  · rw [hcross.2.2.1]
    exact mul_pos_of_neg_of_neg
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hr) (sub_pos.mpr hτr)) hturn
  · rw [hcross.2.2.2]
    exact mul_pos_of_neg_of_neg
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hr) (sub_pos.mpr hτr)) hturn

namespace PLDrawing

/-- Helper toward Definition 3.2: at a strict reflex left bend, the
union of the two small left half-disks belongs to the bordering face. -/
theorem dartBorders_bend_reflex_wedge_subset_face
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (hturn : (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im < 0) :
    let b := (P.arc d).point (i + 1)
    let u := b - (P.arc d).point i
    let v := (P.arc d).point (i + 2) - b
    ∃ r : ℝ, 0 < r ∧ ∀ y : ℂ, y ∈ Metric.ball b r →
      (0 < (star u * (y - b)).im ∨ 0 < (star v * (y - b)).im) → y ∈ F.val := by
  dsimp only
  let a := (P.arc d).point i
  let b := (P.arc d).point (i + 1)
  let c := (P.arc d).point (i + 2)
  let u := b - a
  let v := c - b
  obtain ⟨r, hr, hlocal⟩ := P.bend_contact_local_image hvert d hi
  let A := {y : ℂ | y ∈ Metric.ball b r ∧ 0 < (star u * (y - b)).im}
  let B := {y : ℂ | y ∈ Metric.ball b r ∧ 0 < (star v * (y - b)).im}
  have hAc : Convex ℝ A := by simpa only [one_mul] using signed_halfDisk_convex b u r 1
  have hBc : Convex ℝ B := by simpa only [one_mul] using signed_halfDisk_convex b v r 1
  have hc : (star u * v).im < 0 := hturn
  have hsafe : A ∪ B ⊆ P.imageᶜ := by
    intro y hy hyP
    have hyr : y ∈ Metric.ball b r := hy.elim And.left And.left
    rcases (hlocal y hyr).mp hyP with hleft | hright
    · have hzu := segment_contact_side_eq_zero a b b y (right_mem_segment ℝ a b) hleft
      have hzv : (star v * (y - b)).im ≤ 0 := by
        change y ∈ segment ℝ a b at hleft
        rw [segment_eq_image'] at hleft
        obtain ⟨t, ht, rfl⟩ := hleft
        have heq : a + t • (b - a) - b = (1 - t) • (-u) := by
          change a + t • (b - a) - b = (1 - t) • (-(b - a))
          module
        rw [heq]
        have h := (bend_offset_sides u v 1 (1 - t) 0).2.2.1
        simp only [one_smul, one_mul, one_pow, mul_one, zero_smul, add_zero, zero_mul] at h
        rw [h]
        exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2) hc.le
      exact hy.elim (fun hy => (ne_of_gt hy.2) hzu) (fun hy => (not_lt_of_ge hzv) hy.2)
    · have hzv := segment_contact_side_eq_zero b c b y (left_mem_segment ℝ b c) hright
      have hzu : (star u * (y - b)).im ≤ 0 := by
        change y ∈ segment ℝ b c at hright
        rw [segment_eq_image'] at hright
        obtain ⟨t, ht, rfl⟩ := hright
        have h := (bend_offset_sides u v 1 t 0).2.2.2
        simp only [one_smul, one_mul, one_pow, mul_one, zero_smul, add_zero, zero_mul] at h
        rw [add_sub_cancel_left, h]
        exact mul_nonpos_of_nonneg_of_nonpos ht.1 hc.le
      exact hy.elim (fun hy => (not_lt_of_ge hzu) hy.2) (fun hy => (ne_of_gt hy.2) hzv)
  let τ := r / (2 * (‖u - v‖ + 1))
  have hτ : 0 < τ := div_pos hr (by positivity)
  let z := b + τ • (u - v)
  have hzr : z ∈ Metric.ball b r := by
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖b + τ • (u - v) - b‖ < r
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
    have hp : τ * (2 * (‖u - v‖ + 1)) = r := div_mul_cancel₀ r (by positivity)
    nlinarith only [hp, hτ, norm_nonneg (u - v)]
  have hzu : (star u * (z - b)).im = -τ * (star u * v).im := by
    dsimp only [z]
    simp only [add_sub_cancel_left, Complex.star_def, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring
  have hzv : (star v * (z - b)).im = -τ * (star u * v).im := by
    dsimp only [z]
    simp only [add_sub_cancel_left, Complex.star_def, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring
  have hp : 0 < -τ * (star u * v).im := mul_pos_of_neg_of_neg (neg_neg_of_pos hτ) hc
  have hzA : z ∈ A := ⟨hzr, hzu.symm ▸ hp⟩
  have hzB : z ∈ B := ⟨hzr, hzv.symm ▸ hp⟩
  have hpre : IsPreconnected (A ∪ B) := hAc.isPreconnected.union z hzA hzB hBc.isPreconnected
  obtain ⟨δ, hδ, hface⟩ := P.dartBorders_bend_left_offsets_mem_face hvert d F hborder hi
  let ε := δ / 2
  have hε : 0 < ε := half_pos hδ
  have hεδ : ε < δ := half_lt_self hδ
  let f : ℝ → ℂ := fun t => b + t • (-u + ε • (Complex.I * u))
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hfn : f ⁻¹' Metric.ball b r ∈ 𝓝 0 :=
    hf.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds
      (by simpa only [f, zero_smul, add_zero] using Metric.mem_ball_self hr))
  obtain ⟨e, he, hball⟩ := Metric.mem_nhds_iff.mp hfn
  let t := min (δ / 2) (e / 2)
  have ht : 0 < t := lt_min (half_pos hδ) (half_pos he)
  have htδ : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hte : t < e := (min_le_right _ _).trans_lt (half_lt_self he)
  have hfr : f t ∈ Metric.ball b r := by
    apply hball
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using hte
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i (by omega)).symm
  have hfu : 0 < (star u * (f t - b)).im := by
    have h := (bend_offset_sides u v 1 t ε).1
    simp only [one_smul, one_mul, one_pow, mul_one] at h
    dsimp only [f]
    rw [add_sub_cancel_left, h]
    exact mul_pos (mul_pos ht hε) (Complex.normSq_pos.mpr hu)
  have hfF : f t ∈ F.val := (hface t ε ht htδ hε hεδ).1
  have hWF : A ∪ B ⊆ F.val := by
    obtain ⟨z, _, hF⟩ := F.property
    rw [hF] at hfF ⊢
    rw [connectedComponentIn_eq hfF]
    exact hpre.subset_connectedComponentIn (Or.inl ⟨hfr, hfu⟩) hsafe
  refine ⟨r, hr, ?_⟩
  intro y hyr hy
  exact hWF (hy.elim (fun hu => Or.inl ⟨hyr, hu⟩) (fun hv => Or.inr ⟨hyr, hv⟩))

/-- Helper toward Definition 3.2: a reflex bend admits a small injective
two-segment return path in the bordering face and winding-one accumulation. -/
theorem dartBorders_bend_exists_reflex_return
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (hturn : (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im < 0) :
    let b := (P.arc d).point (i + 1)
    let u := b - (P.arc d).point i
    let v := (P.arc d).point (i + 2) - b
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      let q := (Path.segment (b + r • v) (b + r • (u - v))).trans
        (Path.segment (b + r • (u - v)) (b - r • u))
      Function.Injective q ∧ (∀ t : I, t ∈ openParams → q t ∈ F.val) ∧
      b ∈ closure {w : ℂ | w ∈ F.val ∧
        HasWinding (((Path.segment (b - r • u) b).trans
          (Path.segment b (b + r • v))).trans q) w 1} := by
  dsimp only
  let b := (P.arc d).point (i + 1)
  let u := b - (P.arc d).point i
  let v := (P.arc d).point (i + 2) - b
  obtain ⟨R, hR, hface⟩ :=
    P.dartBorders_bend_reflex_wedge_subset_face hvert d F hborder hi hturn
  let r := min (1 / 2 : ℝ) (R / (2 * (‖u‖ + ‖v‖ + 1)))
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hprod : r * (2 * (‖u‖ + ‖v‖ + 1)) ≤ R :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have haR : b - r • u ∈ Metric.ball b R := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg,
      norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith only [hprod, hr, norm_nonneg u, norm_nonneg v]
  have hcR : b + r • v ∈ Metric.ball b R := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith only [hprod, hr, norm_nonneg u, norm_nonneg v]
  have hpR : b + r • (u - v) ∈ Metric.ball b R := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hn := mul_le_mul_of_nonneg_left (norm_sub_le u v) hr.le
    nlinarith only [hprod, hr, norm_nonneg u, norm_nonneg v, hn]
  let α := Path.segment (b + r • v) (b + r • (u - v))
  let β := Path.segment (b + r • (u - v)) (b - r • u)
  let q := α.trans β
  have hc : (star u * v).im < 0 := hturn
  have hα (t : I) : (star v * (α t - b)).im = -r * (t : ℝ) * (star u * v).im := by
    dsimp only [α]
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module,
      Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring
  have hβ (t : I) : (star u * (β t - b)).im = -r * (1 - (t : ℝ)) * (star u * v).im := by
    dsimp only [β]
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module,
      Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring
  have hqcross (t : I) : (star (u - v) * (q t - b)).im =
      r * (1 - 2 * (t : ℝ)) * (star u * v).im := by
    dsimp only [q]
    rw [Path.trans_apply]
    split_ifs <;>
      simp only [α, β, Path.segment_apply, AffineMap.lineMap_apply_module,
        Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.smul_re, Complex.smul_im, smul_eq_mul] <;> ring
  have hqinj : Function.Injective q := by
    intro s t heq
    have he := congrArg (fun z : ℂ => (star (u - v) * (z - b)).im) heq
    rw [hqcross, hqcross] at he
    have he' : (r * (star u * v).im) * (s : ℝ) =
        (r * (star u * v).im) * (t : ℝ) := by nlinarith only [he]
    exact Subtype.ext (mul_left_cancel₀ (mul_ne_zero hr.ne' hc.ne) he')
  have hαR (t : I) : α t ∈ Metric.ball b R :=
    (convex_ball b R).segment_subset hcR hpR (by
      rw [Path.segment_apply]; exact lineMap_mem_segment ℝ _ _ t.2)
  have hβR (t : I) : β t ∈ Metric.ball b R :=
    (convex_ball b R).segment_subset hpR haR (by
      rw [Path.segment_apply]; exact lineMap_mem_segment ℝ _ _ t.2)
  have hqF : ∀ t : I, t ∈ openParams → q t ∈ F.val := by
    intro t ht
    dsimp only [q]
    rw [Path.trans_apply]
    split_ifs with htHalf
    · apply hface _ (hαR _)
      right
      rw [hα]
      exact mul_pos_of_neg_of_neg
        (mul_neg_of_neg_of_pos (neg_neg_of_pos hr) (by change 0 < 2 * (t : ℝ); linarith only [ht.1])) hc
    · apply hface _ (hβR _)
      left
      rw [hβ]
      exact mul_pos_of_neg_of_neg
        (mul_neg_of_neg_of_pos (neg_neg_of_pos hr)
          (by change 0 < 1 - (2 * (t : ℝ) - 1); linarith only [ht.2])) hc
  refine ⟨r, hr, hr1, hqinj, hqF, ?_⟩
  rw [Metric.mem_closure_iff]
  intro η hη
  let τ := min (r / 2) (min (R / (2 * (‖u - v‖ + 1))) (η / (2 * (‖u - v‖ + 1))))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτr : τ < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hτR : τ * (2 * (‖u - v‖ + 1)) ≤ R := by
    apply (le_div_iff₀ (by positivity)).mp
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hτη : τ * (2 * (‖u - v‖ + 1)) ≤ η := by
    apply (le_div_iff₀ (by positivity)).mp
    exact (min_le_right _ _).trans (min_le_right _ _)
  let w := b + τ • (u - v)
  have hdist : dist w b = τ * ‖u - v‖ := by
    dsimp only [w]
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
  have hwR : w ∈ Metric.ball b R := by
    rw [Metric.mem_ball, hdist]
    nlinarith only [hτR, hτ, norm_nonneg (u - v)]
  have hwu : (star u * (w - b)).im = -τ * (star u * v).im := by
    dsimp only [w]
    simp only [add_sub_cancel_left, Complex.star_def, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring
  have hwF : w ∈ F.val := hface w hwR (Or.inl
    (hwu.symm ▸ mul_pos_of_neg_of_neg (neg_neg_of_pos hτ) hc))
  have hwinding := hasWinding_bend_reflex_quadrilateral (b := b) hturn hr hτ hτr
  refine ⟨w, ⟨hwF, hwinding⟩, ?_⟩
  rw [dist_comm, hdist]
  nlinarith only [hτη, hτ, norm_nonneg (u - v)]

/-- Helper toward Definition 3.2: a bordering face satisfies the winding
left-side test at a bend with strictly negative turn cross product. -/
theorem dartBorders_toPath_leftAtOn_of_bend_right_turn
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (s : {t : I // t ∈ openParams}) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (hbend : (s.1 : ℝ) = Polyline.segmentParameterStart (i + 1))
    (hturn : (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im < 0) :
    LeftAtOn F.val (P.arc d).toPath s := by
  let p := P.arc d
  change i + 2 < p.points.length at hi
  let B := p.point (i + 1)
  let u := B - p.point i
  let v := p.point (i + 2) - B
  obtain ⟨r, hr, hr1, hinj, hqface, hcl⟩ :=
    P.dartBorders_bend_exists_reflex_return hvert d F hborder hi hturn
  let L := Polyline.segmentParameterStart i
  let M := Polyline.segmentParameterStart (i + 1)
  let H := Polyline.segmentParameterEnd p.points.length (i + 1)
  have hend : Polyline.segmentParameterEnd p.points.length i = M :=
    Polyline.segmentParameterEnd_eq_start_succ (by omega)
  have hLM : L < M := by
    rw [← hend]
    exact Polyline.segmentParameterStart_lt_end p.points.length i
  have hMH : M < H := Polyline.segmentParameterStart_lt_end p.points.length (i + 1)
  have hL0 : 0 ≤ L := (Polyline.segmentParameterStart_mem_Icc i).1
  have hH1 : H ≤ 1 := (Polyline.segmentParameterEnd_mem_Icc p.points.length (i + 1)).2
  let av := M - r * (M - L)
  let bv := M + r * (H - M)
  have hLa : L < av := by
    dsimp only [av]
    nlinarith only [mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hLM)]
  have haM : av < M := by
    dsimp only [av]
    linarith only [mul_pos hr (sub_pos.mpr hLM)]
  have hMb : M < bv := by
    dsimp only [bv]
    linarith only [mul_pos hr (sub_pos.mpr hMH)]
  have hbH : bv < H := by
    dsimp only [bv]
    nlinarith only [mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hMH)]
  let a : I := ⟨av, ⟨hL0.trans hLa.le, haM.le.trans (hMH.le.trans hH1)⟩⟩
  let b : I := ⟨bv, ⟨(hL0.trans hLM.le).trans hMb.le, hbH.le.trans hH1⟩⟩
  have ha : (0 : I) < a := hL0.trans_lt hLa
  have hb : b < (1 : I) := hbH.trans_le hH1
  have has : a < s.1 := by change av < (s.1 : ℝ); rw [hbend]; exact haM
  have hsb : s.1 < b := by change (s.1 : ℝ) < bv; rw [hbend]; exact hMb
  have hsEval : p.toPath s.1 = B := P.toPath_eq_vertex_at_bend d s hi hbend
  have haEval : p.toPath a = B - r • u := by
    have hf := Polyline.toPath_segment_affine_apply p (i := i) (by omega)
      a hLa.le (by rw [hend]; exact haM.le)
    rw [hend] at hf
    have hratio : ((a : ℝ) - L) / (M - L) = 1 - r := by
      change (M - r * (M - L) - L) / (M - L) = 1 - r
      field_simp
      ring
    change p.toPath a = p.point i + (((((a : ℝ) - L) / (M - L)) : ℝ) : ℂ) * u at hf
    rw [hratio] at hf
    rw [hf]
    dsimp only [u, B]
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hbEval : p.toPath b = B + r • v := by
    have hf := Polyline.toPath_segment_affine_apply p (i := i + 1) (by omega)
      b hMb.le hbH.le
    have hratio : ((b : ℝ) - M) / (H - M) = r := by
      change (M + r * (H - M) - M) / (H - M) = r
      field_simp
      ring
    change p.toPath b = B + (((((b : ℝ) - M) / (H - M)) : ℝ) : ℂ) * v at hf
    rw [hratio] at hf
    exact hf
  have hleft := Polyline.toPath_affine_on_segment_subinterval p (i := i) (by omega)
    a s.1 has hLa.le (by rw [hend]; exact hbend.le)
  have hright := Polyline.toPath_affine_on_segment_subinterval p (i := i + 1) (by omega)
    s.1 b hsb hbend.ge hbH.le
  obtain ⟨f, hc, h0, h1, hedge⟩ := edgeSubarc_two_segments_reparam p.toPath a s.1 b
    has hsb hleft hright
  let q := (Path.segment (p.toPath b) (B + r • (u - v))).trans
    (Path.segment (B + r • (u - v)) (p.toPath a))
  have hqinj : Function.Injective q := by
    dsimp only [q]
    rw [haEval, hbEval]
    exact hinj
  have hqF : ∀ t : I, t ∈ openParams → q t ∈ F.val := by
    dsimp only [q]
    rw [haEval, hbEval]
    exact hqface
  have hwind (w : ℂ) (hw : HasWinding (((Path.segment (B - r • u) B).trans
      (Path.segment B (B + r • v))).trans (((Path.segment (B + r • v) (B + r • (u - v))).trans
        (Path.segment (B + r • (u - v)) (B - r • u))))) w 1) :
      HasWinding ((edgeSubarc p.toPath a b (has.trans hsb).le).trans q) w 1 := by
    have hw' : HasWinding (((Path.segment (p.toPath a) (p.toPath s.1)).trans
        (Path.segment (p.toPath s.1) (p.toPath b))).trans q) w 1 := by
      dsimp only [q]
      rw [haEval, hbEval, hsEval]
      exact hw
    have ht := hw'.trans_reparam_left f hc h0 h1
    rw [← hedge] at ht
    exact ht
  refine ⟨a, b, ha, has, hsb, hb, q, hqinj, hqF, ?_⟩
  rw [hsEval]
  have hsubset : {w : ℂ | w ∈ F.val ∧
      HasWinding (((Path.segment (B - r • u) B).trans (Path.segment B (B + r • v))).trans
        (((Path.segment (B + r • v) (B + r • (u - v))).trans
        (Path.segment (B + r • (u - v)) (B - r • u))))) w 1} ⊆
      {w : ℂ | w ∈ F.val ∧
        HasWinding ((edgeSubarc p.toPath a b (has.trans hsb).le).trans q) w 1} :=
    fun w hw => ⟨hw.1, hwind w hw.2⟩
  exact closure_mono hsubset hcl


/-- Helper toward Definition 3.2: the two strict-turn constructions give
the left-side test whenever the bend cross product is nonzero. -/
theorem dartBorders_toPath_leftAtOn_of_bend_turn_ne_zero
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (s : {t : I // t ∈ openParams}) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (hbend : (s.1 : ℝ) = Polyline.segmentParameterStart (i + 1))
    (hturn : (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im ≠ 0) :
    LeftAtOn F.val (P.arc d).toPath s := by
  rcases lt_or_gt_of_ne hturn with hneg | hpos
  · exact P.dartBorders_toPath_leftAtOn_of_bend_right_turn hvert d F hborder s hi hbend hneg
  · exact P.dartBorders_toPath_leftAtOn_of_bend_left_turn hvert d F hborder s hi hbend hpos































end PLDrawing

end DirectedDistances.PlanarMap

end

