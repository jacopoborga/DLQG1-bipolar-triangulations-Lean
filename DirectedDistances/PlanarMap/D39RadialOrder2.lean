/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39RadialOrder

/-! # Complementary turns and radial germs -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open scoped ComplexConjugate

/-- Helper toward Proposition 5.16: distinct arguments give a turn strictly
smaller than a full revolution. -/
theorem d39_ccwTurn_lt_two_pi {u v : ℂ} (huv : u.arg ≠ v.arg) :
    ccwTurn u v < 2 * Real.pi := by
  exact lt_of_le_of_ne (ccwTurn_le_two_pi u v)
    (fun h => huv ((ccwTurn_eq_two_pi_iff u v).mp h))

/-- Helper toward Proposition 5.16: strict cyclic betweenness is unchanged
by cyclically rotating three distinct rays. -/
theorem d39_between_cyclic {u v w : ℂ}
    (huv : u.arg ≠ v.arg) (hvw : v.arg ≠ w.arg) (hwu : w.arg ≠ u.arg) :
    ccwTurn u w < ccwTurn u v ↔ ccwTurn v u < ccwTurn v w := by
  have huv' := ccwTurn_add_reverse u v huv
  have hvw' := ccwTurn_add_reverse v w hvw
  have hwu' := ccwTurn_add_reverse w u hwu
  constructor
  · intro h
    have hcomp := ccwTurn_comp_add h
    have hpos := ccwTurn_pos u w
    linarith
  · intro h
    have hcomp := ccwTurn_comp_add h
    have hbound := d39_ccwTurn_lt_two_pi hvw
    linarith

/-- Helper toward Proposition 5.16: exchanging the endpoints complements
strict betweenness, including reflex and antipodal endpoint turns. -/
theorem d39_between_iff_not_reverse {u v w : ℂ}
    (huv : u.arg ≠ v.arg) (hvw : v.arg ≠ w.arg) (hwu : w.arg ≠ u.arg) :
    ccwTurn u w < ccwTurn u v ↔ ¬ ccwTurn v w < ccwTurn v u := by
  rw [d39_between_cyclic huv hvw hwu]
  have hne : ccwTurn v u ≠ ccwTurn v w := by
    intro h
    exact hwu (ccwTurn_left_injective h).symm
  exact ⟨fun h => not_lt_of_ge h.le, fun h => lt_of_le_of_ne (le_of_not_gt h) hne⟩

/-- Helper toward Proposition 5.16: a reflex endpoint turn has a strictly
convex complementary turn; the antipodal endpoint case remains a half-turn. -/
theorem d39_complementary_turn_le_pi {u v : ℂ}
    (huv : u.arg ≠ v.arg) (hpi : Real.pi ≤ ccwTurn u v) :
    0 < ccwTurn v u ∧ ccwTurn v u ≤ Real.pi ∧
      (Real.pi < ccwTurn u v → ccwTurn v u < Real.pi) := by
  have hsum := ccwTurn_add_reverse u v huv
  exact ⟨ccwTurn_pos v u, by linarith, fun h => by linarith⟩

/-- Helper toward Proposition 5.16: a lifted displacement smaller than one
revolution is exactly the counterclockwise turn to its polar direction. -/
theorem d39_ccwTurn_polar (u : ℂ) (θ : ℝ) (hθ : 0 < θ)
    (hθmax : θ < 2 * Real.pi) :
    ccwTurn u (Complex.exp (((u.arg + θ : ℝ) : ℂ) * Complex.I)) = θ := by
  have hu := Complex.arg_mem_Ioc u
  by_cases hcut : u.arg + θ ≤ Real.pi
  · have ha : (Complex.exp (((u.arg + θ : ℝ) : ℂ) * Complex.I)).arg =
        u.arg + θ := by
      rw [Complex.arg_exp_mul_I, (toIocMod_eq_self Real.two_pi_pos).2]
      constructor <;> linarith [hu.1]
    rw [ccwTurn, ha, ite_eq_left (by linarith)]
    ring
  · have he : Complex.exp (((u.arg + θ : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((u.arg + θ - 2 * Real.pi : ℝ) : ℂ) * Complex.I) := by
      have hp := Complex.exp_periodic
        (((u.arg + θ - 2 * Real.pi : ℝ) : ℂ) * Complex.I)
      convert hp using 1
      congr 1
      push_cast
      ring
    have ha : (Complex.exp (((u.arg + θ : ℝ) : ℂ) * Complex.I)).arg =
        u.arg + θ - 2 * Real.pi := by
      rw [he, Complex.arg_exp_mul_I, (toIocMod_eq_self Real.two_pi_pos).2]
      constructor <;> linarith [hu.2]
    rw [ccwTurn, ha, ite_eq_right (by linarith)]
    ring

/-- Helper toward Proposition 5.16: every non-full turn, including an
antipodal or reflex turn, splits into two strictly convex turns. -/
theorem d39_exists_convex_turn_split (u v : ℂ) (huv : u.arg ≠ v.arg) :
    ∃ m : ℂ, m ≠ 0 ∧
      0 < ccwTurn u m ∧ ccwTurn u m < Real.pi ∧
      0 < ccwTurn m v ∧ ccwTurn m v < Real.pi ∧
      ccwTurn u m + ccwTurn m v = ccwTurn u v := by
  let m := Complex.exp (((u.arg + ccwTurn u v / 2 : ℝ) : ℂ) * Complex.I)
  have hp := ccwTurn_pos u v
  have hb := d39_ccwTurn_lt_two_pi huv
  have hm : ccwTurn u m = ccwTurn u v / 2 :=
    d39_ccwTurn_polar u _ (by linarith) (by linarith)
  have hlt : ccwTurn u m < ccwTurn u v := by rw [hm]; linarith
  have hadd := ccwTurn_comp_add hlt
  exact ⟨m, Complex.exp_ne_zero _, by rw [hm]; linarith,
    by rw [hm]; linarith, ccwTurn_pos m v, by linarith, hadd⟩

/-- Helper toward Proposition 5.16: a point in a strictly convex closed
wedge, away from its boundary rays, satisfies both strict side tests. -/
theorem d39_closedWedge_strict_of_not_boundary {u v z : ℂ}
    (harea : 0 < (conj u * v).im) (hz : z ∈ d39ClosedWedge u v)
    (hzu : z ∉ d39ClosedWedge u u) (hzv : z ∉ d39ClosedWedge v v) :
    0 < (conj u * z).im ∧ 0 < (conj z * v).im := by
  obtain ⟨s, t, hs, ht, heq⟩ := hz
  have hspos : 0 < s := by
    apply lt_of_le_of_ne hs
    intro h
    apply hzv
    exact ⟨t, 0, ht, le_rfl, by simpa [← h] using heq⟩
  have htpos : 0 < t := by
    apply lt_of_le_of_ne ht
    intro h
    apply hzu
    exact ⟨s, 0, hs, le_rfl, by simpa [← h] using heq⟩
  rw [heq]
  constructor
  · rw [d39_leftSide_origin_barycentric]
    exact mul_pos htpos harea
  · have he : (conj ((s : ℂ) * u + (t : ℂ) * v) * v).im =
        s * (conj u * v).im := by
      simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
        Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [he]
    exact mul_pos hspos harea

/-- Helper toward Proposition 5.16: positivity of the oriented determinant
forces the counterclockwise turn to be strictly convex. -/
theorem d39_ccwTurn_lt_pi_of_det_pos {u v : ℂ}
    (hdet : 0 < (conj u * v).im) : ccwTurn u v < Real.pi := by
  by_contra h
  have ht := ccwTurn_le_two_pi u v
  have hs : Real.sin (ccwTurn u v) ≤ 0 := by
    have he : Real.sin (ccwTurn u v - 2 * Real.pi) = Real.sin (ccwTurn u v) := by
      rw [Real.sin_sub_two_pi]
    rw [← he]
    exact Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
  rw [d39_det_eq_norm_mul_sin_ccwTurn] at hdet
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (norm_nonneg u) (norm_nonneg v)) hs)) hdet

/-- Helper toward Proposition 5.16: strict side tests in a convex wedge
are exactly strict cyclic betweenness, with no restriction on the third turn. -/
theorem d39_strict_sides_iff_between {u v w : ℂ}
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hpi : ccwTurn u v < Real.pi) :
    (0 < (conj u * w).im ∧ 0 < (conj w * v).im) ↔
      ccwTurn u w < ccwTurn u v := by
  constructor
  · rintro ⟨huw, hwv⟩
    have huwPi := d39_ccwTurn_lt_pi_of_det_pos huw
    by_contra h
    rcases lt_or_eq_of_le (le_of_not_gt h) with hlt | heq
    · have hcomp := ccwTurn_comp_add hlt
      have hvw := d39_det_pos_of_ccwTurn_lt_pi v w hv hw
        (ccwTurn_pos v w) (by linarith [ccwTurn_pos u v])
      have hswap : (conj w * v).im = -(conj v * w).im := by
        simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
        ring
      rw [hswap] at hwv
      linarith
    · have ha := ccwTurn_left_injective heq
      have he := (Complex.arg_eq_arg_iff hv hw).mp ha
      rw [← Complex.ofReal_div] at he
      have hzero : (conj w * v).im = 0 := by
        rw [← he]
        simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
          Complex.ofReal_re, Complex.ofReal_im]
        ring
      linarith
  · intro h
    have hcomp := ccwTurn_comp_add h
    exact ⟨d39_det_pos_of_ccwTurn_lt_pi u w hu hw (ccwTurn_pos u w) (h.trans hpi),
      d39_det_pos_of_ccwTurn_lt_pi w v hw hv (ccwTurn_pos w v)
        (by linarith [ccwTurn_pos u w])⟩

/-- Helper toward Proposition 5.16: the usual three-segment triangle loop
has winding zero or one near zero away from its two radial boundary rays. -/
theorem d39_triangleLoop_winding_zero_or_one_near_zero
    (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) (hpi : ccwTurn u v < Real.pi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, ‖z‖ < δ →
      z ∉ d39ClosedWedge u u → z ∉ d39ClosedWedge v v →
      (HasWinding ((Path.segment (0 : ℂ) u).trans
        ((Path.segment u v).trans (Path.segment v 0))) z 0 ∨
       HasWinding ((Path.segment (0 : ℂ) u).trans
        ((Path.segment u v).trans (Path.segment v 0))) z 1) := by
  have harea := d39_det_pos_of_ccwTurn_lt_pi u v hu hv (ccwTurn_pos u v) hpi
  have hC0 : (0 : ℂ) ∉ Set.range (Path.segment u v) := by
    rw [Path.range_segment]
    intro hz
    have he := d39_leftSide_eq_zero_of_mem_segment hz
    have he' : (conj (v - u) * (0 - u)).im = (conj u * v).im := by
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.sub_re, Complex.sub_im, Complex.zero_re, Complex.zero_im]
      ring
    rw [he'] at he
    exact harea.ne' he
  obtain ⟨δ, hδ, m, hlocal⟩ := d39_radialLoop_splitting 1 u v zero_lt_one hu hv
    (ccwTurn_pos u v) hpi ((Path.segment u v).cast (by simp) (by simp))
      (by simpa using hC0)
  let L := (Path.segment (0 : ℂ) u).trans
    ((Path.segment u v).trans (Path.segment v 0))
  have hlocal' : ∀ z : ℂ, ‖z‖ < δ →
      ((0 < (conj u * z).im ∧ 0 < (conj z * v).im) → HasWinding L z (m + 1)) ∧
      (z ∉ d39ClosedWedge u v → HasWinding L z m) := by
    simpa only [L, HasWinding, Path.trans_apply, Path.segment_apply, Path.cast_coe,
      Complex.ofReal_one, one_mul] using hlocal
  have hsub : Set.range L ⊆ d39ClosedWedge u v := by
    dsimp only [L]
    rw [Path.trans_range, Path.trans_range, Path.range_segment, Path.range_segment,
      Path.range_segment]
    have h0 := d39_zero_mem_closedWedge u v
    have hum : u ∈ d39ClosedWedge u v := ⟨1, 0, by norm_num, le_rfl, by simp⟩
    have hvm : v ∈ d39ClosedWedge u v := ⟨0, 1, le_rfl, by norm_num, by simp⟩
    exact Set.union_subset ((d39ClosedWedge_convex u v).segment_subset h0 hum)
      (Set.union_subset ((d39ClosedWedge_convex u v).segment_subset hum hvm)
        ((d39ClosedWedge_convex u v).segment_subset hvm h0))
  let t := δ / (2 * ‖u‖)
  have ht : 0 < t := div_pos hδ (mul_pos (by norm_num) (norm_pos_iff.mpr hu))
  have hnorm : ‖-(t : ℂ) * u‖ < δ := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    dsimp only [t]
    have he : δ / (2 * ‖u‖) * ‖u‖ = δ / 2 := by
      field_simp
    rw [he]
    linarith
  have hout := d39_negative_ray_not_mem_closedWedge t u v hu ht
    (by rw [d39_arg_div_eq_ccwTurn u v hu hv (ccwTurn_pos u v) hpi]; exact ccwTurn_pos u v)
    (by rw [d39_arg_div_eq_ccwTurn u v hu hv (ccwTurn_pos u v) hpi]; exact hpi)
  have hz0 := d39_hasWinding_zero_of_convex L _ (d39ClosedWedge_convex u v) hsub hout
  have hm : m = 0 := hasWinding_unique ((hlocal' _ hnorm).2 hout) hz0
  refine ⟨δ, hδ, ?_⟩
  intro z hz hzu hzv
  by_cases hzw : z ∈ d39ClosedWedge u v
  · have hs := d39_closedWedge_strict_of_not_boundary harea hzw hzu hzv
    right
    simpa only [hm, zero_add] using (hlocal' z hz).1 hs
  · left
    simpa only [hm] using (hlocal' z hz).2 hzw

/-- Helper toward Proposition 5.16: sufficiently small points on the target
boundary ray have preimages on the source boundary ray. -/
theorem d39_radial_germ_preimage_selfWedge
    (K : ℂ ≃ₜ ℂ) (u u' : ℂ) (hu' : u' ≠ 0)
    (hsegments : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * u} =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * u'}) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ, ‖z‖ < ε →
      z ∈ d39ClosedWedge u' u' → K.symm z ∈ d39ClosedWedge u u := by
  obtain ⟨r, s, hr, hs, heq⟩ := hsegments
  refine ⟨s * ‖u'‖, mul_pos hs (norm_pos_iff.mpr hu'), ?_⟩
  intro z hz hzu
  obtain ⟨a, b, ha, hb, hab⟩ := hzu
  have hzform : z = ((a + b : ℝ) : ℂ) * u' := by
    rw [hab]
    push_cast
    ring
  have hbound : a + b ≤ s := by
    rw [hzform, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg ha hb)] at hz
    exact (lt_of_mul_lt_mul_right hz (norm_nonneg u')).le
  have hmem : z ∈ K '' {z : ℂ | ∃ t : ℝ,
      0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * u} := by
    rw [heq]
    exact ⟨a + b, add_nonneg ha hb, hbound, hzform⟩
  obtain ⟨p, ⟨t, ht, _, hpt⟩, hpz⟩ := hmem
  have hpre : K.symm z = p := by rw [← hpz, K.symm_apply_apply]
  exact ⟨t, 0, ht, le_rfl, by simpa [hpre] using hpt⟩

/-- Helper toward Proposition 5.16: sufficiently small source boundary
points are sent to the corresponding target boundary ray. -/
theorem d39_radial_germ_image_selfWedge
    (K : ℂ ≃ₜ ℂ) (u u' : ℂ) (hu : u ≠ 0)
    (hsegments : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * u} =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * u'}) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ, ‖z‖ < ε →
      z ∈ d39ClosedWedge u u → K z ∈ d39ClosedWedge u' u' := by
  obtain ⟨r, s, hr, hs, heq⟩ := hsegments
  refine ⟨r * ‖u‖, mul_pos hr (norm_pos_iff.mpr hu), ?_⟩
  intro z hz hzu
  obtain ⟨a, b, ha, hb, hab⟩ := hzu
  have hzform : z = ((a + b : ℝ) : ℂ) * u := by
    rw [hab]
    push_cast
    ring
  have hbound : a + b ≤ r := by
    rw [hzform, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg ha hb)] at hz
    exact (lt_of_mul_lt_mul_right hz (norm_nonneg u)).le
  have hmem : K z ∈ K '' {z : ℂ | ∃ t : ℝ,
      0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * u} :=
    ⟨z, ⟨a + b, add_nonneg ha hb, hbound, hzform⟩, rfl⟩
  rw [heq] at hmem
  obtain ⟨t, ht, _, hKt⟩ := hmem
  exact ⟨t, 0, ht, le_rfl, by simpa using hKt⟩

/-- Helper toward Proposition 5.16: the radial segment hypotheses are
symmetric under passing to the inverse homeomorphism. -/
theorem d39_radial_germ_symm (K : ℂ ≃ₜ ℂ) (u u' : ℂ)
    (hsegments : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * u} =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * u'}) :
    ∃ s r : ℝ, 0 < s ∧ 0 < r ∧
      K.symm '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * u'} =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * u} := by
  obtain ⟨r, s, hr, hs, heq⟩ := hsegments
  refine ⟨s, r, hs, hr, ?_⟩
  rw [← heq, Set.image_image]
  simp only [Homeomorph.symm_apply_apply, Set.image_id']

/-- Helper toward Proposition 5.16: points of a nonzero boundary ray,
other than zero, have exactly the argument of its direction. -/
theorem d39_arg_eq_of_mem_selfWedge {u z : ℂ} (hz : z ≠ 0)
    (hzu : z ∈ d39ClosedWedge u u) : z.arg = u.arg := by
  obtain ⟨a, b, ha, hb, heq⟩ := hzu
  have he : z = ((a + b : ℝ) : ℂ) * u := by
    rw [heq]
    push_cast
    ring
  have hpos : 0 < a + b := by
    apply lt_of_le_of_ne (add_nonneg ha hb)
    intro h
    exact hz (by simpa [← h] using he)
  rw [he, Complex.arg_real_mul u hpos]

/-- Helper toward Proposition 5.16: equal source arguments force equal
target arguments under the radial germ hypotheses. -/
theorem d39_radial_germ_arg_eq (K : ℂ ≃ₜ ℂ) (hK0 : K 0 = 0)
    (u v u' v' : ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : u.arg = v.arg)
    (hsegmentsU : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * u} =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * u'})
    (hsegmentsV : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * v} =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * v'}) :
    u'.arg = v'.arg := by
  obtain ⟨ε, hε, hU⟩ := d39_radial_germ_image_selfWedge K u u' hu hsegmentsU
  obtain ⟨η, hη, hV⟩ := d39_radial_germ_image_selfWedge K v v' hv hsegmentsV
  let t := min ε η / (2 * ‖u‖)
  have ht : 0 < t := div_pos (lt_min hε hη)
    (mul_pos (by norm_num) (norm_pos_iff.mpr hu))
  have hnorm : ‖(t : ℂ) * u‖ < min ε η := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    dsimp only [t]
    have he : min ε η / (2 * ‖u‖) * ‖u‖ = min ε η / 2 := by field_simp
    rw [he]
    linarith [lt_min hε hη]
  have hpointU : (t : ℂ) * u ∈ d39ClosedWedge u u :=
    ⟨t, 0, ht.le, le_rfl, by simp⟩
  have he := (Complex.arg_eq_arg_iff hv hu).mp huv.symm
  rw [← Complex.ofReal_div] at he
  have hpointV : (t : ℂ) * u ∈ d39ClosedWedge v v := by
    refine ⟨t * (‖u‖ / ‖v‖), 0,
      (mul_pos ht (div_pos (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv))).le,
      le_rfl, ?_⟩
    calc
      (t : ℂ) * u = (t : ℂ) * (((‖u‖ / ‖v‖ : ℝ) : ℂ) * v) :=
        congrArg (fun z : ℂ => (t : ℂ) * z) he.symm
      _ = _ := by push_cast; ring
  have hnonzero : K ((t : ℂ) * u) ≠ 0 := by
    intro h
    have heq := K.injective (h.trans hK0.symm)
    exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne') hu) heq
  exact (d39_arg_eq_of_mem_selfWedge hnonzero
    (hU _ (hnorm.trans_le (min_le_left _ _)) hpointU)).symm.trans
      (d39_arg_eq_of_mem_selfWedge hnonzero
        (hV _ (hnorm.trans_le (min_le_right _ _)) hpointV))

/-- Helper toward Proposition 5.16: radial germs preserve and reflect
equality of direction arguments; target injectivity needs no extra premise. -/
theorem d39_radial_germ_arg_eq_iff (K : ℂ ≃ₜ ℂ) (hK0 : K 0 = 0)
    (u v u' v' : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) (hu' : u' ≠ 0) (hv' : v' ≠ 0)
    (hsegmentsU : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * u} =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * u'})
    (hsegmentsV : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * v} =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * v'}) :
    u.arg = v.arg ↔ u'.arg = v'.arg := by
  constructor
  · intro h
    exact d39_radial_germ_arg_eq K hK0 u v u' v' hu hv h hsegmentsU hsegmentsV
  · intro h
    have hinv0 : K.symm 0 = 0 := by
      apply K.injective
      rw [K.apply_symm_apply, hK0]
    exact d39_radial_germ_arg_eq K.symm hinv0 u' v' u v hu' hv' h
      (d39_radial_germ_symm K u u' hsegmentsU)
      (d39_radial_germ_symm K v v' hsegmentsV)

/-- Helper toward Proposition 5.16: replacing a nonzero ray direction by
another with the same argument does not change its closed boundary ray. -/
theorem d39_selfWedge_eq_of_arg_eq {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (harg : u.arg = v.arg) : d39ClosedWedge u u = d39ClosedWedge v v := by
  have hsub : ∀ (a b : ℂ), a ≠ 0 → b ≠ 0 → a.arg = b.arg →
      d39ClosedWedge a a ⊆ d39ClosedWedge b b := by
    intro a b ha hb hab z hz
    obtain ⟨s, t, hs, ht, he⟩ := hz
    have he' := (Complex.arg_eq_arg_iff hb ha).mp hab.symm
    rw [← Complex.ofReal_div] at he'
    refine ⟨(s + t) * (‖a‖ / ‖b‖), 0,
      mul_nonneg (add_nonneg hs ht) (div_nonneg (norm_nonneg a) (norm_nonneg b)),
      le_rfl, ?_⟩
    calc
      z = ((s + t : ℝ) : ℂ) * a := by rw [he]; push_cast; ring
      _ = ((s + t : ℝ) : ℂ) * (((‖a‖ / ‖b‖ : ℝ) : ℂ) * b) :=
        congrArg (fun q : ℂ => ((s + t : ℝ) : ℂ) * q) he'.symm
      _ = _ := by push_cast; ring
  exact Set.Subset.antisymm (hsub u v hu hv harg) (hsub v u hv hu harg.symm)

/-- Helper toward Proposition 5.16: points on a ray sufficiently close to
zero lie on the segment from zero to its nonzero prescribed endpoint. -/
theorem d39_mem_segment_of_mem_selfWedge {u z : ℂ}
    (_hu : u ≠ 0) (hz : ‖z‖ < ‖u‖) (hray : z ∈ d39ClosedWedge u u) :
    z ∈ segment ℝ 0 u := by
  obtain ⟨a, b, ha, hb, he⟩ := hray
  have he' : z = ((a + b : ℝ) : ℂ) * u := by rw [he]; push_cast; ring
  have hbound : a + b ≤ 1 := by
    rw [he', norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg ha hb)] at hz
    exact (lt_of_mul_lt_mul_right (by simpa only [one_mul] using hz)
      (norm_nonneg u)).le
  rw [segment_eq_image']
  refine ⟨a + b, ⟨add_nonneg ha hb, hbound⟩, ?_⟩
  dsimp only
  rw [sub_zero, zero_add, RCLike.real_smul_eq_coe_mul]
  exact he'.symm

/-- Helper toward Proposition 5.16: every small disk contains a strict
interior point of a convex wedge whose negative lies strictly outside it. -/
theorem d39_exists_small_wedge_testPoint (u v : ℂ)
    (harea : 0 < (conj u * v).im) (r : ℝ) (hr : 0 < r) :
    ∃ z : ℂ, ‖z‖ < r ∧
      0 < (conj u * z).im ∧ 0 < (conj z * v).im ∧
      -z ∉ d39ClosedWedge u v := by
  let t := r / (2 * (‖u + v‖ + 1))
  have ht : 0 < t := div_pos hr (by positivity)
  let z := (t : ℂ) * (u + v)
  have hnorm : ‖z‖ < r := by
    rw [show z = (t : ℂ) * (u + v) from rfl, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    dsimp only [t]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg (u + v)]
  have hdetU : (conj u * z).im = t * (conj u * v).im := by
    simp only [z, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hdetV : (conj z * v).im = t * (conj u * v).im := by
    simp only [z, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  refine ⟨z, hnorm, by rw [hdetU]; exact mul_pos ht harea,
    by rw [hdetV]; exact mul_pos ht harea, ?_⟩
  intro hmem
  have hnonneg := d39_det_nonneg_of_mem_closedWedge u v (-z) harea.le hmem
  have he : (conj (-z) * v).im = -(conj z * v).im := by simp
  rw [he, hdetV] at hnonneg
  exact (not_le_of_gt (mul_pos ht harea)) (neg_nonneg.mp hnonneg)

/-- Helper toward Proposition 5.16: strict side tests avoid both boundary
rays of the tested wedge. -/
theorem d39_not_mem_boundary_of_strict_sides {u v z : ℂ}
    (hz : 0 < (conj u * z).im ∧ 0 < (conj z * v).im) :
    z ∉ d39ClosedWedge u u ∧ z ∉ d39ClosedWedge v v := by
  constructor
  · intro h
    exact hz.1.ne' (d39_det_eq_zero_of_mem_selfWedge u z h)
  · intro h
    have he := d39_det_eq_zero_of_mem_selfWedge v z h
    have hs : (conj z * v).im = -(conj v * z).im := by
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    rw [hs, he, neg_zero] at hz
    exact lt_irrefl 0 hz.2

/-- Helper toward Proposition 5.16: orientation preservation calibrates the
image triangle's local winding offset to zero when both endpoint turns are
convex and the radial pieces map into the prescribed endpoint rays. -/
theorem d39_image_triangle_radialLoop_winding
    (K : ℂ ≃ₜ ℂ) (hK : OrientationPreserving K) (hK0 : K 0 = 0)
    (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hpi : ccwTurn u v < Real.pi) (hpi' : ccwTurn (K u) (K v) < Real.pi)
    (hU : K '' segment ℝ 0 u ⊆ d39ClosedWedge (K u) (K u))
    (hV : K '' segment ℝ 0 v ⊆ d39ClosedWedge (K v) (K v)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, ‖z‖ < δ →
      ((0 < (conj (K u) * z).im ∧ 0 < (conj z * K v).im) →
        HasWinding (((Path.segment (0 : ℂ) u).trans
          ((Path.segment u v).trans (Path.segment v 0))).map K.continuous) z 1) ∧
      (z ∉ d39ClosedWedge (K u) (K v) →
        HasWinding (((Path.segment (0 : ℂ) u).trans
          ((Path.segment u v).trans (Path.segment v 0))).map K.continuous) z 0) := by
  have hKu : K u ≠ 0 := fun h => hu (K.injective (h.trans hK0.symm))
  have hKv : K v ≠ 0 := fun h => hv (K.injective (h.trans hK0.symm))
  let L := (Path.segment (0 : ℂ) u).trans
    ((Path.segment u v).trans (Path.segment v 0))
  let A := ((Path.segment (0 : ℂ) u).map K.continuous).cast hK0.symm rfl
  let P := (Path.segment u v).map K.continuous
  let B := ((Path.segment v (0 : ℂ)).map K.continuous).cast rfl hK0.symm
  let L' := A.trans (P.trans B)
  have hA : Set.range A ⊆ d39ClosedWedge (K u) (K u) := by
    rintro z ⟨t, rfl⟩
    apply hU
    refine ⟨(Path.segment (0 : ℂ) u) t, ?_, rfl⟩
    rw [← Path.range_segment]
    exact Set.mem_range_self t
  have hB : Set.range B ⊆ d39ClosedWedge (K v) (K v) := by
    rintro z ⟨t, rfl⟩
    apply hV
    refine ⟨(Path.segment v (0 : ℂ)) t, ?_, rfl⟩
    rw [segment_symm, ← Path.range_segment]
    exact Set.mem_range_self t
  have hP : (0 : ℂ) ∉ Set.range P := by
    rintro ⟨t, ht⟩
    have he : (Path.segment u v) t = 0 := K.injective (ht.trans hK0.symm)
    have hseg : (0 : ℂ) ∈ segment ℝ u v := by
      rw [← Path.range_segment]
      exact ⟨t, he⟩
    have hzero := d39_leftSide_eq_zero_of_mem_segment hseg
    have he' : (conj (v - u) * (0 - u)).im = (conj u * v).im := by
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.sub_re, Complex.sub_im, Complex.zero_re, Complex.zero_im]
      ring
    rw [he'] at hzero
    exact (d39_det_pos_of_ccwTurn_lt_pi u v hu hv (ccwTurn_pos u v) hpi).ne' hzero
  obtain ⟨δ, hδ, m, hlocal⟩ := d39_radialLoop_splitting_paths
    (K u) (K v) hKu hKv (ccwTurn_pos _ _) hpi' A P B hA hB hP
  have hmap (w : ℂ) (n : ℤ) :
      HasWinding L' w n ↔ HasWinding (L.map K.continuous) w n := by
    have hpath : L' = (L.map K.continuous).cast hK0.symm hK0.symm := by
      simp only [L', L, A, P, B, Path.map_trans]
      rfl
    rw [hpath]
    rfl
  obtain ⟨ε, hε, hsource⟩ := d39_triangleLoop_winding_zero_or_one_near_zero u v hu hv hpi
  have hinv0 : K.symm 0 = 0 := by
    apply K.injective
    rw [K.apply_symm_apply, hK0]
  let R := min ε (min ‖u‖ ‖v‖)
  have hR : 0 < R := lt_min hε (lt_min (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv))
  obtain ⟨η, hη, hηpre⟩ := Metric.continuousAt_iff.mp
    (K.symm.continuous.continuousAt (x := (0 : ℂ))) R hR
  have hvalues (w : ℂ) (hwη : ‖w‖ < η)
      (hwu : w ∉ d39ClosedWedge (K u) (K u))
      (hwv : w ∉ d39ClosedWedge (K v) (K v)) :
      HasWinding L' w 0 ∨ HasWinding L' w 1 := by
    have hpre : ‖K.symm w‖ < R := by
      have h := hηpre (by simpa only [dist_zero_right] using hwη)
      simpa only [hinv0, dist_zero_right] using h
    have hpreU : K.symm w ∉ d39ClosedWedge u u := by
      intro h
      apply hwu
      have hseg := d39_mem_segment_of_mem_selfWedge hu
        (hpre.trans_le ((min_le_right ε (min ‖u‖ ‖v‖)).trans (min_le_left _ _))) h
      have hmem := hU ⟨K.symm w, hseg, K.apply_symm_apply w⟩
      exact hmem
    have hpreV : K.symm w ∉ d39ClosedWedge v v := by
      intro h
      apply hwv
      have hseg := d39_mem_segment_of_mem_selfWedge hv
        (hpre.trans_le ((min_le_right ε (min ‖u‖ ‖v‖)).trans (min_le_right _ _))) h
      exact hV ⟨K.symm w, hseg, K.apply_symm_apply w⟩
    have hs := hsource (K.symm w) (hpre.trans_le (min_le_left _ _)) hpreU hpreV
    have htransport (n : ℤ) (hn : HasWinding L (K.symm w) n) : HasWinding L' w n := by
      apply (hmap w n).2
      have hh := (hK L (K.symm w) (d39_not_mem_range_of_hasWinding hn) n).1 hn
      simpa only [K.apply_symm_apply] using hh
    exact hs.elim (fun h => Or.inl (htransport 0 h)) (fun h => Or.inr (htransport 1 h))
  have harea := d39_det_pos_of_ccwTurn_lt_pi (K u) (K v) hKu hKv
    (ccwTurn_pos _ _) hpi'
  obtain ⟨w, hw, hwu, hwv, hout⟩ :=
    d39_exists_small_wedge_testPoint (K u) (K v) harea (min δ η) (lt_min hδ hη)
  have hboundU := (d39_selfWedge_subset_closedWedge (K u) (K v)).1
  have hboundV := (d39_selfWedge_subset_closedWedge (K u) (K v)).2
  have havoid := d39_not_mem_boundary_of_strict_sides ⟨hwu, hwv⟩
  have hinside := (hlocal w (hw.trans_le (min_le_left _ _))).1 ⟨hwu, hwv⟩
  have houtside := (hlocal (-w) (by
    rw [norm_neg]; exact hw.trans_le (min_le_left _ _))).2 hout
  have hmInside : m + 1 = 0 ∨ m + 1 = 1 :=
    (hvalues w (hw.trans_le (min_le_right _ _)) havoid.1 havoid.2).elim
      (fun h => Or.inl (hasWinding_unique hinside h))
      (fun h => Or.inr (hasWinding_unique hinside h))
  have hmOutside : m = 0 ∨ m = 1 :=
    (hvalues (-w) (by rw [norm_neg]; exact hw.trans_le (min_le_right _ _))
      (fun h => hout (hboundU h)) (fun h => hout (hboundV h))).elim
      (fun h => Or.inl (hasWinding_unique houtside h))
      (fun h => Or.inr (hasWinding_unique houtside h))
  have hm : m = 0 := by omega
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  constructor
  · intro hs
    apply (hmap z 1).1
    simpa only [hm, zero_add] using (hlocal z hz).1 hs
  · intro hs
    apply (hmap z 0).1
    simpa only [hm] using (hlocal z hz).2 hs

/-- Helper toward Proposition 5.16: the standard triangle's winding-one
test near zero is precisely its pair of strict side inequalities. -/
theorem d39_triangleLoop_hasWinding_one_iff_strict_sides
    (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) (hpi : ccwTurn u v < Real.pi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, ‖z‖ < δ →
      z ∉ d39ClosedWedge u u → z ∉ d39ClosedWedge v v →
      (HasWinding ((Path.segment (0 : ℂ) u).trans
        ((Path.segment u v).trans (Path.segment v 0))) z 1 ↔
        0 < (conj u * z).im ∧ 0 < (conj z * v).im) := by
  obtain ⟨δ, hδ, hlocal⟩ := d39_triangle_winding_near_zero 1 u v zero_lt_one hu hv
    (ccwTurn_pos u v) hpi
  have hpath : ((d39TrianglePolyline 1 u v).toPath.cast rfl
      (d39TrianglePolyline_closed 1 u v)) =
        (Path.segment (0 : ℂ) u).trans ((Path.segment u v).trans (Path.segment v 0)) := by
    apply Path.ext
    funext t
    change ((Path.segment (0 : ℂ) ((1 : ℂ) * u)).trans
      ((Path.segment ((1 : ℂ) * u) ((1 : ℂ) * v)).trans
        (Path.segment ((1 : ℂ) * v) 0))) t = _
    rw [one_mul, one_mul]
    rfl
  refine ⟨δ, hδ, ?_⟩
  intro z hz hzu hzv
  constructor
  · intro hw
    by_contra hs
    have hout : z ∉ d39ClosedWedge u v := by
      intro hm
      exact hs (d39_closedWedge_strict_of_not_boundary
        (d39_det_pos_of_ccwTurn_lt_pi u v hu hv (ccwTurn_pos u v) hpi) hm hzu hzv)
    have hzero := ((hlocal z hz).2 hout).2.2
    rw [hpath] at hzero
    have he := hasWinding_unique hw hzero
    norm_num at he
  · intro hs
    have hw := ((hlocal z hz).1 hs).2.2
    rw [hpath] at hw
    exact hw

/-- Helper toward Proposition 5.16: the calibrated image triangle detects
its target strict wedge near zero, away from the two boundary rays. -/
theorem d39_image_triangle_hasWinding_one_iff_strict_sides
    (K : ℂ ≃ₜ ℂ) (hK : OrientationPreserving K) (hK0 : K 0 = 0)
    (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hpi : ccwTurn u v < Real.pi) (hpi' : ccwTurn (K u) (K v) < Real.pi)
    (hU : K '' segment ℝ 0 u ⊆ d39ClosedWedge (K u) (K u))
    (hV : K '' segment ℝ 0 v ⊆ d39ClosedWedge (K v) (K v)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, ‖z‖ < δ →
      z ∉ d39ClosedWedge (K u) (K u) → z ∉ d39ClosedWedge (K v) (K v) →
      (HasWinding (((Path.segment (0 : ℂ) u).trans
        ((Path.segment u v).trans (Path.segment v 0))).map K.continuous) z 1 ↔
        0 < (conj (K u) * z).im ∧ 0 < (conj z * K v).im) := by
  obtain ⟨δ, hδ, hlocal⟩ := d39_image_triangle_radialLoop_winding K hK hK0 u v hu hv
    hpi hpi' hU hV
  have hKu : K u ≠ 0 := fun h => hu (K.injective (h.trans hK0.symm))
  have hKv : K v ≠ 0 := fun h => hv (K.injective (h.trans hK0.symm))
  refine ⟨δ, hδ, ?_⟩
  intro z hz hzu hzv
  constructor
  · intro hw
    by_contra hs
    have hout : z ∉ d39ClosedWedge (K u) (K v) := by
      intro hm
      exact hs (d39_closedWedge_strict_of_not_boundary
        (d39_det_pos_of_ccwTurn_lt_pi (K u) (K v) hKu hKv (ccwTurn_pos _ _) hpi') hm hzu hzv)
    have he := hasWinding_unique hw ((hlocal z hz).2 hout)
    norm_num at he
  · exact (hlocal z hz).1

/-- Helper toward Proposition 5.16: radial germ data control the entire
image of every sufficiently short initial radial segment. -/
theorem d39_radial_germ_segment_image
    (K : ℂ ≃ₜ ℂ) (hK0 : K 0 = 0) (u u' : ℂ) (hu : u ≠ 0)
    (hsegments : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * u} =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * u'}) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, 0 < t → t ≤ r →
      K '' segment ℝ 0 ((t : ℂ) * u) ⊆ d39ClosedWedge u' u' := by
  obtain ⟨r, hr, hsmall⟩ := d39_radial_germ_image_positive K hK0 u u' hu hsegments
  refine ⟨r, hr, ?_⟩
  intro t ht htr z hz
  obtain ⟨p, hp, rfl⟩ := hz
  rw [segment_eq_image'] at hp
  obtain ⟨a, ha, hpa⟩ := hp
  have he : p = ((a * t : ℝ) : ℂ) * u := by
    rw [← hpa]
    dsimp only
    rw [sub_zero, zero_add, RCLike.real_smul_eq_coe_mul]
    push_cast
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  by_cases ha0 : a = 0
  · rw [he, ha0, zero_mul, Complex.ofReal_zero, zero_mul, hK0]
    exact d39_zero_mem_closedWedge u' u'
  · have hat : 0 < a * t := mul_pos (lt_of_le_of_ne ha.1 (Ne.symm ha0)) ht
    have hatr : a * t ≤ r := (mul_le_of_le_one_left ht.le ha.2).trans htr
    obtain ⟨s, hs, hKs⟩ := hsmall (a * t) hat hatr
    exact ⟨s, 0, hs.le, le_rfl, by simpa [he] using hKs⟩

/-- Helper toward Proposition 5.16: the triple lemma for convex endpoint
turns on both sides, with arbitrary third direction and the exact initial
segment-image hypotheses. -/
theorem d39_radial_germ_between_iff_of_convex
    (K : ℂ ≃ₜ ℂ) (hK : OrientationPreserving K) (hK0 : K 0 = 0)
    (u v w u' v' w' : ℂ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hu' : u' ≠ 0) (hv' : v' ≠ 0) (hw' : w' ≠ 0)
    (huw : u.arg ≠ w.arg) (hvw : v.arg ≠ w.arg)
    (hpi : ccwTurn u v < Real.pi) (hpi' : ccwTurn u' v' < Real.pi)
    (hsegmentsU : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * u} =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * u'})
    (hsegmentsV : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * v} =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * v'})
    (hsegmentsW : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * w} =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * w'}) :
    ccwTurn u w < ccwTurn u v ↔ ccwTurn u' w' < ccwTurn u' v' := by
  obtain ⟨ru, hru, hruSeg⟩ := d39_radial_germ_segment_image K hK0 u u' hu hsegmentsU
  obtain ⟨rv, hrv, hrvSeg⟩ := d39_radial_germ_segment_image K hK0 v v' hv hsegmentsV
  let r := min ru rv / 2
  have hr : 0 < r := half_pos (lt_min hru hrv)
  have hru' : r ≤ ru := (half_le_self (lt_min hru hrv).le).trans (min_le_left _ _)
  have hrv' : r ≤ rv := (half_le_self (lt_min hru hrv).le).trans (min_le_right _ _)
  let a := (r : ℂ) * u
  let b := (r : ℂ) * v
  have ha : a ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hu
  have hb : b ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hv
  have haarg : a.arg = u.arg := Complex.arg_real_mul u hr
  have hbarg : b.arg = v.arg := Complex.arg_real_mul v hr
  have hKa : K a ≠ 0 := fun h => ha (K.injective (h.trans hK0.symm))
  have hKb : K b ≠ 0 := fun h => hb (K.injective (h.trans hK0.symm))
  have hSU := hruSeg r hr hru'
  have hSV := hrvSeg r hr hrv'
  have hKaarg : (K a).arg = u'.arg := d39_arg_eq_of_mem_selfWedge hKa
    (hSU ⟨a, right_mem_segment ℝ 0 a, rfl⟩)
  have hKbarg : (K b).arg = v'.arg := d39_arg_eq_of_mem_selfWedge hKb
    (hSV ⟨b, right_mem_segment ℝ 0 b, rfl⟩)
  have hU : K '' segment ℝ 0 a ⊆ d39ClosedWedge (K a) (K a) := by
    rw [d39_selfWedge_eq_of_arg_eq hKa hu' hKaarg]
    exact hSU
  have hV : K '' segment ℝ 0 b ⊆ d39ClosedWedge (K b) (K b) := by
    rw [d39_selfWedge_eq_of_arg_eq hKb hv' hKbarg]
    exact hSV
  have habpi : ccwTurn a b < Real.pi := by simpa only [ccwTurn, haarg, hbarg] using hpi
  have hKabpi : ccwTurn (K a) (K b) < Real.pi := by
    simpa only [ccwTurn, hKaarg, hKbarg] using hpi'
  obtain ⟨ε, hε, hsource⟩ := d39_triangleLoop_hasWinding_one_iff_strict_sides a b ha hb habpi
  obtain ⟨ε₀, hε₀, hzeroone⟩ := d39_triangleLoop_winding_zero_or_one_near_zero a b ha hb habpi
  obtain ⟨δ, hδ, htarget⟩ := d39_image_triangle_hasWinding_one_iff_strict_sides
    K hK hK0 a b ha hb habpi hKabpi hU hV
  obtain ⟨η, hη, hηmap⟩ := Metric.continuousAt_iff.mp
    (K.continuous.continuousAt (x := (0 : ℂ))) δ hδ
  obtain ⟨κ, hκ, hκmap⟩ := d39_radial_germ_image_selfWedge K w w' hw hsegmentsW
  let R := min ε (min ε₀ (min η κ))
  have hR : 0 < R := lt_min hε (lt_min hε₀ (lt_min hη hκ))
  let t := R / (2 * (‖w‖ + 1))
  have ht : 0 < t := div_pos hR (by positivity)
  let z := (t : ℂ) * w
  have hz : z ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne') hw
  have hzarg : z.arg = w.arg := Complex.arg_real_mul w ht
  have hznorm : ‖z‖ < R := by
    rw [show z = (t : ℂ) * w from rfl, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht]
    dsimp only [t]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg w]
  have hzε := hznorm.trans_le (min_le_left ε (min ε₀ (min η κ)))
  have hzε₀ := hznorm.trans_le
    ((min_le_right ε (min ε₀ (min η κ))).trans (min_le_left ε₀ (min η κ)))
  have hzη := hznorm.trans_le
    ((min_le_right ε (min ε₀ (min η κ))).trans
      ((min_le_right ε₀ (min η κ)).trans (min_le_left η κ)))
  have hzκ := hznorm.trans_le
    ((min_le_right ε (min ε₀ (min η κ))).trans
      ((min_le_right ε₀ (min η κ)).trans (min_le_right η κ)))
  have hKznorm : ‖K z‖ < δ := by
    have h := hηmap (by simpa only [dist_zero_right] using hzη)
    simpa only [hK0, dist_zero_right] using h
  have hKz : K z ≠ 0 := fun h => hz (K.injective (h.trans hK0.symm))
  have hKzarg : (K z).arg = w'.arg := d39_arg_eq_of_mem_selfWedge hKz
    (hκmap z hzκ ⟨t, 0, ht.le, le_rfl, by simp [z]⟩)
  have huw' : u'.arg ≠ w'.arg := fun h => huw
    ((d39_radial_germ_arg_eq_iff K hK0 u w u' w' hu hw hu' hw'
      hsegmentsU hsegmentsW).2 h)
  have hvw' : v'.arg ≠ w'.arg := fun h => hvw
    ((d39_radial_germ_arg_eq_iff K hK0 v w v' w' hv hw hv' hw'
      hsegmentsV hsegmentsW).2 h)
  have hza : z ∉ d39ClosedWedge a a := by
    intro h
    have he := d39_arg_eq_of_mem_selfWedge hz h
    exact huw (by simpa only [haarg, hzarg] using he.symm)
  have hzb : z ∉ d39ClosedWedge b b := by
    intro h
    have he := d39_arg_eq_of_mem_selfWedge hz h
    exact hvw (by simpa only [hbarg, hzarg] using he.symm)
  have hKza : K z ∉ d39ClosedWedge (K a) (K a) := by
    intro h
    have he := d39_arg_eq_of_mem_selfWedge hKz h
    exact huw' (by simpa only [hKaarg, hKzarg] using he.symm)
  have hKzb : K z ∉ d39ClosedWedge (K b) (K b) := by
    intro h
    have he := d39_arg_eq_of_mem_selfWedge hKz h
    exact hvw' (by simpa only [hKbarg, hKzarg] using he.symm)
  have havoid := (hzeroone z hzε₀ hza hzb).elim
    (fun h => d39_not_mem_range_of_hasWinding h) (fun h => d39_not_mem_range_of_hasWinding h)
  have hsides : (0 < (conj a * z).im ∧ 0 < (conj z * b).im) ↔
      ccwTurn u w < ccwTurn u v := by
    rw [d39_strict_sides_iff_between ha hb hz habpi]
    simp only [ccwTurn, haarg, hbarg, hzarg]
  have htsides : (0 < (conj (K a) * K z).im ∧ 0 < (conj (K z) * K b).im) ↔
      ccwTurn u' w' < ccwTurn u' v' := by
    rw [d39_strict_sides_iff_between hKa hKb hKz hKabpi]
    simp only [ccwTurn, hKaarg, hKbarg, hKzarg]
  exact hsides.symm.trans ((hsource z hzε hza hzb).symm.trans
    ((hK _ z havoid 1).trans ((htarget (K z) hKznorm hKza hKzb).trans htsides)))

/-- Helper toward Proposition 5.16: complementary convex wedges give the
triple lemma when both endpoint turns are strictly reflex. -/
theorem d39_radial_germ_between_iff_of_reflex
    (K : ℂ ≃ₜ ℂ) (hK : OrientationPreserving K) (hK0 : K 0 = 0)
    (u v w u' v' w' : ℂ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hu' : u' ≠ 0) (hv' : v' ≠ 0) (hw' : w' ≠ 0)
    (huv : u.arg ≠ v.arg) (huw : u.arg ≠ w.arg) (hvw : v.arg ≠ w.arg)
    (hpi : Real.pi < ccwTurn u v) (hpi' : Real.pi < ccwTurn u' v')
    (hsegmentsU : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * u} =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * u'})
    (hsegmentsV : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * v} =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * v'})
    (hsegmentsW : ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * w} =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * w'}) :
    ccwTurn u w < ccwTurn u v ↔ ccwTurn u' w' < ccwTurn u' v' := by
  have huv' : u'.arg ≠ v'.arg := fun h => huv
    ((d39_radial_germ_arg_eq_iff K hK0 u v u' v' hu hv hu' hv'
      hsegmentsU hsegmentsV).2 h)
  have huw' : u'.arg ≠ w'.arg := fun h => huw
    ((d39_radial_germ_arg_eq_iff K hK0 u w u' w' hu hw hu' hw'
      hsegmentsU hsegmentsW).2 h)
  have hvw' : v'.arg ≠ w'.arg := fun h => hvw
    ((d39_radial_germ_arg_eq_iff K hK0 v w v' w' hv hw hv' hw'
      hsegmentsV hsegmentsW).2 h)
  have hc : ccwTurn v u < Real.pi := by
    have hsum := ccwTurn_add_reverse u v huv
    linarith
  have hc' : ccwTurn v' u' < Real.pi := by
    have hsum := ccwTurn_add_reverse u' v' huv'
    linarith
  rw [d39_between_iff_not_reverse huv hvw huw.symm,
    d39_between_iff_not_reverse huv' hvw' huw'.symm]
  exact not_congr (d39_radial_germ_between_iff_of_convex K hK hK0 v u w v' u' w'
    hv hu hw hv' hu' hw' hvw huw hc hc' hsegmentsV hsegmentsU hsegmentsW)












































end DirectedDistances.PlanarMap

end
