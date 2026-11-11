/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PolygonEdgeJump

/-! # One-sided edge-angle limits

Helpers toward Proposition 5.16. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap
namespace Polyline

open Filter Topology
open scoped ComplexConjugate

/-- Helper toward Proposition 5.16: the imaginary part of the edge quotient,
multiplied by the squared denominator norm, is the oriented side coordinate.
The sign is the same as that of the displayed side coordinate. -/
theorem edgeQuotient_im_mul_normSq (p : Polyline) (i : ℕ) (z : ℂ) :
    (((p.point (i + 1) - z) / (p.point i - z)).im) *
        ‖p.point i - z‖ ^ 2 =
      (conj (p.point (i + 1) - p.point i) * (z - p.point i)).im := by
  let a := p.point i
  let b := p.point (i + 1)
  let d := a - z
  let e := b - a
  have hnum : b - z = d + e := by
    dsimp [d, e, a, b]
    ring
  by_cases hd : d = 0
  · have hza : z = a := by dsimp [d] at hd; exact (sub_eq_zero.mp hd).symm
    subst z
    simp [a]
  · have hns : Complex.normSq d ≠ 0 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hd)
    rw [show p.point (i + 1) - z = d + e by exact hnum,
      show p.point i - z = d by rfl]
    rw [Complex.div_im, ← Complex.normSq_eq_norm_sq]
    rw [sub_mul, div_mul_cancel₀ _ hns, div_mul_cancel₀ _ hns]
    simp only [Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im,
      Complex.mul_im]
    dsimp [d, e, a, b]
    ring

/-- Helper toward Proposition 5.16: on the edge's affine line, the edge
quotient has imaginary part with the sign of the oriented side coordinate
based at the observation point `x`. -/
theorem edgeQuotient_im_mul_normSq_eq_side (p : Polyline) (i : ℕ) (x : ℂ)
    (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1)) (z : ℂ) :
    (((p.point (i + 1) - z) / (p.point i - z)).im) *
        ‖p.point i - z‖ ^ 2 =
      (conj (p.point (i + 1) - p.point i) * (z - x)).im := by
  have hbase := edgeQuotient_im_mul_normSq p i z
  obtain ⟨t, ht, ht1, htx⟩ :=
    exists_parameter_Ioo_of_mem_segmentAt p i x hx hxi hxi1
  let e := p.point (i + 1) - p.point i
  have hxline : x - p.point i = t • (p.point (i + 1) - p.point i) := by
    rw [htx]
    simp
  have hprod : conj e * e = (Complex.normSq e : ℂ) := by
    rw [mul_comm, Complex.mul_conj]
  have hlineim :
      (conj (p.point (i + 1) - p.point i) * (x - p.point i)).im = 0 := by
    rw [hxline, RCLike.real_smul_eq_coe_mul]
    have hmul : conj e * ((t : ℂ) * e) = (t : ℂ) * (conj e * e) := by
      dsimp [e]
      ring
    change (conj e * ((t : ℂ) * e)).im = 0
    rw [hmul, hprod]
    simp
  have hzsplit : z - p.point i = (z - x) + (x - p.point i) := by ring
  rw [hzsplit, mul_add, Complex.add_im, hlineim] at hbase
  simpa only [add_zero] using hbase

/-- Helper toward Proposition 5.16: approaching an interior edge point from
the positive oriented side, the principal edge angle tends to `pi`. -/
theorem tendsto_edgeAngle_nhdsWithin_pos (p : Polyline) (hsimple : p.IsSimple)
    (i : ℕ) (hi : i + 1 < p.points.length) (x : ℂ)
    (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1)) :
    Tendsto (fun z : ℂ => p.edgeAngle z i)
      (𝓝[{z | 0 < (conj (p.point (i + 1) - p.point i) * (z - x)).im}] x)
      (𝓝 Real.pi) := by
  let q : ℂ → ℂ := fun z => (p.point (i + 1) - z) / (p.point i - z)
  have hden : p.point i - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxi)
  have hqcont : ContinuousAt q x := by
    dsimp [q]
    exact (continuousAt_const.sub continuousAt_id).div
      (continuousAt_const.sub continuousAt_id) hden
  obtain ⟨hre, him⟩ := edgeQuotient_at_segmentInterior p hsimple i hi x hx hxi hxi1
  have hpos : ∀ᶠ z : ℂ in
      𝓝[{z | 0 < (conj (p.point (i + 1) - p.point i) * (z - x)).im}] x,
      0 < (q z).im := by
    filter_upwards [self_mem_nhdsWithin, eventually_ne_nhdsWithin hxi] with z hzside hza
    have hdenz : p.point i - z ≠ 0 := by
      intro h
      exact hza (sub_eq_zero.mp h).symm
    have hN : 0 < ‖p.point i - z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hdenz)
    have hid := edgeQuotient_im_mul_normSq_eq_side p i x hx hxi hxi1 z
    change (q z).im * ‖p.point i - z‖ ^ 2 =
      (conj (p.point (i + 1) - p.point i) * (z - x)).im at hid
    have hqpos : 0 < (q z).im := by
      by_contra hnot
      have hqle : (q z).im ≤ 0 := le_of_not_gt hnot
      have hmul : (q z).im * ‖p.point i - z‖ ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hqle hN.le
      rw [hid] at hmul
      exact (not_le_of_gt hzside) hmul
    exact hqpos
  have hq' : Tendsto q
      (𝓝[{z | 0 < (conj (p.point (i + 1) - p.point i) * (z - x)).im}] x)
      (𝓝[{w | 0 ≤ w.im}] (q x)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hqcont.tendsto.mono_left nhdsWithin_le_nhds,
      hpos.mono fun z hz => le_of_lt hz⟩
  have harg :=
    (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
      (by simpa [q] using hre) (by simpa [q] using him)).comp hq'
  convert harg using 1
  ext z
  rfl

/-- Helper toward Proposition 5.16: approaching an interior edge point from
the negative oriented side, the principal edge angle tends to `-pi`. -/
theorem tendsto_edgeAngle_nhdsWithin_neg (p : Polyline) (hsimple : p.IsSimple)
    (i : ℕ) (hi : i + 1 < p.points.length) (x : ℂ)
    (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1)) :
    Tendsto (fun z : ℂ => p.edgeAngle z i)
      (𝓝[{z | (conj (p.point (i + 1) - p.point i) * (z - x)).im < 0}] x)
      (𝓝 (-Real.pi)) := by
  let q : ℂ → ℂ := fun z => (p.point (i + 1) - z) / (p.point i - z)
  have hden : p.point i - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxi)
  have hqcont : ContinuousAt q x := by
    dsimp [q]
    exact (continuousAt_const.sub continuousAt_id).div
      (continuousAt_const.sub continuousAt_id) hden
  obtain ⟨hre, him⟩ := edgeQuotient_at_segmentInterior p hsimple i hi x hx hxi hxi1
  have hneg : ∀ᶠ z : ℂ in
      𝓝[{z | (conj (p.point (i + 1) - p.point i) * (z - x)).im < 0}] x,
      (q z).im < 0 := by
    filter_upwards [self_mem_nhdsWithin, eventually_ne_nhdsWithin hxi] with z hzside hza
    have hdenz : p.point i - z ≠ 0 := by
      intro h
      exact hza (sub_eq_zero.mp h).symm
    have hN : 0 < ‖p.point i - z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hdenz)
    have hid := edgeQuotient_im_mul_normSq_eq_side p i x hx hxi hxi1 z
    change (q z).im * ‖p.point i - z‖ ^ 2 =
      (conj (p.point (i + 1) - p.point i) * (z - x)).im at hid
    have hqneg : (q z).im < 0 := by
      by_contra hnot
      have hqge : 0 ≤ (q z).im := le_of_not_gt hnot
      have hmul : 0 ≤ (q z).im * ‖p.point i - z‖ ^ 2 :=
        mul_nonneg hqge hN.le
      rw [hid] at hmul
      exact (not_le_of_gt hzside) hmul
    exact hqneg
  have hq' : Tendsto q
      (𝓝[{z | (conj (p.point (i + 1) - p.point i) * (z - x)).im < 0}] x)
      (𝓝[{w | w.im < 0}] (q x)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hqcont.tendsto.mono_left nhdsWithin_le_nhds,
      hneg.mono fun z hz => hz⟩
  have harg :=
    (Complex.tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero
      (by simpa [q] using hre) (by simpa [q] using him)).comp hq'
  convert harg using 1
  ext z
  rfl

private theorem tendsto_angleSum_nhdsWithin_of_edge (p : Polyline)
    (hsimple : p.IsSimple) (i : ℕ) (hi : i + 1 < p.points.length) (x : ℂ)
    (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1)) (s : Set ℂ) (L : ℝ)
    (hedge : Tendsto (fun z : ℂ => p.edgeAngle z i) (𝓝[s] x) (𝓝 L)) :
    Tendsto (fun z : ℂ => p.angleSum z) (𝓝[s] x)
      (𝓝 ((∑ j ∈ Finset.range (p.points.length - 1),
        if j = i then L else p.edgeAngle x j) / (2 * Real.pi))) := by
  have hsum : ∀ t : Finset ℕ, (∀ j ∈ t, j + 1 < p.points.length) →
      Tendsto (fun z : ℂ => ∑ j ∈ t, p.edgeAngle z j) (𝓝[s] x)
        (𝓝 (∑ j ∈ t, if j = i then L else p.edgeAngle x j)) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        intro _
        simpa using (tendsto_const_nhds :
          Tendsto (fun _ : ℂ => (0 : ℝ)) (𝓝[s] x) (𝓝 0))
    | @insert j t hji ih =>
        intro hbound
        have hj : j + 1 < p.points.length := hbound j (Finset.mem_insert_self j t)
        have ht : ∀ k ∈ t, k + 1 < p.points.length :=
          fun k hk => hbound k (Finset.mem_insert_of_mem hk)
        have hedgej : Tendsto (fun z : ℂ => p.edgeAngle z j) (𝓝[s] x)
            (𝓝 (if j = i then L else p.edgeAngle x j)) := by
          by_cases hji' : j = i
          · subst j
            simpa using hedge
          · have hxj := not_mem_segmentAt_of_ne p hsimple i hi x hx hxi hxi1 j hj hji'
            have hc := continuousAt_edgeAngle_of_not_mem_segmentAt p x j hxj
            simpa [hji'] using hc.tendsto.mono_left nhdsWithin_le_nhds
        simpa only [Finset.sum_insert hji] using hedgej.add (ih ht)
  have htotal := hsum (Finset.range (p.points.length - 1)) (by
    intro j hj
    simp only [Finset.mem_range] at hj
    omega)
  simpa [angleSum] using htotal.div_const (2 * Real.pi)

/-- Helper toward Proposition 5.16: the normalized angle sum has a one-sided
limit from the positive oriented side of an interior edge point. -/
theorem tendsto_angleSum_nhdsWithin_pos (p : Polyline) (hsimple : p.IsSimple)
    (i : ℕ) (hi : i + 1 < p.points.length) (x : ℂ)
    (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1)) :
    Tendsto (fun z : ℂ => p.angleSum z)
      (𝓝[{z | 0 < (conj (p.point (i + 1) - p.point i) * (z - x)).im}] x)
      (𝓝 ((∑ j ∈ Finset.range (p.points.length - 1),
        if j = i then Real.pi else p.edgeAngle x j) / (2 * Real.pi))) := by
  exact tendsto_angleSum_nhdsWithin_of_edge p hsimple i hi x hx hxi hxi1 _ _
    (tendsto_edgeAngle_nhdsWithin_pos p hsimple i hi x hx hxi hxi1)

/-- Helper toward Proposition 5.16: the normalized angle sum has a one-sided
limit from the negative oriented side of an interior edge point. -/
theorem tendsto_angleSum_nhdsWithin_neg (p : Polyline) (hsimple : p.IsSimple)
    (i : ℕ) (hi : i + 1 < p.points.length) (x : ℂ)
    (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1)) :
    Tendsto (fun z : ℂ => p.angleSum z)
      (𝓝[{z | (conj (p.point (i + 1) - p.point i) * (z - x)).im < 0}] x)
      (𝓝 ((∑ j ∈ Finset.range (p.points.length - 1),
        if j = i then -Real.pi else p.edgeAngle x j) / (2 * Real.pi))) := by
  exact tendsto_angleSum_nhdsWithin_of_edge p hsimple i hi x hx hxi hxi1 _ _
    (tendsto_edgeAngle_nhdsWithin_neg p hsimple i hi x hx hxi hxi1)

private theorem int_sub_eq_one_of_abs_lt_half (m n : ℤ)
    (h : |((m - n : ℤ) : ℝ) - 1| < 1 / 2) : m - n = 1 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : m - n ≤ 0 := by omega
    have hle' : ((m - n : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hle
    have hh := abs_lt.mp h
    linarith
  · have hge : 2 ≤ m - n := by omega
    have hge' : (2 : ℝ) ≤ ((m - n : ℤ) : ℝ) := by exact_mod_cast hge
    have hh := abs_lt.mp h
    linarith

/-- Helper toward Proposition 5.16: the normalized angle sum jumps by one
across the interior of a simple closed polygonal edge. -/
theorem angleSum_edge_jump (p : Polyline) (hsimple : p.IsSimple)
    (hclosed : p.start = p.finish) (i : ℕ) (hi : i + 1 < p.points.length)
    (x : ℂ) (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (u v : ℂ), u ∉ p.image → v ∉ p.image →
        dist u x < ε → dist v x < ε →
        ((conj (p.point (i + 1) - p.point i) * (u - x)).im) *
          ((conj (p.point (i + 1) - p.point i) * (v - x)).im) < 0 →
        |p.angleSum u - p.angleSum v| = 1 := by
  let s := Finset.range (p.points.length - 1)
  let Lpos := (∑ j ∈ s, if j = i then Real.pi else p.edgeAngle x j) /
    (2 * Real.pi)
  let Lneg := (∑ j ∈ s, if j = i then -Real.pi else p.edgeAngle x j) /
    (2 * Real.pi)
  have hiMem : i ∈ s := by
    simp [s]
    omega
  have hsumdiff :
      (∑ j ∈ s, if j = i then Real.pi else p.edgeAngle x j) -
        (∑ j ∈ s, if j = i then -Real.pi else p.edgeAngle x j) =
      2 * Real.pi := by
    calc
      _ = ∑ j ∈ s,
          ((if j = i then Real.pi else p.edgeAngle x j) -
            (if j = i then -Real.pi else p.edgeAngle x j)) := by
              rw [Finset.sum_sub_distrib]
      _ = (if i = i then Real.pi else p.edgeAngle x i) -
            (if i = i then -Real.pi else p.edgeAngle x i) := by
              apply Finset.sum_eq_single_of_mem i hiMem
              intro j hj hji
              simp [hji]
      _ = 2 * Real.pi := by simp; ring
  have hLdiff : Lpos - Lneg = 1 := by
    dsimp [Lpos, Lneg]
    rw [← sub_div, hsumdiff]
    field_simp [Real.pi_ne_zero]
  have hpos := tendsto_angleSum_nhdsWithin_pos p hsimple i hi x hx hxi hxi1
  have hneg := tendsto_angleSum_nhdsWithin_neg p hsimple i hi x hx hxi hxi1
  have hevpos : ∀ᶠ z : ℂ in 𝓝 x,
      z ∈ {z | 0 < (conj (p.point (i + 1) - p.point i) * (z - x)).im} →
        dist (p.angleSum z) Lpos < 1 / 4 := by
    have hb := Metric.ball_mem_nhds Lpos (by norm_num : 0 < (1 / 4 : ℝ))
    have hevent := hpos.eventually hb
    have hwithin : ∀ᶠ z : ℂ in
        𝓝[{z | 0 < (conj (p.point (i + 1) - p.point i) * (z - x)).im}] x,
        dist (p.angleSum z) Lpos < 1 / 4 := by
      simpa [Metric.mem_ball, Lpos, s] using hevent
    exact eventually_nhdsWithin_iff.mp hwithin
  have hevneg : ∀ᶠ z : ℂ in 𝓝 x,
      z ∈ {z | (conj (p.point (i + 1) - p.point i) * (z - x)).im < 0} →
        dist (p.angleSum z) Lneg < 1 / 4 := by
    have hb := Metric.ball_mem_nhds Lneg (by norm_num : 0 < (1 / 4 : ℝ))
    have hevent := hneg.eventually hb
    have hwithin : ∀ᶠ z : ℂ in
        𝓝[{z | (conj (p.point (i + 1) - p.point i) * (z - x)).im < 0}] x,
        dist (p.angleSum z) Lneg < 1 / 4 := by
      simpa [Metric.mem_ball, Lneg, s] using hevent
    exact eventually_nhdsWithin_iff.mp hwithin
  obtain ⟨εp, hεp, hnearpos⟩ := Metric.eventually_nhds_iff.mp hevpos
  obtain ⟨εn, hεn, hnearneg⟩ := Metric.eventually_nhds_iff.mp hevneg
  refine ⟨min εp εn, lt_min hεp hεn, ?_⟩
  intro u v hu hv hux hvx hcross
  have hux' : dist u x < εp := lt_of_lt_of_le hux (min_le_left _ _)
  have hvx' : dist v x < εn := lt_of_lt_of_le hvx (min_le_right _ _)
  have huxn : dist u x < εn := lt_of_lt_of_le hux (min_le_right _ _)
  have hvxp : dist v x < εp := lt_of_lt_of_le hvx (min_le_left _ _)
  rcases mul_neg_iff.mp hcross with ⟨huPos, hvNeg⟩ | ⟨huNeg, hvPos⟩
  · have huNear := hnearpos hux' (by simpa using huPos)
    have hvNear := hnearneg hvx' (by simpa using hvNeg)
    have huClose : |p.angleSum u - Lpos| < 1 / 4 := by
      simpa [Real.dist_eq] using huNear
    have hvClose : |p.angleSum v - Lneg| < 1 / 4 := by
      simpa [Real.dist_eq] using hvNear
    have hclose : |(p.angleSum u - p.angleSum v) - 1| < 1 / 2 := by
      have heq : (p.angleSum u - p.angleSum v) - 1 =
          (p.angleSum u - Lpos) + -(p.angleSum v - Lneg) := by linarith [hLdiff]
      calc
        _ = |(p.angleSum u - Lpos) + -(p.angleSum v - Lneg)| := by rw [heq]
        _ ≤ |p.angleSum u - Lpos| + |p.angleSum v - Lneg| := by
          calc
            |(p.angleSum u - Lpos) + -(p.angleSum v - Lneg)| ≤
                |p.angleSum u - Lpos| + |-(p.angleSum v - Lneg)| := abs_add_le _ _
            _ = |p.angleSum u - Lpos| + |p.angleSum v - Lneg| := by rw [abs_neg]
        _ < 1 / 2 := by linarith
    obtain ⟨m, hm⟩ := angleSum_isInt p hclosed u hu
    obtain ⟨n, hn⟩ := angleSum_isInt p hclosed v hv
    have hcast : |((m - n : ℤ) : ℝ) - 1| < 1 / 2 := by
      simpa [hm, hn, Int.cast_sub] using hclose
    have hmn := int_sub_eq_one_of_abs_lt_half m n hcast
    have hdiff : p.angleSum u - p.angleSum v = 1 := by
      rw [hm, hn, ← Int.cast_sub, hmn]
      norm_num
    rw [hdiff]
    norm_num
  · have huNear := hnearneg huxn (by simpa using huNeg)
    have hvNear := hnearpos hvxp (by simpa using hvPos)
    have huClose : |p.angleSum u - Lneg| < 1 / 4 := by
      simpa [Real.dist_eq] using huNear
    have hvClose : |p.angleSum v - Lpos| < 1 / 4 := by
      simpa [Real.dist_eq] using hvNear
    have hclose : |(p.angleSum v - p.angleSum u) - 1| < 1 / 2 := by
      have heq : (p.angleSum v - p.angleSum u) - 1 =
          (p.angleSum v - Lpos) + -(p.angleSum u - Lneg) := by linarith [hLdiff]
      calc
        _ = |(p.angleSum v - Lpos) + -(p.angleSum u - Lneg)| := by rw [heq]
        _ ≤ |p.angleSum v - Lpos| + |p.angleSum u - Lneg| := by
          calc
            |(p.angleSum v - Lpos) + -(p.angleSum u - Lneg)| ≤
                |p.angleSum v - Lpos| + |-(p.angleSum u - Lneg)| := abs_add_le _ _
            _ = |p.angleSum v - Lpos| + |p.angleSum u - Lneg| := by rw [abs_neg]
        _ < 1 / 2 := by linarith
    obtain ⟨m, hm⟩ := angleSum_isInt p hclosed v hv
    obtain ⟨n, hn⟩ := angleSum_isInt p hclosed u hu
    have hcast : |((m - n : ℤ) : ℝ) - 1| < 1 / 2 := by
      simpa [hm, hn, Int.cast_sub] using hclose
    have hmn := int_sub_eq_one_of_abs_lt_half m n hcast
    have hdiff : p.angleSum v - p.angleSum u = 1 := by
      rw [hm, hn, ← Int.cast_sub, hmn]
      norm_num
    rw [show p.angleSum u - p.angleSum v =
      -(p.angleSum v - p.angleSum u) by ring, hdiff]
    norm_num

end Polyline
end DirectedDistances.PlanarMap

end
