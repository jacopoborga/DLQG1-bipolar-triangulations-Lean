/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PolygonalSeparation4

/-! # Cyclic angle jump for polygonal separation

Helpers toward Proposition 5.16. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap
namespace Polyline

open Filter Topology
open scoped ComplexConjugate

/-- Helper toward Proposition 5.16: at an interior point of a nondegenerate
edge, its edge quotient is a negative real number, without requiring linear
simplicity of the whole polyline. -/
theorem edgeQuotient_at_segmentInterior_cyclic (p : Polyline)
    (i : ℕ) (_hi : i + 1 < p.points.length) (x : ℂ)
    (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1))
    (hne : p.point i ≠ p.point (i + 1)) :
    let q : ℂ := (p.point (i + 1) - x) / (p.point i - x)
    q.re < 0 ∧ q.im = 0 := by
  obtain ⟨t, ht, ht1, htx⟩ :=
    exists_parameter_Ioo_of_mem_segmentAt p i x hx hxi hxi1
  let a := p.point i
  let b := p.point (i + 1)
  let d : ℂ := b - a
  have hd : d ≠ 0 := by
    dsimp [d, a, b]
    exact sub_ne_zero.mpr (Ne.symm hne)
  have htx' : x = a + (t : ℂ) * d := by
    simpa [a, b, d, RCLike.real_smul_eq_coe_mul] using htx
  have hden : a - x = -(t : ℂ) * d := by rw [htx']; ring
  have hnum : b - x = (1 - (t : ℂ)) * d := by
    rw [htx']
    dsimp [d, b, a]
    ring
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hqx : (b - x) / (a - x) = (((t - 1) / t : ℝ) : ℂ) := by
    rw [hnum, hden]
    push_cast
    field_simp [ht0, hd]
    ring
  have htreal : (t - 1) / t < 0 := div_neg_of_neg_of_pos (by linarith) ht
  dsimp [a, b]
  rw [hqx]
  exact ⟨by simpa using htreal, by simp⟩

/-- Helper toward Proposition 5.16: approaching an interior edge point from
the positive oriented side, the principal edge angle tends to `pi`, using only
nondegeneracy of the edge. -/
theorem tendsto_edgeAngle_nhdsWithin_pos_cyclic (p : Polyline)
    (i : ℕ) (hi : i + 1 < p.points.length) (x : ℂ)
    (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1))
    (hne : p.point i ≠ p.point (i + 1)) :
    Tendsto (fun z : ℂ => p.edgeAngle z i)
      (𝓝[{z | 0 < (conj (p.point (i + 1) - p.point i) * (z - x)).im}] x)
      (𝓝 Real.pi) := by
  let q : ℂ → ℂ := fun z => (p.point (i + 1) - z) / (p.point i - z)
  have hden : p.point i - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxi)
  have hqcont : ContinuousAt q x := by
    dsimp [q]
    exact (continuousAt_const.sub continuousAt_id).div
      (continuousAt_const.sub continuousAt_id) hden
  obtain ⟨hre, him⟩ := edgeQuotient_at_segmentInterior_cyclic
    p i hi x hx hxi hxi1 hne
  have hpos : ∀ᶠ z : ℂ in
      𝓝[{z | 0 < (conj (p.point (i + 1) - p.point i) * (z - x)).im}] x,
      0 < (q z).im := by
    filter_upwards [self_mem_nhdsWithin, eventually_ne_nhdsWithin hxi]
      with z hzside hza
    have hdenz : p.point i - z ≠ 0 := by
      intro h
      exact hza (sub_eq_zero.mp h).symm
    have hN : 0 < ‖p.point i - z‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hdenz)
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
the negative oriented side, the principal edge angle tends to `-pi`, using
only nondegeneracy of the edge. -/
theorem tendsto_edgeAngle_nhdsWithin_neg_cyclic (p : Polyline)
    (i : ℕ) (hi : i + 1 < p.points.length) (x : ℂ)
    (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1))
    (hne : p.point i ≠ p.point (i + 1)) :
    Tendsto (fun z : ℂ => p.edgeAngle z i)
      (𝓝[{z | (conj (p.point (i + 1) - p.point i) * (z - x)).im < 0}] x)
      (𝓝 (-Real.pi)) := by
  let q : ℂ → ℂ := fun z => (p.point (i + 1) - z) / (p.point i - z)
  have hden : p.point i - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxi)
  have hqcont : ContinuousAt q x := by
    dsimp [q]
    exact (continuousAt_const.sub continuousAt_id).div
      (continuousAt_const.sub continuousAt_id) hden
  obtain ⟨hre, him⟩ := edgeQuotient_at_segmentInterior_cyclic
    p i hi x hx hxi hxi1 hne
  have hneg : ∀ᶠ z : ℂ in
      𝓝[{z | (conj (p.point (i + 1) - p.point i) * (z - x)).im < 0}] x,
      (q z).im < 0 := by
    filter_upwards [self_mem_nhdsWithin, eventually_ne_nhdsWithin hxi]
      with z hzside hza
    have hdenz : p.point i - z ≠ 0 := by
      intro h
      exact hza (sub_eq_zero.mp h).symm
    have hN : 0 < ‖p.point i - z‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hdenz)
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

/-- Helper toward Proposition 5.16: one edge angle has a one-sided limit
while all other edge angles are continuous, provided the chain is cyclically
simple. -/
theorem tendsto_angleSum_nhdsWithin_of_edge_cyclic (p : Polyline)
    (hcyclic : p.IsCyclicSimple) (i : ℕ) (hi : i + 1 < p.points.length)
    (x : ℂ) (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
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
          · have hxj := not_mem_segmentAt_of_ne_cyclic p hcyclic i hi x hx hxi hxi1
              j hj hji'
            have hc := continuousAt_edgeAngle_of_not_mem_segmentAt p x j hxj
            simpa [hji'] using hc.tendsto.mono_left nhdsWithin_le_nhds
        simpa only [Finset.sum_insert hji] using hedgej.add (ih ht)
  have htotal := hsum (Finset.range (p.points.length - 1)) (by
    intro j hj
    simp only [Finset.mem_range] at hj
    omega)
  simpa [angleSum] using htotal.div_const (2 * Real.pi)

/-- Helper toward Proposition 5.16: the normalized angle sum has a one-sided
limit from the positive oriented side of an edge in a cyclically simple
polygon. -/
theorem tendsto_angleSum_nhdsWithin_pos_cyclic (p : Polyline)
    (hcyclic : p.IsCyclicSimple) (i : ℕ) (hi : i + 1 < p.points.length)
    (x : ℂ) (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1)) :
    Tendsto (fun z : ℂ => p.angleSum z)
      (𝓝[{z | 0 < (conj (p.point (i + 1) - p.point i) * (z - x)).im}] x)
      (𝓝 ((∑ j ∈ Finset.range (p.points.length - 1),
        if j = i then Real.pi else p.edgeAngle x j) / (2 * Real.pi))) := by
  have hne := hcyclic.2.2.1 i hi
  exact tendsto_angleSum_nhdsWithin_of_edge_cyclic p hcyclic i hi x hx hxi hxi1 _ _
    (tendsto_edgeAngle_nhdsWithin_pos_cyclic p i hi x hx hxi hxi1 hne)

/-- Helper toward Proposition 5.16: the normalized angle sum has a one-sided
limit from the negative oriented side of an edge in a cyclically simple
polygon. -/
theorem tendsto_angleSum_nhdsWithin_neg_cyclic (p : Polyline)
    (hcyclic : p.IsCyclicSimple) (i : ℕ) (hi : i + 1 < p.points.length)
    (x : ℂ) (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1)) :
    Tendsto (fun z : ℂ => p.angleSum z)
      (𝓝[{z | (conj (p.point (i + 1) - p.point i) * (z - x)).im < 0}] x)
      (𝓝 ((∑ j ∈ Finset.range (p.points.length - 1),
        if j = i then -Real.pi else p.edgeAngle x j) / (2 * Real.pi))) := by
  have hne := hcyclic.2.2.1 i hi
  exact tendsto_angleSum_nhdsWithin_of_edge_cyclic p hcyclic i hi x hx hxi hxi1 _ _
    (tendsto_edgeAngle_nhdsWithin_neg_cyclic p i hi x hx hxi hxi1 hne)

/-- Helper toward Proposition 5.16: two integers whose difference is within
one half of one must differ by exactly one. -/
theorem int_sub_eq_one_of_abs_lt_half_cyclic (m n : ℤ)
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
across the interior of an edge in a cyclically simple closed polygon. -/
theorem angleSum_edge_jump_cyclic (p : Polyline) (hcyclic : p.IsCyclicSimple)
    (i : ℕ) (hi : i + 1 < p.points.length) (x : ℂ)
    (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (u v : ℂ), u ∉ p.image → v ∉ p.image →
        dist u x < ε → dist v x < ε →
        ((conj (p.point (i + 1) - p.point i) * (u - x)).im) *
          ((conj (p.point (i + 1) - p.point i) * (v - x)).im) < 0 →
        |p.angleSum u - p.angleSum v| = 1 := by
  have hroot := hcyclic.2.1
  have hclosed : p.start = p.finish := by
    rw [← point_zero_eq_start p, ← point_last_eq_finish p]
    exact hroot
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
  have hpos := tendsto_angleSum_nhdsWithin_pos_cyclic p hcyclic i hi x hx hxi hxi1
  have hneg := tendsto_angleSum_nhdsWithin_neg_cyclic p hcyclic i hi x hx hxi hxi1
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
    have hmn := int_sub_eq_one_of_abs_lt_half_cyclic m n hcast
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
    have hmn := int_sub_eq_one_of_abs_lt_half_cyclic m n hcast
    have hdiff : p.angleSum v - p.angleSum u = 1 := by
      rw [hm, hn, ← Int.cast_sub, hmn]
      norm_num
    rw [show p.angleSum u - p.angleSum v =
      -(p.angleSum v - p.angleSum u) by ring, hdiff]
    norm_num

/-- Helper toward Proposition 5.16: the winding-defined inside set of a
cyclically simple polygon is nonempty. -/
theorem inside_nonempty_cyclic (p : Polyline) (hcyclic : p.IsCyclicSimple) :
    p.inside.Nonempty := by
  let i : ℕ := 0
  let d : ℂ := p.point (i + 1) - p.point i
  let x : ℂ := p.point i + (1 / 2 : ℝ) • d
  have hi : i + 1 < p.points.length := by
    rcases hcyclic with ⟨hlen, _, _, _, _, _⟩
    dsimp [i]
    omega
  have hd : d ≠ 0 := by
    dsimp [d]
    exact sub_ne_zero.mpr (Ne.symm (hcyclic.2.2.1 i hi))
  have hx : x ∈ p.segmentAt i := by
    rw [Polyline.segmentAt, segment_eq_image']
    refine ⟨1 / 2, by norm_num, ?_⟩
    simp [x, d, i]
  have hxi : x ≠ p.point i := by
    intro heq
    have hmul : ((1 / 2 : ℝ) : ℂ) * d = 0 := by
      have hh := congrArg (fun z : ℂ => z - p.point i) heq
      simpa [x, d, i, RCLike.real_smul_eq_coe_mul] using hh
    rcases mul_eq_zero.mp hmul with hzero | hzero
    · norm_num at hzero
    · exact hd hzero
  have hxi1 : x ≠ p.point (i + 1) := by
    intro heq
    have hmul : (((1 / 2 : ℝ) : ℂ) - 1) * d = 0 := by
      have hh := congrArg (fun z : ℂ => z - p.point i) heq
      dsimp [x, d, i] at hh ⊢
      linear_combination hh
    have hcoef : (((1 / 2 : ℝ) : ℂ) - 1) ≠ 0 := by norm_num
    rcases mul_eq_zero.mp hmul with hzero | hzero
    · exact hcoef hzero
    · exact hd hzero
  obtain ⟨ε, hε, hjump⟩ := angleSum_edge_jump_cyclic p hcyclic i hi x hx hxi hxi1
  obtain ⟨r, hr, _, _, _, _, _, _, hdisl, hdisr⟩ :=
    exists_connected_edge_sides_cyclic p hcyclic i hi x hx hxi hxi1
  let ρ := min r ε
  have hρ : 0 < ρ := lt_min hr hε
  have hρr : ρ ≤ r := min_le_left _ _
  have hρε : ρ ≤ ε := min_le_right _ _
  obtain ⟨u, hu⟩ := leftHalfDisc_nonempty x d ρ hd hρ
  obtain ⟨v, hv⟩ := rightHalfDisc_nonempty x d ρ hd hρ
  have hu' : u ∈ leftHalfDisc x d r :=
    ⟨Metric.ball_subset_ball hρr hu.1, hu.2⟩
  have hv' : v ∈ rightHalfDisc x d r :=
    ⟨Metric.ball_subset_ball hρr hv.1, hv.2⟩
  have huNot : u ∉ p.image := fun huim =>
    (Set.disjoint_left.mp hdisl) hu' huim
  have hvNot : v ∉ p.image := fun hvim =>
    (Set.disjoint_left.mp hdisr) hv' hvim
  have hux : dist u x < ε := lt_of_lt_of_le hu.1 hρε
  have hvx : dist v x < ε := lt_of_lt_of_le hv.1 hρε
  have huPos : 0 < (conj (p.point (i + 1) - p.point i) * (u - x)).im := by
    simpa [d, i, Complex.star_def] using hu.2
  have hvNeg : (conj (p.point (i + 1) - p.point i) * (v - x)).im < 0 := by
    simpa [d, i, Complex.star_def] using hv.2
  have hcross :
      ((conj (p.point (i + 1) - p.point i) * (u - x)).im) *
        ((conj (p.point (i + 1) - p.point i) * (v - x)).im) < 0 :=
    mul_neg_of_pos_of_neg huPos hvNeg
  have hjump' := hjump u v huNot hvNot hux hvx hcross
  have hnonzero : p.angleSum u ≠ 0 ∨ p.angleSum v ≠ 0 := by
    by_contra h
    push Not at h
    rw [h.1, h.2] at hjump'
    norm_num at hjump'
  rcases hnonzero with huNZ | hvNZ
  · exact ⟨u, ⟨huNot, huNZ⟩⟩
  · exact ⟨v, ⟨hvNot, hvNZ⟩⟩





































end Polyline
end DirectedDistances.PlanarMap

end
