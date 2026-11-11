/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PolygonWinding3
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Edge jumps of polygonal winding sums

Helpers toward Proposition 5.16. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap
namespace Polyline

open Filter Topology

/-- Helper toward Proposition 5.16: an interior point of a segment of a
simple polyline lies on no other segment. Adjacent segments meet only at their
shared endpoint, while nonadjacent segments are disjoint. -/
theorem not_mem_segmentAt_of_ne (p : Polyline) (hsimple : p.IsSimple)
    (i : ℕ) (hi : i + 1 < p.points.length) (x : ℂ)
    (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1))
    (j : ℕ) (hj : j + 1 < p.points.length) (hji : j ≠ i) :
    x ∉ p.segmentAt j := by
  rcases hsimple with ⟨hne, hadj, hdisj⟩
  intro hxj
  rcases lt_or_gt_of_ne hji with hji' | hij
  · by_cases hnext : j + 1 = i
    · have hlen : j + 2 < p.points.length := by omega
      have hinter := hadj j hlen
      have hmem : x ∈ ({p.point (j + 1)} : Set ℂ) := by
        rw [← hinter]
        exact ⟨hxj, by simpa [hnext] using hx⟩
      have heq : x = p.point i := by simpa [hnext] using hmem
      exact hxi heq
    · have hfar : j + 1 < i := by omega
      exact (Set.disjoint_left.mp (hdisj j i hj hi hfar)) hxj hx
  · by_cases hnext : i + 1 = j
    · have hlen : i + 2 < p.points.length := by omega
      have hinter := hadj i hlen
      have hmem : x ∈ ({p.point (i + 1)} : Set ℂ) := by
        rw [← hinter]
        exact ⟨hx, by simpa [hnext] using hxj⟩
      have heq : x = p.point (i + 1) := by simpa using hmem
      exact hxi1 heq
    · have hfar : i + 1 < j := by omega
      exact (Set.disjoint_left.mp (hdisj i j hi hj hfar)) hx hxj

/-- Helper toward Proposition 5.16: a positive-radius neighborhood of an
interior point of a simple edge misses every other segment of the polyline. -/
theorem exists_pos_ball_avoiding_nonincident_segments (p : Polyline)
    (hsimple : p.IsSimple) (i : ℕ) (hi : i + 1 < p.points.length)
    (x : ℂ) (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : ℂ, dist y x < ε →
      ∀ j, j + 1 < p.points.length → j ≠ i → y ∉ p.segmentAt j := by
  classical
  let s := (Finset.range (p.points.length - 1)).filter (fun j => j ≠ i)
  have hsegcompact (j : ℕ) : IsCompact (p.segmentAt j) := by
    have hcont : Continuous (fun t : ℝ =>
        p.point j + t • (p.point (j + 1) - p.point j)) := by fun_prop
    rw [Polyline.segmentAt, segment_eq_image']
    exact isCompact_Icc.image hcont
  have hclosed : IsClosed (⋃ j ∈ s, p.segmentAt j) :=
    isClosed_biUnion_finset (fun j _ => (hsegcompact j).isClosed)
  have hxout : x ∉ ⋃ j ∈ s, p.segmentAt j := by
    intro hxU
    rw [Set.mem_iUnion₂] at hxU
    obtain ⟨j, hjs, hxj⟩ := hxU
    have hjs' := Finset.mem_filter.mp hjs
    have hj : j + 1 < p.points.length := by
      simp only [Finset.mem_range] at hjs'
      omega
    exact not_mem_segmentAt_of_ne p hsimple i hi x hx hxi hxi1 j hj hjs'.2 hxj
  have hev : ∀ᶠ y : ℂ in 𝓝 x, y ∉ ⋃ j ∈ s, p.segmentAt j :=
    hclosed.isOpen_compl.mem_nhds hxout
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε, hε, ?_⟩
  intro y hy j hj hji hyj
  apply hball hy
  rw [Set.mem_iUnion₂]
  exact ⟨j, Finset.mem_filter.mpr ⟨by simp only [Finset.mem_range]; omega, hji⟩, hyj⟩

/-- Helper toward Proposition 5.16: the endpoint exclusions for a point on a
segment give its unique affine parameter strictly between zero and one. -/
theorem exists_parameter_Ioo_of_mem_segmentAt (p : Polyline) (i : ℕ)
    (x : ℂ) (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1)) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      x = p.point i + t • (p.point (i + 1) - p.point i) := by
  rw [Polyline.segmentAt, segment_eq_image'] at hx
  obtain ⟨t, ht, htx⟩ := hx
  simp only [Set.mem_Icc] at ht
  refine ⟨t, ?_, ?_, htx.symm⟩
  · by_contra hnot
    have ht0 : t = 0 := le_antisymm (not_lt.mp hnot) ht.1
    have heq : x = p.point i := by
      calc
        x = p.point i + t • (p.point (i + 1) - p.point i) := htx.symm
        _ = p.point i := by simp [ht0]
    exact hxi heq
  · by_contra hnot
    have ht1 : t = 1 := le_antisymm ht.2 (not_lt.mp hnot)
    have heq : x = p.point (i + 1) := by
      calc
        x = p.point i + t • (p.point (i + 1) - p.point i) := htx.symm
        _ = p.point (i + 1) := by simp [ht1]
    exact hxi1 heq

/-- Helper toward Proposition 5.16: at an interior point of a nondegenerate
edge, its edge quotient is a negative real number. -/
theorem edgeQuotient_at_segmentInterior (p : Polyline) (hsimple : p.IsSimple)
    (i : ℕ) (hi : i + 1 < p.points.length) (x : ℂ)
    (hx : x ∈ p.segmentAt i) (hxi : x ≠ p.point i)
    (hxi1 : x ≠ p.point (i + 1)) :
    let q : ℂ := (p.point (i + 1) - x) / (p.point i - x)
    q.re < 0 ∧ q.im = 0 := by
  obtain ⟨t, ht, ht1, htx⟩ :=
    exists_parameter_Ioo_of_mem_segmentAt p i x hx hxi hxi1
  let a := p.point i
  let b := p.point (i + 1)
  let d : ℂ := b - a
  have hd : d ≠ 0 := by
    dsimp [d, a, b]
    exact sub_ne_zero.mpr (Ne.symm (hsimple.1 i hi))
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

/-- Helper toward Proposition 5.16: the edge quotient argument is strictly
between `-pi` and `pi` whenever the observation point avoids that edge. -/
theorem edgeArgument_mem_Ioo_of_not_mem_segmentAt (p : Polyline) (z : ℂ)
    (i : ℕ) (hz : z ∉ p.segmentAt i) :
    Complex.arg ((p.point (i + 1) - z) / (p.point i - z)) ∈
      Set.Ioo (-Real.pi) Real.pi := by
  have hpa : p.point i - z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    exact hz (h ▸ left_mem_segment ℝ (p.point i) (p.point (i + 1)))
  let q : ℂ := (p.point (i + 1) - z) / (p.point i - z)
  have hupper : Complex.arg q < Real.pi := by
    apply Complex.arg_lt_pi_iff.mpr
    by_contra h
    have hparts := not_or.mp h
    have hqre : q.re < 0 := lt_of_not_ge hparts.1
    have hqim : q.im = 0 := by simpa using hparts.2
    have hqreal : q = (q.re : ℂ) := Complex.ext (by simp) hqim
    have hmul : p.point (i + 1) - z = (q.re : ℂ) * (p.point i - z) := by
      have hdiv : (p.point (i + 1) - z) / (p.point i - z) = (q.re : ℂ) := by
        simpa [q] using hqreal
      calc
        p.point (i + 1) - z =
            ((p.point (i + 1) - z) / (p.point i - z)) * (p.point i - z) := by
          field_simp [hpa]
        _ = (q.re : ℂ) * (p.point i - z) := by rw [hdiv]
    have hsame : SameRay ℝ (z - p.point i) (p.point (i + 1) - z) := by
      rw [show z - p.point i = -(p.point i - z) by ring]
      rw [show p.point (i + 1) - z = (q.re : ℝ) • (p.point i - z) by
        rw [RCLike.real_smul_eq_coe_mul]
        exact hmul]
      exact (sameRay_neg_smul_right_iff (R := ℝ)).2 (Or.inl hqre.le)
    have hzseg : z ∈ p.segmentAt i := by
      change z ∈ segment ℝ (p.point i) (p.point (i + 1))
      exact (mem_segment_iff_sameRay (𝕜 := ℝ)).2 hsame
    exact hz hzseg
  have hlower : -Real.pi < Complex.arg q := Complex.neg_pi_lt_arg q
  change Complex.arg q ∈ Set.Ioo (-Real.pi) Real.pi
  exact ⟨hlower, hupper⟩

/-- Helper toward Proposition 5.16: the principal edge angle is continuous at
every point outside its own edge. -/
theorem continuousAt_edgeAngle_of_not_mem_segmentAt (p : Polyline) (z : ℂ)
    (i : ℕ) (hz : z ∉ p.segmentAt i) :
    ContinuousAt (fun w : ℂ => p.edgeAngle w i) z := by
  let q : ℂ := (p.point (i + 1) - z) / (p.point i - z)
  have hq : q ≠ 0 := by
    dsimp [q]
    apply div_ne_zero
    · apply sub_ne_zero.mpr
      intro h
      have hp : p.point (i + 1) ∈ p.segmentAt i := right_mem_segment ℝ _ _
      exact hz (h ▸ hp)
    · apply sub_ne_zero.mpr
      intro h
      have hp : p.point i ∈ p.segmentAt i := left_mem_segment ℝ _ _
      exact hz (h ▸ hp)
  have harg := edgeArgument_mem_Ioo_of_not_mem_segmentAt p z i hz
  have hslit : q ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff_arg.mpr ⟨ne_of_lt harg.2, hq⟩
  have hnum : ContinuousAt (fun w : ℂ => p.point (i + 1) - w) z :=
    continuousAt_const.sub continuousAt_id
  have hden : ContinuousAt (fun w : ℂ => p.point i - w) z :=
    continuousAt_const.sub continuousAt_id
  have hden0 : p.point i - z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    exact hz (h ▸ left_mem_segment ℝ _ _)
  have hquot : ContinuousAt
      (fun w : ℂ => (p.point (i + 1) - w) / (p.point i - w)) z :=
    hnum.div hden hden0
  have hcont : ContinuousAt
      (Complex.arg ∘ fun w : ℂ => (p.point (i + 1) - w) / (p.point i - w)) z :=
    ContinuousAt.comp (f := fun w : ℂ => (p.point (i + 1) - w) / (p.point i - w))
      (x := z) (g := Complex.arg) (Complex.continuousAt_arg hslit) hquot
  change ContinuousAt (fun w : ℂ =>
    Complex.arg ((p.point (i + 1) - w) / (p.point i - w))) z
  convert hcont using 1
  ext w
  rfl

/-- Helper toward Proposition 5.16: composing a continuous edge quotient
whose imaginary part is eventually positive with the principal argument gives
the positive-side limit `pi` at a negative real value. -/
theorem tendsto_arg_nhdsWithin_im_pos_of_continuousAt
    (q : ℂ → ℂ) (x : ℂ)
    (hq : ContinuousAt q x) (hre : (q x).re < 0) (him : (q x).im = 0)
    (hpos : ∀ᶠ z : ℂ in 𝓝[{z | 0 < z.im}] x, 0 < (q z).im) :
    Tendsto (fun z => Complex.arg (q z))
      (𝓝[{z | 0 < z.im}] x) (𝓝 Real.pi) := by
  have hq' : Tendsto q (𝓝[{z | 0 < z.im}] x)
      (𝓝[{w | 0 ≤ w.im}] (q x)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hq.tendsto.mono_left nhdsWithin_le_nhds,
      hpos.mono fun z hz => le_of_lt hz⟩
  exact (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hre him).comp hq'

/-- Helper toward Proposition 5.16: composing a continuous edge quotient
whose imaginary part is eventually negative with the principal argument gives
the negative-side limit `-pi` at a negative real value. -/
theorem tendsto_arg_nhdsWithin_im_neg_of_continuousAt
    (q : ℂ → ℂ) (x : ℂ)
    (hq : ContinuousAt q x) (hre : (q x).re < 0) (him : (q x).im = 0)
    (hneg : ∀ᶠ z : ℂ in 𝓝[{z | z.im < 0}] x, (q z).im < 0) :
    Tendsto (fun z => Complex.arg (q z))
      (𝓝[{z | z.im < 0}] x) (𝓝 (-Real.pi)) := by
  have hq' : Tendsto q (𝓝[{z | z.im < 0}] x)
      (𝓝[{w | w.im < 0}] (q x)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hq.tendsto.mono_left nhdsWithin_le_nhds,
      hneg.mono fun z hz => hz⟩
  exact (Complex.tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him).comp hq'













































end Polyline
end DirectedDistances.PlanarMap

end
