/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PolygonWinding4

/-! # Vanishing of polygonal angle sums at infinity

Helpers toward Proposition 5.16. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap
namespace Polyline

open Filter Topology

/-- Helper toward Proposition 5.16: for fixed complex points `a` and `b`,
the quotient of their rays from `z` tends to one as `z` tends to infinity. -/
theorem tendsto_sub_div_sub_cocompact (a b : ℂ) :
    Tendsto (fun z : ℂ => (a - z) / (b - z)) (cocompact ℂ) (nhds 1) := by
  have hden : Tendsto (fun z : ℂ => ‖b - z‖) (cocompact ℂ) atTop := by
    simpa only [dist_eq_norm, norm_sub_rev] using
      tendsto_dist_right_cocompact_atTop b
  have htermNorm : Tendsto (fun z : ℂ => ‖(a - b) / (b - z)‖)
      (cocompact ℂ) (nhds 0) := by
    simpa only [norm_div] using
      (Filter.Tendsto.const_div_atTop hden ‖a - b‖)
  have hterm : Tendsto (fun z : ℂ => (a - b) / (b - z))
      (cocompact ℂ) (nhds (0 : ℂ)) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr htermNorm
  have hplus : Tendsto (fun z : ℂ => (1 : ℂ) + (a - b) / (b - z))
      (cocompact ℂ) (nhds 1) := by
    simpa using tendsto_const_nhds.add hterm
  have hb : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ b := by
    have hbset : ({b} : Set ℂ)ᶜ ∈ cocompact ℂ :=
      isCompact_singleton.compl_mem_cocompact
    filter_upwards [hbset] with z hz
    simpa using hz
  have heq : (fun z : ℂ => (a - z) / (b - z)) =ᶠ[cocompact ℂ]
      fun z => (1 : ℂ) + (a - b) / (b - z) := by
    filter_upwards [hb] with z hz
    have hne : b - z ≠ 0 := sub_ne_zero.mpr hz.symm
    field_simp [hne]
    ring
  exact Tendsto.congr' heq.symm hplus

/-- Helper toward Proposition 5.16: every polygonal edge angle tends to zero
as the viewpoint tends to infinity. -/
theorem tendsto_edgeAngle_cocompact (p : Polyline) (i : ℕ) :
    Tendsto (fun z : ℂ => p.edgeAngle z i) (cocompact ℂ) (nhds 0) := by
  have hslit : (1 : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff_arg]
    simp only [Complex.arg_one]
    exact ⟨Ne.symm Real.pi_ne_zero, by norm_num⟩
  have harg : Tendsto (fun z : ℂ => Complex.arg
      ((p.point (i + 1) - z) / (p.point i - z))) (cocompact ℂ) (nhds 0) := by
    have hcomp := (Complex.continuousAt_arg hslit).tendsto.comp
      (tendsto_sub_div_sub_cocompact (p.point (i + 1)) (p.point i))
    convert hcomp using 1
    · ext z
      rfl
    · simp [Complex.arg_one]
  simpa [edgeAngle] using harg

/-- Helper toward Proposition 5.16: the normalized sum of polygonal edge
angles tends to zero as the viewpoint tends to infinity. -/
theorem tendsto_angleSum_cocompact (p : Polyline) :
    Tendsto (fun z : ℂ => p.angleSum z) (cocompact ℂ) (nhds 0) := by
  have hsum (s : Finset ℕ) : Tendsto
      (fun z : ℂ => ∑ i ∈ s, p.edgeAngle z i) (cocompact ℂ) (nhds 0) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
        simpa [Finset.sum_insert, his] using
          (tendsto_edgeAngle_cocompact p i).add ih
  have htotal := hsum (Finset.range (p.points.length - 1))
  simpa [angleSum] using htotal.div_const (2 * Real.pi)

/-- Helper toward Proposition 5.16: a closed polyline's normalized
principal-angle sum vanishes outside a sufficiently large disk. -/
theorem exists_radius_angleSum_eq_zero (p : Polyline)
    (hclosed : p.start = p.finish) :
    ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → p.angleSum z = 0 := by
  have hsum := tendsto_angleSum_cocompact p
  have hsmall : ∀ᶠ z : ℂ in cocompact ℂ, |p.angleSum z| < (1 / 2 : ℝ) := by
    have hball : Metric.ball (0 : ℝ) (1 / 2) ∈ nhds (0 : ℝ) :=
      Metric.ball_mem_nhds _ (by norm_num)
    filter_upwards [hsum.eventually hball] with z hz
    simpa [Metric.mem_ball, Real.norm_eq_abs] using hz
  have havoid : ∀ᶠ z : ℂ in cocompact ℂ, z ∉ p.image :=
    p.isCompact_image.compl_mem_cocompact
  have hzero : ∀ᶠ z : ℂ in cocompact ℂ, p.angleSum z = 0 := by
    filter_upwards [havoid, hsmall] with z hz hsmall
    obtain ⟨n, hn⟩ := angleSum_isInt p hclosed z hz
    have hsmall' : |(n : ℝ)| < (1 / 2 : ℝ) := by simpa [hn] using hsmall
    have hnloR : (-1 : ℝ) < (n : ℝ) := by
      have h := (abs_lt.mp hsmall').1
      linarith
    have hnhiR : (n : ℝ) < (1 : ℝ) := by
      have h := (abs_lt.mp hsmall').2
      linarith
    have hnlo : (-1 : ℤ) < n := by exact_mod_cast hnloR
    have hnhi : n < (1 : ℤ) := by exact_mod_cast hnhiR
    have hn0 : n = 0 := by omega
    rw [hn, hn0]
    norm_num
  have hzeroSet : {z : ℂ | p.angleSum z = 0} ∈ cocompact ℂ := hzero
  rw [← Metric.cobounded_eq_cocompact] at hzeroSet
  obtain ⟨R, -, hR⟩ :=
    (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).mem_iff.mp hzeroSet
  refine ⟨R, ?_⟩
  intro z hz
  apply hR
  have hz' : z ∉ Metric.closedBall (0 : ℂ) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using not_le_of_gt hz
  exact hz'















end Polyline
end DirectedDistances.PlanarMap

end
