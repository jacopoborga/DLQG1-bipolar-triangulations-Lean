/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39RadialOrder6

/-! # Small-radius transport for three ray germs

Helpers toward Proposition 5.16. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16: continuity at the origin supplies one
positive radius whose closed disk maps inside a prescribed open ball and whose
radius is shorter than each of three nonzero ray segments. -/
theorem d39_small_radius_for_three_germs
    (K : ℂ ≃ₜ ℂ) (hK0 : K 0 = 0)
    (u v w : ℂ) (rU rV rW R : ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hrU : 0 < rU) (hrV : 0 < rV) (hrW : 0 < rW) (hR : 0 < R) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < rU * ‖u‖ ∧ ρ < rV * ‖v‖ ∧
      ρ < rW * ‖w‖ ∧ ∀ z : ℂ, ‖z‖ ≤ ρ → ‖K z‖ < R := by
  have hcont : ContinuousAt K 0 := K.continuous.continuousAt
  obtain ⟨δ, hδ, hδmap⟩ := (Metric.continuousAt_iff.mp hcont) R hR
  let aU := rU * ‖u‖ / 2
  let aV := rV * ‖v‖ / 2
  let aW := rW * ‖w‖ / 2
  let ρ := min (δ / 2) (min aU (min aV aW))
  have huNorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hvNorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hwNorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hρpos : 0 < ρ := by
    dsimp [ρ, aU, aV, aW]
    positivity
  have hρδ : ρ < δ := by
    have hle : ρ ≤ δ / 2 := by
      dsimp [ρ]
      exact min_le_left _ _
    linarith
  have hρUhalf : ρ ≤ rU * ‖u‖ / 2 := by
    dsimp [ρ, aU]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hρVhalf : ρ ≤ rV * ‖v‖ / 2 := by
    dsimp [ρ, aV]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρWhalf : ρ ≤ rW * ‖w‖ / 2 := by
    dsimp [ρ, aW]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ρ, hρpos, ?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt hρUhalf (by nlinarith [mul_pos hrU huNorm])
  · exact lt_of_le_of_lt hρVhalf (by nlinarith [mul_pos hrV hvNorm])
  · exact lt_of_le_of_lt hρWhalf (by nlinarith [mul_pos hrW hwNorm])
  · intro z hz
    have hzδ : dist z 0 < δ := by
      rw [dist_eq_norm]
      simpa using lt_of_le_of_lt hz hρδ
    have hmap := hδmap hzδ
    simpa [dist_eq_norm, hK0] using hmap

/-- Helper toward Proposition 5.16: if a centered circle has radius strictly
between zero and the endpoint radius of a nonzero ray segment, it meets that
segment at exactly one parameter value. -/
theorem d39_circle_meets_radial_segment_once
    {u : ℂ} {r ρ : ℝ} (hu : u ≠ 0)
    (hρ : 0 < ρ) (hρr : ρ < r * ‖u‖) :
    ∃! t : ℝ, 0 ≤ t ∧ t ≤ r ∧ ‖(t : ℂ) * u‖ = ρ := by
  have huNorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have htr : ρ / ‖u‖ < r := (div_lt_iff₀ huNorm).2 (by nlinarith [hρr])
  have hnorm_mul (t : ℝ) (ht : 0 ≤ t) : ‖(t : ℂ) * u‖ = t * ‖u‖ := by
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  refine ⟨ρ / ‖u‖, ⟨le_of_lt (div_pos hρ huNorm), htr.le, ?_⟩, ?_⟩
  · rw [hnorm_mul _ (le_of_lt (div_pos hρ huNorm))]
    field_simp [ne_of_gt huNorm]
  · intro t ht
    rcases ht with ⟨ht0, htR, hnorm⟩
    have hmul : t * ‖u‖ = ρ := by
      calc
        t * ‖u‖ = ‖(t : ℂ) * u‖ := (hnorm_mul t ht0).symm
        _ = ρ := hnorm
    calc
      t = (t * ‖u‖) / ‖u‖ := by field_simp [ne_of_gt huNorm]
      _ = ρ / ‖u‖ := by rw [hmul]

/-- Helper toward Proposition 5.16: orientation preservation transports the
winding integer of any loop avoiding the origin to its image loop about the
image of the origin. -/
theorem d39_orientationPreserving_transports_winding_at_origin
    {K : ℂ ≃ₜ ℂ} (hK : OrientationPreserving K)
    {z : ℂ} (L : Path z z) (havoid : 0 ∉ Set.range L) (n : ℤ) :
    HasWinding L 0 n ↔ HasWinding (L.map K.continuous) (K 0) n :=
  hK L 0 havoid n

/-- Helper toward Proposition 5.16: the positively traversed centered circle
of radius `ρ`, based at the positive real point `ρ`. -/
def d39CenteredCirclePath (ρ : ℝ) : Path (ρ : ℂ) (ρ : ℂ) where
  toFun t := (ρ : ℂ) * Complex.exp
    (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)
  source' := by simp
  target' := by simp [Complex.exp_two_pi_mul_I]
  continuous_toFun := by continuity

/-- Helper toward Proposition 5.16: the centered circle has winding one about
the origin, witnessed by the logarithmic lift with angular increment `2π`. -/
theorem d39_centeredCirclePath_hasWinding_one {ρ : ℝ} (hρ : 0 < ρ) :
    HasWinding (d39CenteredCirclePath ρ) 0 1 := by
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hρ)
  let φ : C(unitInterval, ℂ) := ⟨fun t =>
    Complex.log (ρ : ℂ) +
      (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I), by continuity⟩
  refine ⟨φ, ?_, ?_⟩
  · intro t
    simp [φ, d39CenteredCirclePath, Complex.exp_add, Complex.exp_log hρC]
  · simp [φ]

/-- Helper toward Proposition 5.16: an orientation-preserving homeomorphism
maps the centered circle to a loop of winding one about the image of the
origin. -/
theorem d39_oriented_image_centeredCircle_hasWinding_one
    {K : ℂ ≃ₜ ℂ} (hK : OrientationPreserving K) {ρ : ℝ} (hρ : 0 < ρ) :
    HasWinding ((d39CenteredCirclePath ρ).map K.continuous) (K 0) 1 := by
  have havoid : 0 ∉ Set.range (d39CenteredCirclePath ρ) := by
    rintro ⟨t, ht⟩
    have hnorm : ‖d39CenteredCirclePath ρ t‖ = ρ := by
      change ‖(ρ : ℂ) * Complex.exp
        (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)‖ = ρ
      rw [Complex.norm_mul, Complex.norm_exp_ofReal_mul_I,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
      simp
    have : ρ = 0 := by simpa [ht] using hnorm.symm
    exact (ne_of_gt hρ) this
  exact (d39_orientationPreserving_transports_winding_at_origin hK
    (d39CenteredCirclePath ρ) havoid 1).mp
      (d39_centeredCirclePath_hasWinding_one hρ)

/-- Helper toward Proposition 5.16: equality of the images of two bounded ray
segments gives each source point a unique parameter on the target ray segment. -/
theorem d39_image_germ_segment_has_unique_target_parameter
    (K : ℂ ≃ₜ ℂ) (u u' : ℂ) (r s : ℝ)
    (hu' : u' ≠ 0)
    (himage : K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧
        z = (t : ℂ) * u} =
      {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * u'}) :
    ∀ t : ℝ, 0 ≤ t → t ≤ r →
      ∃! t' : ℝ, 0 ≤ t' ∧ t' ≤ s ∧
        K ((t : ℂ) * u) = (t' : ℂ) * u' := by
  intro t ht0 htR
  have hmem : K ((t : ℂ) * u) ∈
      K '' {z : ℂ | ∃ x : ℝ, 0 ≤ x ∧ x ≤ r ∧ z = (x : ℂ) * u} :=
    ⟨(t : ℂ) * u, ⟨t, ht0, htR, rfl⟩, rfl⟩
  rw [himage] at hmem
  rcases hmem with ⟨t', ht'0, ht's, heq⟩
  refine ⟨t', ⟨ht'0, ht's, heq⟩, ?_⟩
  intro t'' ht''
  rcases ht'' with ⟨ht''0, ht''s, heq'⟩
  have hparams : (t' : ℂ) * u' = (t'' : ℂ) * u' := heq.symm.trans heq'
  have hparams' : (t' : ℂ) = (t'' : ℂ) := mul_right_cancel₀ hu' hparams
  exact_mod_cast hparams'.symm

/-- Helper toward Proposition 5.16: the image of a centered circle meets the
image of a nonzero bounded ray germ segment at exactly one point. -/
theorem d39_image_circle_meets_image_germ_once
    (K : ℂ ≃ₜ ℂ) (u u' : ℂ) (r s ρ : ℝ)
    (hu : u ≠ 0) (hρ : 0 < ρ) (hρr : ρ < r * ‖u‖)
    (himage : K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧
        z = (t : ℂ) * u} =
      {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * u'}) :
    ∃! y : ℂ, y ∈ K '' {z : ℂ | ‖z‖ = ρ} ∧
      y ∈ {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * u'} := by
  have huNorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have ht0 : 0 < ρ / ‖u‖ := div_pos hρ huNorm
  have htr : ρ / ‖u‖ < r := (div_lt_iff₀ huNorm).2 (by nlinarith [hρr])
  have hnorm (t : ℝ) (ht : 0 ≤ t) : ‖(t : ℂ) * u‖ = t * ‖u‖ := by
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  let x : ℂ := ((ρ / ‖u‖ : ℝ) : ℂ) * u
  let y : ℂ := K x
  have hxseg : x ∈ {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * u} := by
    refine ⟨ρ / ‖u‖, ht0.le, htr.le, rfl⟩
  have hxcircle : ‖x‖ = ρ := by
    dsimp [x]
    rw [hnorm _ ht0.le]
    field_simp [ne_of_gt huNorm]
  have hyseg : y ∈ {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * u'} := by
    rw [← himage]
    exact ⟨x, hxseg, rfl⟩
  refine ⟨y, ⟨⟨x, hxcircle, rfl⟩, hyseg⟩, ?_⟩
  intro y' hy'
  rcases hy' with ⟨⟨x', hx'circle, hKx'⟩, hy'seg⟩
  rw [← himage] at hy'seg
  rcases hy'seg with ⟨x'', hx''seg, hKx''⟩
  have hxx' : x' = x'' := K.injective (hKx'.trans hKx''.symm)
  have hx'seg : x' ∈ {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧
      z = (t : ℂ) * u} := by
    rw [hxx']
    exact hx''seg
  rcases hx'seg with ⟨t, ht, htR, rfl⟩
  have htCircle : ‖(t : ℂ) * u‖ = ρ := by
    change ‖(t : ℂ) * u‖ = ρ at hx'circle
    exact hx'circle
  obtain ⟨_, _, hunique⟩ :=
    d39_circle_meets_radial_segment_once hu hρ hρr
  have htEq : t = ρ / ‖u‖ := by
    have hleft := hunique t ⟨ht, htR, htCircle⟩
    have hright := hunique (ρ / ‖u‖)
      ⟨le_of_lt ht0, htr.le, by simpa [x] using hxcircle⟩
    exact hleft.trans hright.symm
  calc
    y' = K ((t : ℂ) * u) := hKx'.symm
    _ = y := by simp [y, x, htEq]



















































end DirectedDistances.PlanarMap

end
