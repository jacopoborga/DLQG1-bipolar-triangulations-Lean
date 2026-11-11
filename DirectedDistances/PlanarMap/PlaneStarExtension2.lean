/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlaneStarExtension

/-! Supporting lemmas for paper labels `def-bs-topology` (see CORRESPONDENCE.md). -/

/-! # Radial extension of circle homeomorphisms

Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16. -/

public section
noncomputable section
namespace DirectedDistances.PlanarMap

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
the angular direction, with the harmless value `1` at zero. -/
@[expose] def starDirection (z : ℂ) : Circle := Circle.exp z.arg

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
polar reconstruction, including the origin. -/
theorem norm_mul_starDirection (z : ℂ) :
    (‖z‖ : ℂ) * (starDirection z : ℂ) = z := by
  exact Complex.norm_mul_exp_arg_mul_I z

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
direction is continuous away from the origin. -/
theorem continuousAt_starDirection {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt starDirection z := by
  exact AddCircle.homeomorphCircle'.continuous.continuousAt.comp
    (Complex.continuousAt_arg_coe_angle hz)

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
nonnegative polar radii give their stated norms. -/
theorem norm_star_polar (r : ℝ) (hr : 0 ≤ r) (c : Circle) :
    ‖(r : ℂ) * (c : ℂ)‖ = r := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
    Circle.norm_coe, mul_one]

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
a positive polar radius determines its direction. -/
theorem starDirection_polar (r : ℝ) (hr : 0 < r) (c : Circle) :
    starDirection ((r : ℂ) * (c : ℂ)) = c := by
  apply Subtype.ext
  apply mul_left_cancel₀ (show (r : ℂ) ≠ 0 by exact_mod_cast hr.ne')
  have hrec := norm_mul_starDirection ((r : ℂ) * (c : ℂ))
  rw [norm_star_polar r hr.le c] at hrec
  exact hrec

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
the cone extension, defined on the entire plane. -/
@[expose] def starConeMap (h : Circle → Circle) (z : ℂ) : ℂ :=
  (‖z‖ : ℂ) * (h (starDirection z) : ℂ)

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
the cone extension fixes the origin. -/
@[simp] theorem starConeMap_zero (h : Circle → Circle) : starConeMap h 0 = 0 := by
  simp only [starConeMap, norm_zero, Complex.ofReal_zero, zero_mul]

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
the cone extension preserves the norm. -/
@[simp] theorem norm_starConeMap (h : Circle → Circle) (z : ℂ) :
    ‖starConeMap h z‖ = ‖z‖ := norm_star_polar _ (norm_nonneg _) _

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
the cone extension acts on every nonnegative polar radius, including zero. -/
theorem starConeMap_polar (h : Circle → Circle) (r : ℝ) (hr : 0 ≤ r) (c : Circle) :
    starConeMap h ((r : ℂ) * (c : ℂ)) = (r : ℂ) * (h c : ℂ) := by
  rcases hr.eq_or_lt with hr | hr
  · subst r
    simp only [Complex.ofReal_zero, zero_mul, starConeMap_zero]
  · rw [starConeMap, norm_star_polar r hr.le c, starDirection_polar r hr c]

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
norm preservation gives continuity at the cone vertex without angular limits. -/
theorem continuousAt_starConeMap_zero (h : Circle → Circle) :
    ContinuousAt (starConeMap h) 0 := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨ε, hε, fun {z} hz => ?_⟩
  simpa only [starConeMap_zero, dist_zero_right, norm_starConeMap] using hz

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
a continuous circle map has a continuous cone extension. -/
theorem continuous_starConeMap (h : Circle → Circle) (hh : Continuous h) :
    Continuous (starConeMap h) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst z
    exact continuousAt_starConeMap_zero h
  · exact (Complex.continuous_ofReal.continuousAt.comp continuous_norm.continuousAt).mul
      (continuous_subtype_val.continuousAt.comp
        (hh.continuousAt.comp (continuousAt_starDirection hz)))

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
the cone extension of an inverse circle map inverts the cone extension. -/
theorem starConeMap_inverse (h : Circle ≃ₜ Circle) (z : ℂ) :
    starConeMap h.symm (starConeMap h z) = z := by
  change starConeMap h.symm ((‖z‖ : ℂ) * (h (starDirection z) : ℂ)) = z
  rw [starConeMap_polar h.symm _ (norm_nonneg _) _,
    h.symm_apply_apply]
  exact norm_mul_starDirection z

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
every circle homeomorphism extends radially to a plane homeomorphism. -/
@[expose] def starConeHomeomorph (h : Circle ≃ₜ Circle) : ℂ ≃ₜ ℂ where
  toFun := starConeMap h
  invFun := starConeMap h.symm
  left_inv := starConeMap_inverse h
  right_inv := starConeMap_inverse h.symm
  continuous_toFun := continuous_starConeMap h h.continuous
  continuous_invFun := continuous_starConeMap h.symm h.symm.continuous

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
the radial homeomorphism realizes its circle map on every nonnegative radius. -/
theorem starConeHomeomorph_polar (h : Circle ≃ₜ Circle) (r : ℝ) (hr : 0 ≤ r)
    (c : Circle) :
    starConeHomeomorph h ((r : ℂ) * (c : ℂ)) = (r : ℂ) * (h c : ℂ) :=
  starConeMap_polar h r hr c

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
the cone extension realizes the specified angular lift on the entire plane. -/
theorem starConeHomeomorph_exp (f : ℝ ≃ₜ ℝ) (h : Circle ≃ₜ Circle)
    (hh : ∀ t : ℝ, h (Circle.exp t) = Circle.exp (f t))
    (r t : ℝ) (hr : 0 ≤ r) :
    starConeHomeomorph h ((r : ℂ) * (Circle.exp t : ℂ)) =
      (r : ℂ) * (Circle.exp (f t) : ℂ) := by
  rw [starConeHomeomorph_polar h r hr, hh]

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
a matched circle direction gives equality of the whole closed rays. -/
theorem starConeHomeomorph_image_ray (h : Circle ≃ₜ Circle) (c : Circle) :
    starConeHomeomorph h '' {z : ℂ | ∃ r : ℝ, 0 ≤ r ∧ z = (r : ℂ) * (c : ℂ)} =
      {z : ℂ | ∃ r : ℝ, 0 ≤ r ∧ z = (r : ℂ) * (h c : ℂ)} := by
  ext z
  constructor
  · rintro ⟨w, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, starConeHomeomorph_polar h r hr c⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨(r : ℂ) * (c : ℂ), ⟨r, hr, rfl⟩, starConeHomeomorph_polar h r hr c⟩

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
a matched circle direction gives equality of all bounded radial segments. -/
theorem starConeHomeomorph_image_radial_segment (h : Circle ≃ₜ Circle)
    (c : Circle) (ρ : ℝ) :
    starConeHomeomorph h ''
        {z : ℂ | ∃ r : ℝ, 0 ≤ r ∧ r ≤ ρ ∧ z = (r : ℂ) * (c : ℂ)} =
      {z : ℂ | ∃ r : ℝ, 0 ≤ r ∧ r ≤ ρ ∧ z = (r : ℂ) * (h c : ℂ)} := by
  ext z
  constructor
  · rintro ⟨w, ⟨r, hr, hrρ, rfl⟩, rfl⟩
    exact ⟨r, hr, hrρ, starConeHomeomorph_polar h r hr c⟩
  · rintro ⟨r, hr, hrρ, rfl⟩
    exact ⟨(r : ℂ) * (c : ℂ), ⟨r, hr, hrρ, rfl⟩, starConeHomeomorph_polar h r hr c⟩

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
the inverse cone map is induced by the inverse angular lift. -/
theorem starConeHomeomorph_symm_exp (f : ℝ ≃ₜ ℝ) (h : Circle ≃ₜ Circle)
    (hh : ∀ t : ℝ, h (Circle.exp t) = Circle.exp (f t))
    (r t : ℝ) (hr : 0 ≤ r) :
    (starConeHomeomorph h).symm ((r : ℂ) * (Circle.exp t : ℂ)) =
      (r : ℂ) * (Circle.exp (f.symm t) : ℂ) := by
  change starConeHomeomorph h.symm _ = _
  apply starConeHomeomorph_exp f.symm h.symm ?_ r t hr
  intro s
  apply h.injective
  rw [h.apply_symm_apply, hh, f.apply_symm_apply]

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
the cone homeomorphism maps actual real affine segments to the corresponding
segments, with the same endpoint radius. -/
theorem starConeHomeomorph_image_segment (h : Circle ≃ₜ Circle) (c : Circle)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    starConeHomeomorph h '' segment ℝ (0 : ℂ) ((ρ : ℂ) * (c : ℂ)) =
      segment ℝ (0 : ℂ) ((ρ : ℂ) * (h c : ℂ)) := by
  rw [segment_eq_image, segment_eq_image, Set.image_image]
  apply Set.image_congr
  intro t ht
  simp only [smul_zero, zero_add, Complex.real_smul]
  rw [← mul_assoc, ← Complex.ofReal_mul,
    starConeHomeomorph_polar h (t * ρ) (mul_nonneg ht.1 hρ),
    Complex.ofReal_mul, mul_assoc]

/-- Helper toward Definition 3.8 (def-bs-topology) / Propositions 5.9, 5.16:
two ordered finite stars admit a norm-preserving ambient homeomorphism,
with a common increasing degree-one lift, matching every ray and every
radial segment. This statement does not assert orientation preservation. -/
theorem exists_plane_star_cone_extension (n : ℕ) (hn : 1 ≤ n)
    (a b : Fin n → ℝ) (ha : StrictMono a) (hb : StrictMono b)
    (ha0 : ∀ j, 0 ≤ a j) (ha2 : ∀ j, a j < 2 * Real.pi)
    (hb0 : ∀ j, 0 ≤ b j) (hb2 : ∀ j, b j < 2 * Real.pi) :
    ∃ (f : ℝ ≃ₜ ℝ) (H : ℂ ≃ₜ ℂ),
      StrictMono f ∧
      (∀ t : ℝ, f (t + 2 * Real.pi) = f t + 2 * Real.pi) ∧
      (∀ j : Fin n, f (a j) = b j) ∧
      H 0 = 0 ∧
      (∀ (r t : ℝ), 0 ≤ r →
        H ((r : ℂ) * (Circle.exp t : ℂ)) =
          (r : ℂ) * (Circle.exp (f t) : ℂ)) ∧
      (∀ z : ℂ, ‖H z‖ = ‖z‖) ∧
      (∀ j : Fin n,
        H '' {z : ℂ | ∃ r : ℝ, 0 ≤ r ∧ z = (r : ℂ) * (Circle.exp (a j) : ℂ)} =
          {z : ℂ | ∃ r : ℝ, 0 ≤ r ∧ z = (r : ℂ) * (Circle.exp (b j) : ℂ)}) ∧
      (∀ (j : Fin n) (ρ : ℝ), 0 ≤ ρ →
        H '' segment ℝ (0 : ℂ) ((ρ : ℂ) * (Circle.exp (a j) : ℂ)) =
          segment ℝ (0 : ℂ) ((ρ : ℂ) * (Circle.exp (b j) : ℂ))) := by
  obtain ⟨f, h, c, d, hf, hper, hh, hj, _⟩ :=
    exists_circle_homeomorph_finite_angles n hn a b ha hb ha0 ha2 hb0 hb2
  refine ⟨f, starConeHomeomorph h, hf, hper, fun j => (hj j).1,
    starConeMap_zero h, starConeHomeomorph_exp f h hh,
    norm_starConeMap h, ?_, ?_⟩
  · intro j
    rw [starConeHomeomorph_image_ray, (hj j).2]
  · intro j ρ hρ
    rw [starConeHomeomorph_image_segment h _ ρ hρ, (hj j).2]




























end DirectedDistances.PlanarMap
