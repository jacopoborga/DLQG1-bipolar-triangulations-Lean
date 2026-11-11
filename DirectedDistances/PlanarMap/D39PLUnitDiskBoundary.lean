/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlaneStarExtension2

/-! # Radial extensions on the unit disk

Helper toward Proposition 5.16. -/

public section
noncomputable section
namespace DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16: the radial extension preserves the complex norm. -/
@[simp] theorem norm_starConeHomeomorph (h : Circle ≃ₜ Circle) (z : ℂ) :
    ‖starConeHomeomorph h z‖ = ‖z‖ := by
  exact norm_starConeMap h z

/-- Helper toward Proposition 5.16: the radial extension maps the closed unit disk onto itself. -/
theorem starConeHomeomorph_image_closedBall (h : Circle ≃ₜ Circle) :
    starConeHomeomorph h '' Metric.closedBall (0 : ℂ) 1 =
      Metric.closedBall (0 : ℂ) 1 := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_starConeHomeomorph] using hw
  · intro hz
    refine ⟨(starConeHomeomorph h).symm z, ?_, (starConeHomeomorph h).apply_symm_apply z⟩
    have hn : ‖(starConeHomeomorph h).symm (z : ℂ)‖ = ‖(z : ℂ)‖ := by
      change ‖starConeMap h.symm (z : ℂ)‖ = ‖(z : ℂ)‖
      exact norm_starConeMap h.symm z
    simpa only [Metric.mem_closedBall, dist_zero_right, hn] using hz

/-- Helper toward Proposition 5.16: the radial extension maps the open unit disk onto itself. -/
theorem starConeHomeomorph_image_ball (h : Circle ≃ₜ Circle) :
    starConeHomeomorph h '' Metric.ball (0 : ℂ) 1 = Metric.ball (0 : ℂ) 1 := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [Metric.mem_ball, dist_zero_right, norm_starConeHomeomorph] using hw
  · intro hz
    refine ⟨(starConeHomeomorph h).symm z, ?_, (starConeHomeomorph h).apply_symm_apply z⟩
    have hn : ‖(starConeHomeomorph h).symm (z : ℂ)‖ = ‖(z : ℂ)‖ := by
      change ‖starConeMap h.symm (z : ℂ)‖ = ‖(z : ℂ)‖
      exact norm_starConeMap h.symm (z : ℂ)
    simpa only [Metric.mem_ball, dist_zero_right, hn] using hz

/-- Helper toward Proposition 5.16: the radial extension maps the unit circle onto itself. -/
theorem starConeHomeomorph_image_sphere (h : Circle ≃ₜ Circle) :
    starConeHomeomorph h '' Metric.sphere (0 : ℂ) 1 = Metric.sphere (0 : ℂ) 1 := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [Metric.mem_sphere, dist_zero_right, norm_starConeHomeomorph] using hw
  · intro hz
    refine ⟨(starConeHomeomorph h).symm z, ?_, (starConeHomeomorph h).apply_symm_apply z⟩
    have hn : ‖(starConeHomeomorph h).symm (z : ℂ)‖ = ‖(z : ℂ)‖ := by
      change ‖starConeMap h.symm (z : ℂ)‖ = ‖(z : ℂ)‖
      exact norm_starConeMap h.symm (z : ℂ)
    simpa only [Metric.mem_sphere, dist_zero_right, hn] using hz

/-- Helper toward Proposition 5.16: restrict the radial extension to the closed unit disk. -/
@[expose] def starConeClosedBallHomeomorph (h : Circle ≃ₜ Circle) :
    Metric.closedBall (0 : ℂ) 1 ≃ₜ Metric.closedBall (0 : ℂ) 1 where
  toFun z := ⟨starConeHomeomorph h z, by
    have hz : ‖(z : ℂ)‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
    apply Metric.mem_closedBall.mpr
    rw [dist_zero_right, norm_starConeHomeomorph]
    exact hz⟩
  invFun z := ⟨(starConeHomeomorph h).symm z, by
    have hz : ‖(z : ℂ)‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
    have hn : ‖(starConeHomeomorph h).symm (z : ℂ)‖ = ‖(z : ℂ)‖ := by
      change ‖starConeMap h.symm (z : ℂ)‖ = ‖(z : ℂ)‖
      exact norm_starConeMap h.symm (z : ℂ)
    apply Metric.mem_closedBall.mpr
    rw [dist_zero_right, hn]
    exact hz⟩
  left_inv z := Subtype.ext ((starConeHomeomorph h).left_inv z)
  right_inv z := Subtype.ext ((starConeHomeomorph h).right_inv z)
  continuous_toFun := Continuous.subtype_mk
    ((starConeHomeomorph h).continuous.comp continuous_subtype_val) fun z => by
      have hz : ‖(z : ℂ)‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
      apply Metric.mem_closedBall.mpr
      change dist (starConeHomeomorph h (z : ℂ)) 0 ≤ 1
      rw [dist_zero_right, norm_starConeHomeomorph]
      exact hz
  continuous_invFun := Continuous.subtype_mk
    ((starConeHomeomorph h).symm.continuous.comp continuous_subtype_val) fun z => by
      have hz : ‖(z : ℂ)‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
      have hn : ‖(starConeHomeomorph h).symm (z : ℂ)‖ = ‖(z : ℂ)‖ := by
        change ‖starConeMap h.symm (z : ℂ)‖ = ‖(z : ℂ)‖
        exact norm_starConeMap h.symm (z : ℂ)
      apply Metric.mem_closedBall.mpr
      change dist ((starConeHomeomorph h).symm (z : ℂ)) 0 ≤ 1
      rw [dist_zero_right, hn]
      exact hz

/-- Helper toward Proposition 5.16: the restricted map is the ambient radial extension. -/
@[simp] theorem starConeClosedBallHomeomorph_apply_val (h : Circle ≃ₜ Circle)
    (z : Metric.closedBall (0 : ℂ) 1) :
    (starConeClosedBallHomeomorph h z : ℂ) = starConeHomeomorph h (z : ℂ) := rfl

/-- Helper toward Proposition 5.16: the restriction agrees with the circle map on the boundary. -/
theorem starConeClosedBallHomeomorph_apply_circle (h : Circle ≃ₜ Circle)
    (c : Circle) :
    starConeClosedBallHomeomorph h
        ⟨(c : ℂ), by simp only [Metric.mem_closedBall, dist_zero_right, Circle.norm_coe]; norm_num⟩ =
      ⟨(h c : ℂ), by simp only [Metric.mem_closedBall, dist_zero_right, Circle.norm_coe]; norm_num⟩ := by
  apply Subtype.ext
  rw [starConeClosedBallHomeomorph_apply_val]
  calc
    starConeHomeomorph h (c : ℂ) = starConeHomeomorph h ((1 : ℝ) * (c : ℂ)) := by simp
    _ = (1 : ℝ) * (h c : ℂ) := starConeHomeomorph_polar h 1 (by norm_num) c
    _ = (h c : ℂ) := by simp

/-- Helper toward Proposition 5.16: every circle homeomorphism extends to a
homeomorphism of the closed unit disk. -/
theorem exists_closedBall_homeomorph_extending_circle (f : Circle ≃ₜ Circle) :
    ∃ H : Metric.closedBall (0 : ℂ) 1 ≃ₜ Metric.closedBall (0 : ℂ) 1,
      ∀ c : Circle,
        H ⟨(c : ℂ), by simp only [Metric.mem_closedBall, dist_zero_right, Circle.norm_coe]; norm_num⟩ =
          ⟨(f c : ℂ), by simp only [Metric.mem_closedBall, dist_zero_right, Circle.norm_coe]; norm_num⟩ := by
  refine ⟨starConeClosedBallHomeomorph f, ?_⟩
  exact starConeClosedBallHomeomorph_apply_circle f

/-- Helper toward Proposition 5.16: the restricted extension fixes the origin. -/
theorem starConeClosedBallHomeomorph_zero (h : Circle ≃ₜ Circle) :
    starConeClosedBallHomeomorph h ⟨0, by simp only [Metric.mem_closedBall, dist_zero_right]; norm_num⟩ =
      ⟨0, by simp only [Metric.mem_closedBall, dist_zero_right]; norm_num⟩ := by
  apply Subtype.ext
  rw [starConeClosedBallHomeomorph_apply_val]
  exact starConeMap_zero h

/-- Helper toward Proposition 5.16: the restricted extension maps each point on a radius
to the point with the same radius in the image direction. -/
theorem starConeClosedBallHomeomorph_apply_polar (h : Circle ≃ₜ Circle)
    (r ρ : ℝ) (hr : 0 ≤ r) (hrρ : r ≤ ρ) (hρ : ρ ≤ 1) (c : Circle) :
    starConeClosedBallHomeomorph h
        ⟨(r : ℂ) * (c : ℂ), by
          apply Metric.mem_closedBall.mpr
          rw [dist_zero_right, norm_star_polar r hr c]
          exact hrρ.trans hρ⟩ =
      ⟨(r : ℂ) * (h c : ℂ), by
        apply Metric.mem_closedBall.mpr
        rw [dist_zero_right, norm_star_polar r hr (h c)]
        exact hrρ.trans hρ⟩ := by
  apply Subtype.ext
  rw [starConeClosedBallHomeomorph_apply_val]
  exact starConeHomeomorph_polar h r hr c

/-- Helper toward Proposition 5.16: the restricted extension maps each closed radial segment
onto the segment in the image direction. -/
theorem starConeClosedBallHomeomorph_image_radial_segment (h : Circle ≃ₜ Circle)
    (c : Circle) (ρ : ℝ) (_hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    starConeClosedBallHomeomorph h ''
        {z : Metric.closedBall (0 : ℂ) 1 | ∃ r : ℝ, 0 ≤ r ∧ r ≤ ρ ∧
          (z : ℂ) = (r : ℂ) * (c : ℂ)} =
      {z : Metric.closedBall (0 : ℂ) 1 | ∃ r : ℝ, 0 ≤ r ∧ r ≤ ρ ∧
        (z : ℂ) = (r : ℂ) * (h c : ℂ)} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases x with ⟨x, hxmem⟩
    rcases hx with ⟨r, hr, hrρ, hx⟩
    change x = (r : ℂ) * (c : ℂ) at hx
    subst x
    refine ⟨r, hr, hrρ, ?_⟩
    simpa only [starConeClosedBallHomeomorph_apply_val] using
      starConeHomeomorph_polar h r hr c
  · rintro ⟨r, hr, hrρ, hz⟩
    have hz' : z = ⟨(r : ℂ) * (h c : ℂ), by
        apply Metric.mem_closedBall.mpr
        rw [dist_zero_right, norm_star_polar r hr (h c)]
        exact hrρ.trans hρ1⟩ := Subtype.ext hz
    subst z
    refine ⟨⟨(r : ℂ) * (c : ℂ), by
      apply Metric.mem_closedBall.mpr
      rw [dist_zero_right, norm_star_polar r hr c]
      exact hrρ.trans hρ1⟩, ⟨r, hr, hrρ, rfl⟩, ?_⟩
    apply Subtype.ext
    simpa only [starConeClosedBallHomeomorph_apply_val] using
      starConeHomeomorph_polar h r hr c

end DirectedDistances.PlanarMap
