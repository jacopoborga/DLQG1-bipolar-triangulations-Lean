/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39RadialOrder8

/-! # Rotated circle helpers toward Proposition 5.16 -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16: the circle of radius `ρ`, traversed once
counterclockwise from angle `α`. -/
@[expose] def d39RotatedCirclePath (ρ α : ℝ) : Path
    ((ρ : ℂ) * Complex.exp ((α : ℂ) * Complex.I))
    ((ρ : ℂ) * Complex.exp ((α : ℂ) * Complex.I)) where
  toFun t := (ρ : ℂ) * Complex.exp
    ((((α + 2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I))
  source' := by
    apply congrArg (fun z : ℂ => (ρ : ℂ) * z)
    simp
  target' := by
    apply congrArg (fun z : ℂ => (ρ : ℂ) * z)
    have hone : ((1 : unitInterval) : ℝ) = 1 := rfl
    have hangle : (((α + 2 * Real.pi * ((1 : unitInterval) : ℝ) : ℝ) : ℂ) * Complex.I) =
        (α : ℂ) * Complex.I + (2 * Real.pi : ℂ) * Complex.I := by
      rw [hone]
      push_cast
      ring
    rw [hangle, Complex.exp_add]
    simp [Complex.exp_two_pi_mul_I]
  continuous_toFun := by continuity

/-- Helper toward Proposition 5.16: every point of the rotated circle has
distance `ρ` from the origin when `ρ` is positive. -/
theorem d39_rotatedCirclePath_norm {ρ α : ℝ} (hρ : 0 < ρ)
    (t : unitInterval) : ‖d39RotatedCirclePath ρ α t‖ = ρ := by
  change ‖(ρ : ℂ) * Complex.exp
    ((((α + 2 * Real.pi * (t : ℝ) : ℝ) : ℝ) : ℂ) * Complex.I)‖ = ρ
  rw [Complex.norm_mul, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  simp

/-- Helper toward Proposition 5.16: the exposed rotated circle has winding
number one about the origin, witnessed by its linear angular lift. -/
theorem d39_rotatedCirclePath_hasWinding_one {ρ α : ℝ} (hρ : 0 < ρ) :
    HasWinding (d39RotatedCirclePath ρ α) 0 1 := by
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hρ)
  let φ : C(unitInterval, ℂ) := ⟨fun t =>
    Complex.log (ρ : ℂ) +
      (((α + 2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I), by continuity⟩
  refine ⟨φ, ?_, ?_⟩
  · intro t
    simp [φ, d39RotatedCirclePath, Complex.exp_add, Complex.exp_log hρC]
  · dsimp [φ]
    simp
    ring

/-- Helper toward Proposition 5.16: the unique parameter in one open turn
at which the rotated circle has direction `a` is the fractional part of the
normalized angular difference. -/
def d39RotatedCircleRayHitTime (α : ℝ) (a : ℂ) : ℝ :=
  Int.fract ((a.arg - α) / (2 * Real.pi))

/-- Helper toward Proposition 5.16: if `α` is not congruent to the argument
of a nonzero ray modulo `2π`, its fractional-part hit time is strictly
between zero and one. -/
theorem d39_rotatedCircleRayHitTime_mem_Ioo (α : ℝ) (a : ℂ) (_ha : a ≠ 0)
    (hmiss : ∀ k : ℤ, a.arg ≠ α + 2 * Real.pi * (k : ℝ)) :
    d39RotatedCircleRayHitTime α a ∈ Set.Ioo 0 1 := by
  let x := (a.arg - α) / (2 * Real.pi)
  have hnonneg : 0 ≤ Int.fract x := Int.fract_nonneg x
  have hlt : Int.fract x < 1 := Int.fract_lt_one x
  have hpos : 0 < Int.fract x := by
    by_contra hnot
    have hz : Int.fract x = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
    have hx : x = (⌊x⌋ : ℝ) := by
      change x - (⌊x⌋ : ℝ) = 0 at hz
      linarith
    have hmul : 2 * Real.pi * x = a.arg - α := by
      dsimp [x]
      field_simp
    have hangle : a.arg = α + 2 * Real.pi * (⌊x⌋ : ℝ) := by
      calc
        a.arg = α + (a.arg - α) := by ring
        _ = α + 2 * Real.pi * x := by rw [← hmul]
        _ = α + 2 * Real.pi * (⌊x⌋ : ℝ) :=
          congrArg (fun y : ℝ => α + 2 * Real.pi * y) hx
    exact hmiss ⌊x⌋ hangle
  change 0 < Int.fract x ∧ Int.fract x < 1
  exact ⟨hpos, hlt⟩

/-- Helper toward Proposition 5.16: when a lifted argument lies in the turn
from `α` to `α + 2π`, its normalized position is the fractional-part hit
time. -/
theorem d39_rotatedCircleRayHitTime_eq_of_lift
    (α : ℝ) (a : ℂ) (k : ℤ)
    (hlower : α < a.arg + 2 * Real.pi * (k : ℝ))
    (hupper : a.arg + 2 * Real.pi * (k : ℝ) < α + 2 * Real.pi) :
    d39RotatedCircleRayHitTime α a =
      (a.arg + 2 * Real.pi * (k : ℝ) - α) / (2 * Real.pi) := by
  let x := (a.arg - α) / (2 * Real.pi)
  have hperiod : 0 < 2 * Real.pi := by positivity
  have hneg : 2 * Real.pi * (k : ℝ) =
      -(2 * Real.pi * ((-k : ℤ) : ℝ)) := by push_cast; ring
  have hshift : (((-k : ℤ) : ℝ) + 1) * (2 * Real.pi) =
      2 * Real.pi * (1 - (k : ℝ)) := by push_cast; ring
  have hlo : ((-k : ℤ) : ℝ) ≤ x := by
    apply (le_div_iff₀ hperiod).2
    nlinarith [hlower, hneg]
  have hhi : x < ((-k : ℤ) : ℝ) + 1 := by
    apply (div_lt_iff₀ hperiod).2
    nlinarith [hupper, hshift]
  have hfloor : ⌊x⌋ = -k := Int.floor_eq_iff.mpr ⟨hlo, hhi⟩
  calc
    d39RotatedCircleRayHitTime α a = x - (⌊x⌋ : ℝ) := Int.self_sub_floor x
    _ = x + (k : ℝ) := by rw [hfloor]; push_cast; ring
    _ = (a.arg + 2 * Real.pi * (k : ℝ) - α) / (2 * Real.pi) := by
      change (a.arg - α) / (2 * Real.pi) + (k : ℝ) = _
      field_simp [ne_of_gt hperiod]
      ring

/-- Helper toward Proposition 5.16: at the fractional-part parameter, the
rotated circle meets the positive ray through `a`. -/
theorem d39_rotatedCirclePath_hits_ray_at_fract_time
    (ρ α : ℝ) (a : ℂ) (hρ : 0 < ρ) (ha : a ≠ 0)
    (hmiss : ∀ k : ℤ, a.arg ≠ α + 2 * Real.pi * (k : ℝ)) :
    ∃ r : ℝ, 0 < r ∧
      d39RotatedCirclePath ρ α
        ⟨d39RotatedCircleRayHitTime α a,
          (d39_rotatedCircleRayHitTime_mem_Ioo α a ha hmiss).1.le,
          (d39_rotatedCircleRayHitTime_mem_Ioo α a ha hmiss).2.le⟩ =
        (r : ℂ) * a := by
  let x := (a.arg - α) / (2 * Real.pi)
  have hfract : d39RotatedCircleRayHitTime α a = x - (⌊x⌋ : ℝ) := by
    exact Int.self_sub_floor x
  have hmul : 2 * Real.pi * x = a.arg - α := by
    dsimp [x]
    field_simp
  have hphase : α + 2 * Real.pi * d39RotatedCircleRayHitTime α a =
      a.arg + 2 * Real.pi * ((-⌊x⌋ : ℤ) : ℝ) := by
    calc
      α + 2 * Real.pi * d39RotatedCircleRayHitTime α a =
          α + 2 * Real.pi * (x - (⌊x⌋ : ℝ)) :=
            congrArg (fun t : ℝ => α + 2 * Real.pi * t) hfract
      _ = α + (2 * Real.pi * x - 2 * Real.pi * (⌊x⌋ : ℝ)) := by ring
      _ = α + (a.arg - α - 2 * Real.pi * (⌊x⌋ : ℝ)) := by rw [hmul]
      _ = a.arg + 2 * Real.pi * ((-⌊x⌋ : ℤ) : ℝ) := by push_cast; ring
  let z : ℂ := ((α + 2 * Real.pi * d39RotatedCircleRayHitTime α a : ℝ) : ℂ) *
    Complex.I
  have hzarg : z.im = a.arg + 2 * Real.pi * ((-⌊x⌋ : ℤ) : ℝ) := by
    simp [z, hphase]
  obtain ⟨r, hr, hexp⟩ := d39_exp_argument_congruent_to_ray_lies_on_ray
    z a ha (-⌊x⌋) hzarg
  refine ⟨ρ * r, mul_pos hρ hr, ?_⟩
  change (ρ : ℂ) * Complex.exp z = ((ρ * r : ℝ) : ℂ) * a
  rw [hexp]
  push_cast
  ring

/-- Helper toward Proposition 5.16: the ray hit occurs at the radial
parameter forced by the circle radius. -/
theorem d39_rotatedCirclePath_ray_hit_parameter
    (ρ α : ℝ) (a : ℂ) (hρ : 0 < ρ) (ha : a ≠ 0)
    (hmiss : ∀ k : ℤ, a.arg ≠ α + 2 * Real.pi * (k : ℝ)) :
    d39RotatedCirclePath ρ α
      ⟨d39RotatedCircleRayHitTime α a,
        (d39_rotatedCircleRayHitTime_mem_Ioo α a ha hmiss).1.le,
        (d39_rotatedCircleRayHitTime_mem_Ioo α a ha hmiss).2.le⟩ =
      ((ρ / ‖a‖ : ℝ) : ℂ) * a := by
  let t : unitInterval := ⟨d39RotatedCircleRayHitTime α a,
    (d39_rotatedCircleRayHitTime_mem_Ioo α a ha hmiss).1.le,
    (d39_rotatedCircleRayHitTime_mem_Ioo α a ha hmiss).2.le⟩
  obtain ⟨r, hr, hhit⟩ :=
    d39_rotatedCirclePath_hits_ray_at_fract_time ρ α a hρ ha hmiss
  have hrad : r * ‖a‖ = ρ := by
    calc
      r * ‖a‖ = ‖(r : ℂ) * a‖ := by
        rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      _ = ‖d39RotatedCirclePath ρ α t‖ := congrArg norm hhit.symm
      _ = ρ := d39_rotatedCirclePath_norm hρ t
  have hradius : r = ρ / ‖a‖ := by
    field_simp [ne_of_gt (norm_pos_iff.mpr ha)]
    nlinarith [hrad]
  change d39RotatedCirclePath ρ α t = ((ρ / ‖a‖ : ℝ) : ℂ) * a
  rw [← hradius]
  exact hhit

/-- Helper toward Proposition 5.16: a counterclockwise circle can meet a
fixed positive ray at most once in the open parameter interval. -/
theorem d39_rotatedCirclePath_ray_hit_unique
    (ρ α : ℝ) (a : ℂ) (hρ : 0 < ρ) (ha : a ≠ 0)
    (t s : unitInterval) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (hs0 : 0 < (s : ℝ)) (hs1 : (s : ℝ) < 1)
    (htRay : ∃ r : ℝ, 0 ≤ r ∧
      d39RotatedCirclePath ρ α t = (r : ℂ) * a)
    (hsRay : ∃ r : ℝ, 0 ≤ r ∧
      d39RotatedCirclePath ρ α s = (r : ℂ) * a) : t = s := by
  rcases htRay with ⟨r₁, hr₁, h₁⟩
  rcases hsRay with ⟨r₂, hr₂, h₂⟩
  have hrad₁ : ρ = r₁ * ‖a‖ := by
    calc
      ρ = ‖d39RotatedCirclePath ρ α t‖ := (d39_rotatedCirclePath_norm hρ t).symm
      _ = ‖(r₁ : ℂ) * a‖ := congrArg norm h₁
      _ = r₁ * ‖a‖ := by
        rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr₁]
  have hrad₂ : ρ = r₂ * ‖a‖ := by
    calc
      ρ = ‖d39RotatedCirclePath ρ α s‖ := (d39_rotatedCirclePath_norm hρ s).symm
      _ = ‖(r₂ : ℂ) * a‖ := congrArg norm h₂
      _ = r₂ * ‖a‖ := by
        rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr₂]
  have hr₁₂ : r₁ = r₂ := by
    apply mul_right_cancel₀ (norm_pos_iff.mpr ha).ne'
    linarith [hrad₁, hrad₂]
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hρ)
  have h₁' : (ρ : ℂ) * Complex.exp
      ((((α + 2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)) =
      (r₁ : ℂ) * a := by
    change d39RotatedCirclePath ρ α t = (r₁ : ℂ) * a at h₁
    simpa [d39RotatedCirclePath] using h₁
  have h₂' : (ρ : ℂ) * Complex.exp
      ((((α + 2 * Real.pi * (s : ℝ) : ℝ) : ℂ) * Complex.I)) =
      (r₂ : ℂ) * a := by
    change d39RotatedCirclePath ρ α s = (r₂ : ℂ) * a at h₂
    simpa [d39RotatedCirclePath] using h₂
  have hexp : Complex.exp
      ((((α + 2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)) =
      Complex.exp ((((α + 2 * Real.pi * (s : ℝ) : ℝ) : ℂ) * Complex.I)) := by
    apply mul_left_cancel₀ hρC
    calc
      (ρ : ℂ) * Complex.exp
          ((((α + 2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)) =
          (r₁ : ℂ) * a := h₁'
      _ = (r₂ : ℂ) * a := congrArg (fun q : ℝ => (q : ℂ) * a) hr₁₂
      _ = (ρ : ℂ) * Complex.exp
          ((((α + 2 * Real.pi * (s : ℝ) : ℝ) : ℂ) * Complex.I)) := h₂'.symm
  obtain ⟨k, hk⟩ := (Complex.exp_eq_exp_iff_exists_int).1 hexp
  have hangle : α + 2 * Real.pi * (t : ℝ) =
      α + 2 * Real.pi * (s : ℝ) + (k : ℝ) * (2 * Real.pi) := by
    have him := congrArg Complex.im hk
    simpa using him
  have hdiff : (t : ℝ) - (s : ℝ) = (k : ℝ) := by
    nlinarith [hangle, Real.pi_pos]
  have hkloR : (-1 : ℝ) < (k : ℝ) := by
    linarith [hdiff, ht0, hs1]
  have hkhiR : (k : ℝ) < 1 := by
    linarith [hdiff, ht1, hs0]
  have hklo : (-1 : ℤ) < k := by
    exact_mod_cast hkloR
  have hkhi : k < (1 : ℤ) := by
    exact_mod_cast hkhiR
  have hkzero : k = 0 := by omega
  have hkzeroR : (k : ℝ) = 0 := by exact_mod_cast hkzero
  apply Subtype.ext
  linarith [hdiff, hkzeroR]

/-- Helper toward Proposition 5.16: when `α` avoids the ray direction, the
rotated loop meets that positive ray at exactly one open-interval parameter,
given by the fractional-part formula. -/
theorem d39_rotatedCirclePath_meets_ray_at_unique_time
    (ρ α : ℝ) (a : ℂ) (hρ : 0 < ρ) (ha : a ≠ 0)
    (hmiss : ∀ k : ℤ, a.arg ≠ α + 2 * Real.pi * (k : ℝ)) :
    ∃! t : unitInterval,
      (0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
        ∃ r : ℝ, 0 ≤ r ∧ d39RotatedCirclePath ρ α t = (r : ℂ) * a) ∧
      (t : ℝ) = d39RotatedCircleRayHitTime α a := by
  let t : unitInterval := ⟨d39RotatedCircleRayHitTime α a,
    (d39_rotatedCircleRayHitTime_mem_Ioo α a ha hmiss).1.le,
    (d39_rotatedCircleRayHitTime_mem_Ioo α a ha hmiss).2.le⟩
  obtain ⟨r, hr, hhit⟩ :=
    d39_rotatedCirclePath_hits_ray_at_fract_time ρ α a hρ ha hmiss
  refine ⟨t, ?_, ?_⟩
  · refine ⟨⟨(d39_rotatedCircleRayHitTime_mem_Ioo α a ha hmiss).1,
      (d39_rotatedCircleRayHitTime_mem_Ioo α a ha hmiss).2,
      ⟨r, hr.le, hhit⟩⟩, rfl⟩
  · intro s hs
    rcases hs with ⟨⟨hs0, hs1, hsray⟩, _⟩
    symm
    apply d39_rotatedCirclePath_ray_hit_unique ρ α a hρ ha t s
      (d39_rotatedCircleRayHitTime_mem_Ioo α a ha hmiss).1
      (d39_rotatedCircleRayHitTime_mem_Ioo α a ha hmiss).2 hs0 hs1
    · exact ⟨r, hr.le, hhit⟩
    · exact hsray

/-- Helper toward Proposition 5.16: the image loop meets the image germ at
the same angular hit time, with a unique target ray parameter. -/
theorem d39_imageRotatedCirclePath_hits_image_germ
    (K : ℂ ≃ₜ ℂ) (u u' : ℂ) (r s ρ α : ℝ)
    (hu : u ≠ 0) (hu' : u' ≠ 0) (hρ : 0 < ρ) (hρr : ρ < r * ‖u‖)
    (himage : K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧
        z = (t : ℂ) * u} =
      {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * u'})
    (hmiss : ∀ k : ℤ, u.arg ≠ α + 2 * Real.pi * (k : ℝ)) :
    ∃! t' : ℝ, 0 ≤ t' ∧ t' ≤ s ∧
      ((d39RotatedCirclePath ρ α).map K.continuous)
        ⟨d39RotatedCircleRayHitTime α u,
          (d39_rotatedCircleRayHitTime_mem_Ioo α u hu hmiss).1.le,
          (d39_rotatedCircleRayHitTime_mem_Ioo α u hu hmiss).2.le⟩ =
        (t' : ℂ) * u' := by
  have huNorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have ht0 : 0 < ρ / ‖u‖ := div_pos hρ huNorm
  have htr : ρ / ‖u‖ < r := (div_lt_iff₀ huNorm).2 (by nlinarith [hρr])
  let τ : unitInterval := ⟨d39RotatedCircleRayHitTime α u,
    (d39_rotatedCircleRayHitTime_mem_Ioo α u hu hmiss).1.le,
    (d39_rotatedCircleRayHitTime_mem_Ioo α u hu hmiss).2.le⟩
  have hsource := d39_rotatedCirclePath_ray_hit_parameter ρ α u hρ hu hmiss
  have htarget := d39_image_germ_segment_has_unique_target_parameter
    K u u' r s hu' himage (ρ / ‖u‖) ht0.le htr.le
  obtain ⟨t', ht', hunique⟩ := htarget
  refine ⟨t', ?_, ?_⟩
  · rcases ht' with ⟨ht0', hts, hpoint⟩
    refine ⟨ht0', hts, ?_⟩
    change K (d39RotatedCirclePath ρ α τ) = (t' : ℂ) * u'
    rw [hsource]
    exact hpoint
  · intro t'' ht''
    rcases ht'' with ⟨ht''0, ht''s, hpoint⟩
    apply hunique t'' ⟨ht''0, ht''s, ?_⟩
    change K (d39RotatedCirclePath ρ α τ) = (t'' : ℂ) * u' at hpoint
    rw [hsource] at hpoint
    exact hpoint

/-- Helper toward Proposition 5.16: within the open parameter interval, the
image loop lies on an image germ exactly at the source ray's fractional-part
hit time. -/
theorem d39_imageRotatedCirclePath_image_germ_hit_iff
    (K : ℂ ≃ₜ ℂ) (u u' : ℂ) (r s ρ α : ℝ)
    (hu : u ≠ 0) (hu' : u' ≠ 0) (hρ : 0 < ρ) (hρr : ρ < r * ‖u‖)
    (himage : K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧
        z = (t : ℂ) * u} =
      {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * u'})
    (hmiss : ∀ k : ℤ, u.arg ≠ α + 2 * Real.pi * (k : ℝ))
    (t : unitInterval) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    ((d39RotatedCirclePath ρ α).map K.continuous) t ∈
        {z : ℂ | ∃ q : ℝ, 0 ≤ q ∧ q ≤ s ∧ z = (q : ℂ) * u'} ↔
      (t : ℝ) = d39RotatedCircleRayHitTime α u := by
  constructor
  · intro htarget
    rw [← himage] at htarget
    rcases htarget with ⟨z, ⟨q, hq0, hqr, hqeq⟩, hz⟩
    change K z = K (d39RotatedCirclePath ρ α t) at hz
    have hz' : z = d39RotatedCirclePath ρ α t := K.injective hz
    have hray : ∃ q : ℝ, 0 ≤ q ∧
        d39RotatedCirclePath ρ α t = (q : ℂ) * u := by
      refine ⟨q, hq0, ?_⟩
      calc
        d39RotatedCirclePath ρ α t = z := hz'.symm
        _ = (q : ℂ) * u := hqeq
    let τ : unitInterval := ⟨d39RotatedCircleRayHitTime α u,
      (d39_rotatedCircleRayHitTime_mem_Ioo α u hu hmiss).1.le,
      (d39_rotatedCircleRayHitTime_mem_Ioo α u hu hmiss).2.le⟩
    have hτ := d39_rotatedCirclePath_ray_hit_parameter ρ α u hρ hu hmiss
    have hts := d39_rotatedCirclePath_ray_hit_unique ρ α u hρ hu τ t
      (d39_rotatedCircleRayHitTime_mem_Ioo α u hu hmiss).1
      (d39_rotatedCircleRayHitTime_mem_Ioo α u hu hmiss).2 ht0 ht1
      ⟨ρ / ‖u‖, le_of_lt (div_pos hρ (norm_pos_iff.mpr hu)), hτ⟩ hray
    exact congrArg (fun x : unitInterval => (x : ℝ)) hts.symm
  · intro htime
    have htarget := d39_imageRotatedCirclePath_hits_image_germ
      K u u' r s ρ α hu hu' hρ hρr himage hmiss
    rcases htarget with ⟨q, hq, _⟩
    let τ : unitInterval := ⟨d39RotatedCircleRayHitTime α u,
      (d39_rotatedCircleRayHitTime_mem_Ioo α u hu hmiss).1.le,
      (d39_rotatedCircleRayHitTime_mem_Ioo α u hu hmiss).2.le⟩
    have htτ : t = τ := by
      apply Subtype.ext
      exact htime
    rw [htτ]
    exact ⟨q, hq.1, hq.2.1, hq.2.2⟩

/-- Helper toward Proposition 5.16: the rotated image loop has one
intersection with an image germ, and every path parameter on that germ gives
that same point. -/
theorem d39_rotatedCirclePath_to_imageRay_crossing_bridge
    (K : ℂ ≃ₜ ℂ) (u u' : ℂ) (r s ρ α : ℝ)
    (hu : u ≠ 0) (hρ : 0 < ρ) (hρr : ρ < r * ‖u‖)
    (himage : K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧
        z = (t : ℂ) * u} =
      {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * u'}) :
    ∃! y : ℂ,
      (y ∈ K '' {z : ℂ | ‖z‖ = ρ} ∧
        y ∈ {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * u'}) ∧
      (∀ t : unitInterval,
        ((d39RotatedCirclePath ρ α).map K.continuous) t ∈
            {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * u'} →
          ((d39RotatedCirclePath ρ α).map K.continuous) t = y) := by
  obtain ⟨y, hy, hyunique⟩ := d39_image_circle_meets_image_germ_once
    K u u' r s ρ hu hρ hρr himage
  refine ⟨y, ⟨hy, ?_⟩, ?_⟩
  · intro t hray
    apply hyunique
    refine ⟨?_, hray⟩
    refine ⟨d39RotatedCirclePath ρ α t, ?_, rfl⟩
    simpa only [Set.mem_ofPred_eq] using d39_rotatedCirclePath_norm hρ t
  · intro y' hy'
    exact hyunique y' hy'.1

/-- Helper toward Proposition 5.16: an orientation-preserving homeomorphism
transports the rotated loop's winding one to its image about `K 0`. -/
theorem d39_oriented_image_rotatedCirclePath_hasWinding_one
    {K : ℂ ≃ₜ ℂ} (hK : OrientationPreserving K) {ρ α : ℝ}
    (hρ : 0 < ρ) :
    HasWinding ((d39RotatedCirclePath ρ α).map K.continuous) (K 0) 1 := by
  have havoid : 0 ∉ Set.range (d39RotatedCirclePath ρ α) := by
    rintro ⟨t, ht⟩
    have hnorm := d39_rotatedCirclePath_norm (α := α) hρ t
    have : ρ = 0 := by simpa [ht] using hnorm.symm
    exact (ne_of_gt hρ) this
  exact (d39_orientationPreserving_transports_winding_at_origin hK
    (d39RotatedCirclePath ρ α) havoid 1).mp
      (d39_rotatedCirclePath_hasWinding_one hρ)














































end DirectedDistances.PlanarMap

end

