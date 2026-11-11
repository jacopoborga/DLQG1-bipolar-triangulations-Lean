/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39RadialOrder16

/-! Helper toward Proposition 5.16. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16: distinct principal arguments give
 distinct normalized fractional ray times. -/
theorem d39_fract_normalized_arg_ne_of_distinct
    (a b : ℂ) (α : ℝ) (hab : a.arg ≠ b.arg) :
    Int.fract ((a.arg - α) / (2 * Real.pi)) ≠
      Int.fract ((b.arg - α) / (2 * Real.pi)) := by
  have ha := Complex.arg_mem_Ioc a
  have hb := Complex.arg_mem_Ioc b
  change -Real.pi < a.arg ∧ a.arg ≤ Real.pi at ha
  change -Real.pi < b.arg ∧ b.arg ≤ Real.pi at hb
  have hp : 0 < 2 * Real.pi := by positivity
  intro heq
  rcases Int.fract_eq_fract.mp heq with ⟨k, hk⟩
  have hmul := congrArg (fun x : ℝ => x * (2 * Real.pi)) hk
  have hdiff : a.arg - b.arg = (2 * Real.pi) * (k : ℝ) := by
    field_simp [ne_of_gt hp] at hmul
    nlinarith [hmul]
  have hdifflo : -(2 * Real.pi) < a.arg - b.arg := by linarith [ha.1, hb.2]
  have hdiffhi : a.arg - b.arg < 2 * Real.pi := by linarith [ha.2, hb.1]
  have hklo : (-1 : ℝ) < (k : ℝ) := by
    have haux : (-(2 * Real.pi)) / (2 * Real.pi) < (k : ℝ) := by
      rw [div_lt_iff₀ hp]
      rw [show (k : ℝ) * (2 * Real.pi) =
        (2 * Real.pi) * (k : ℝ) by ring]
      rw [← hdiff]
      exact hdifflo
    have hdiv : (-(2 * Real.pi)) / (2 * Real.pi) = -1 := by
      field_simp [ne_of_gt hp]
    rw [hdiv] at haux
    exact haux
  have hkhi : (k : ℝ) < 1 := by
    have haux : (k : ℝ) < (2 * Real.pi) / (2 * Real.pi) := by
      rw [lt_div_iff₀ hp]
      rw [show (k : ℝ) * (2 * Real.pi) =
        (2 * Real.pi) * (k : ℝ) by ring]
      rw [← hdiff]
      exact hdiffhi
    have hdiv : (2 * Real.pi) / (2 * Real.pi) = 1 := by
      field_simp [ne_of_gt hp]
    rw [hdiv] at haux
    exact haux
  have hklo' : (-1 : ℤ) < k := by exact_mod_cast hklo
  have hkhi' : k < (1 : ℤ) := by exact_mod_cast hkhi
  have hkzero : k = 0 := by omega
  apply hab
  have hzero : a.arg - b.arg = 0 := by rw [hdiff, hkzero]; ring
  linarith

/-- Helper toward Proposition 5.16: for a base angle missing three distinct
rays, the source turn comparison is the cyclic order of their ray hit times. -/
theorem d39_source_ccwTurn_lt_iff_cyclicOrder
    (α : ℝ) (u v w : ℂ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : u.arg ≠ v.arg) (huw : u.arg ≠ w.arg)
    (hvw : v.arg ≠ w.arg)
    (hmissU : ∀ k : ℤ, u.arg ≠ α + 2 * Real.pi * (k : ℝ))
    (hmissV : ∀ k : ℤ, v.arg ≠ α + 2 * Real.pi * (k : ℝ))
    (hmissW : ∀ k : ℤ, w.arg ≠ α + 2 * Real.pi * (k : ℝ)) :
    ccwTurn u w < ccwTurn u v ↔
      d39CyclicOrder (d39RotatedCircleRayHitTime α u)
        (d39RotatedCircleRayHitTime α w) (d39RotatedCircleRayHitTime α v) := by
  let tu := d39RotatedCircleRayHitTime α u
  let tw := d39RotatedCircleRayHitTime α w
  let tv := d39RotatedCircleRayHitTime α v
  let xu := (u.arg - α) / (2 * Real.pi)
  let xw := (w.arg - α) / (2 * Real.pi)
  let xv := (v.arg - α) / (2 * Real.pi)
  have htu : tu = Int.fract xu := by
    exact d39_rotatedCircleRayHitTime_eq_fract_of_miss α u hmissU
  have htw : tw = Int.fract xw := by
    exact d39_rotatedCircleRayHitTime_eq_fract_of_miss α w hmissW
  have htv : tv = Int.fract xv := by
    exact d39_rotatedCircleRayHitTime_eq_fract_of_miss α v hmissV
  have htuIoo : tu ∈ Set.Ioo 0 1 := d39_rotatedCircleRayHitTime_mem_Ioo α u hu hmissU
  have htwIoo : tw ∈ Set.Ioo 0 1 := d39_rotatedCircleRayHitTime_mem_Ioo α w hw hmissW
  have htvIoo : tv ∈ Set.Ioo 0 1 := d39_rotatedCircleRayHitTime_mem_Ioo α v hv hmissV
  have hutw : tu ≠ tw := by
    rw [htu, htw]
    exact d39_fract_normalized_arg_ne_of_distinct u w α huw
  have hutv : tu ≠ tv := by
    rw [htu, htv]
    exact d39_fract_normalized_arg_ne_of_distinct u v α huv
  have hwtv : tw ≠ tv := by
    rw [htw, htv]
    exact d39_fract_normalized_arg_ne_of_distinct w v α (Ne.symm hvw)
  have hfractW : Int.fract ((w.arg - u.arg) / (2 * Real.pi)) =
      Int.fract (tw - tu) := by
    calc
      Int.fract ((w.arg - u.arg) / (2 * Real.pi)) = Int.fract (xw - xu) := by
        congr 1
        dsimp [xw, xu]
        field_simp
        ring
      _ = Int.fract (Int.fract xw - Int.fract xu) :=
        d39_fract_sub_fract_eq_fract_sub xw xu
      _ = Int.fract (tw - tu) := by rw [← htw, ← htu]
  have hfractV : Int.fract ((v.arg - u.arg) / (2 * Real.pi)) =
      Int.fract (tv - tu) := by
    calc
      Int.fract ((v.arg - u.arg) / (2 * Real.pi)) = Int.fract (xv - xu) := by
        congr 1
        dsimp [xv, xu]
        field_simp
        ring
      _ = Int.fract (Int.fract xv - Int.fract xu) :=
        d39_fract_sub_fract_eq_fract_sub xv xu
      _ = Int.fract (tv - tu) := by rw [← htv, ← htu]
  have hturnW := d39_ccwTurn_eq_twoPi_mul_fract_arg_diff u w hu hw huw
  have hturnV := d39_ccwTurn_eq_twoPi_mul_fract_arg_diff u v hu hv huv
  have hp : 0 < 2 * Real.pi := by positivity
  have hcompare : ccwTurn u w < ccwTurn u v ↔
      Int.fract (tw - tu) < Int.fract (tv - tu) := by
    rw [hturnW, hturnV, hfractW, hfractV]
    constructor <;> intro h <;> nlinarith [hp]
  have hcyclic := d39_fract_sub_lt_iff_cyclicOrder tu tw tv
    htuIoo.1.le htuIoo.2 htwIoo.1.le htwIoo.2 htvIoo.1.le htvIoo.2
    hutw hutv hwtv
  change (ccwTurn u w < ccwTurn u v ↔
    d39CyclicOrder tu tw tv)
  exact hcompare.trans hcyclic

/-- Helper toward Proposition 5.16: a suitable base angle makes the source
turn comparison equal the cyclic order of the three radial hit times. -/
theorem d39_exists_base_angle_source_ccwTurn_lt_iff_cyclicOrder
    (u v w : ℂ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : u.arg ≠ v.arg) (huw : u.arg ≠ w.arg)
    (hvw : v.arg ≠ w.arg) :
    ∃ α : ℝ,
      (∀ k : ℤ, u.arg ≠ α + 2 * Real.pi * (k : ℝ)) ∧
      (∀ k : ℤ, v.arg ≠ α + 2 * Real.pi * (k : ℝ)) ∧
      (∀ k : ℤ, w.arg ≠ α + 2 * Real.pi * (k : ℝ)) ∧
      (ccwTurn u w < ccwTurn u v ↔
        d39CyclicOrder (d39RotatedCircleRayHitTime α u)
          (d39RotatedCircleRayHitTime α w) (d39RotatedCircleRayHitTime α v)) := by
  obtain ⟨α, hmissU, hmissV, hmissW, _, _, _⟩ :=
    d39_exists_base_angle_with_three_interior_ray_hits u v w hu hv hw huv huw hvw
  exact ⟨α, hmissU, hmissV, hmissW,
    d39_source_ccwTurn_lt_iff_cyclicOrder α u v w hu hv hw huv huw hvw
      hmissU hmissV hmissW⟩

/-- Helper toward Proposition 5.16: a lattice class avoiding the initial
lift value has a unique representative strictly inside one lift period. -/
theorem d39_exists_lattice_representative_in_open_period
    (a L0 period : ℝ) (hperiod : 0 < period)
    (havoid : ∀ k : ℤ, L0 ≠ a + period * (k : ℝ)) :
    ∃ rep : ℝ, (∃ k : ℤ, rep = a + period * (k : ℝ)) ∧
      L0 < rep ∧ rep < L0 + period := by
  let x : ℝ := (L0 - a) / period
  let n : ℤ := ⌊x⌋ + 1
  have hfloorle : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have hfloorlt : (⌊x⌋ : ℝ) < x := by
    by_contra hnot
    have heq : x = (⌊x⌋ : ℝ) := le_antisymm (le_of_not_gt hnot) hfloorle
    apply havoid ⌊x⌋
    have hmul := congrArg (fun y : ℝ => y * period) heq
    dsimp [x] at hmul
    field_simp [ne_of_gt hperiod] at hmul
    nlinarith [hmul]
  refine ⟨a + period * (n : ℝ), ⟨n, rfl⟩, ?_, ?_⟩
  · have hmul := mul_lt_mul_of_pos_right (Int.lt_floor_add_one x) hperiod
    dsimp [x] at hmul
    field_simp [ne_of_gt hperiod] at hmul
    have hn : (n : ℝ) = (⌊x⌋ : ℝ) + 1 := by
      dsimp [n]
      push_cast
      ring
    rw [hn]
    dsimp [x]
    nlinarith [hmul]
  · have hmul := mul_lt_mul_of_pos_right
      (show (⌊x⌋ : ℝ) + 1 < x + 1 by linarith [hfloorlt]) hperiod
    dsimp [x] at hmul
    field_simp [ne_of_gt hperiod] at hmul
    have hn : (n : ℝ) = (⌊x⌋ : ℝ) + 1 := by
      dsimp [n]
      push_cast
      ring
    rw [hn]
    dsimp [x]
    nlinarith [hmul]

/-- Helper toward Proposition 5.16: a unique lattice hit in one lift period
occurs at the value of that lattice representative. -/
theorem d39_continuous_lift_unique_hit_value
    (L : C(unitInterval, ℝ)) (a rep period : ℝ) (t : unitInterval)
    (hrep : ∃ k : ℤ, rep = a + period * (k : ℝ))
    (hwindow : L 0 < rep ∧ rep < L 0 + period)
    (hend : L 1 = L 0 + period)
    (hunique : ∀ s : unitInterval,
      (∃ k : ℤ, L s = a + period * (k : ℝ)) ↔ s = t) :
    L t = rep := by
  have hvalue : rep ∈ Set.Icc (L 0) (L 1) := by
    rw [hend]
    exact ⟨hwindow.1.le, hwindow.2.le⟩
  obtain ⟨s, hs⟩ := (intermediate_value_univ 0 1 L.continuous) hvalue
  have hs' : L s = rep := by simpa using hs
  rcases hrep with ⟨k, hk⟩
  have hhit : ∃ k : ℤ, L s = a + period * (k : ℝ) := by
    exact ⟨k, by rw [hs', hk]⟩
  have hst : s = t := (hunique s).1 hhit
  calc
    L t = L s := (congrArg L hst).symm
    _ = rep := hs'

/-- Helper toward Proposition 5.16: unique lattice hit times have the same
strict order as their representatives in one lift period. -/
theorem d39_image_lift_lattice_hit_times_order_iff
    (L : C(unitInterval, ℝ)) (a b aRep bRep period : ℝ)
    (ta tb : unitInterval) (hperiod : 0 < period)
    (hrepA : ∃ k : ℤ, aRep = a + period * (k : ℝ))
    (hrepB : ∃ k : ℤ, bRep = b + period * (k : ℝ))
    (hwindow : L 0 < aRep ∧ aRep < L 0 + period ∧
      L 0 < bRep ∧ bRep < L 0 + period)
    (hend : L 1 = L 0 + period)
    (haUnique : ∀ t : unitInterval,
      (∃ k : ℤ, L t = a + period * (k : ℝ)) ↔ t = ta)
    (hbUnique : ∀ t : unitInterval,
      (∃ k : ℤ, L t = b + period * (k : ℝ)) ↔ t = tb) :
    ((ta : ℝ) < (tb : ℝ)) ↔ aRep < bRep := by
  have haValue := d39_continuous_lift_unique_hit_value L a aRep period ta
    hrepA ⟨hwindow.1, hwindow.2.1⟩ hend haUnique
  have hbValue := d39_continuous_lift_unique_hit_value L b bRep period tb
    hrepB ⟨hwindow.2.2.1, hwindow.2.2.2⟩ hend hbUnique
  constructor
  · intro htime
    by_contra hrep
    have hle : bRep ≤ aRep := le_of_not_gt hrep
    rcases eq_or_lt_of_le hle with heq | hlt
    · have hhitA : ∃ k : ℤ, L tb = a + period * (k : ℝ) := by
        rw [hbValue, heq]
        exact hrepA
      have htimeEq : tb = ta := (haUnique tb).1 hhitA
      have hvalEq := congrArg (fun t : unitInterval => (t : ℝ)) htimeEq
      exact (ne_of_lt htime) hvalEq.symm
    · have hrev := d39_image_lift_lattice_hit_times_order
        L b a bRep aRep period tb ta hperiod hrepB hrepA
        ⟨hwindow.2.2.1, hlt, hwindow.2.1⟩ hend hbUnique haUnique
      exact (lt_asymm htime hrev)
  · intro hrep
    exact d39_image_lift_lattice_hit_times_order L a b aRep bRep period ta tb
      hperiod hrepA hrepB ⟨hwindow.1, hrep, hwindow.2.2.2⟩ hend haUnique hbUnique

/-- Helper toward Proposition 5.16: on the whole parameter interval, a
lifted image argument hits a target ray exactly at the source ray hit time. -/
theorem d39_image_lift_ray_argument_has_unique_time_all
    (K : ℂ ≃ₜ ℂ) (hK0 : K 0 = 0)
    (u u' : ℂ) (r s ρ α : ℝ)
    (hu : u ≠ 0) (hu' : u' ≠ 0) (hρ : 0 < ρ)
    (hρr : ρ < r * ‖u‖)
    (hKball : ∀ z : ℂ, ‖z‖ ≤ ρ → ‖K z‖ < s * ‖u'‖)
    (himage : K '' {z : ℂ | ∃ q : ℝ, 0 ≤ q ∧ q ≤ r ∧
        z = (q : ℂ) * u} =
      {z : ℂ | ∃ q : ℝ, 0 ≤ q ∧ q ≤ s ∧ z = (q : ℂ) * u'})
    (hmiss : ∀ k : ℤ, u.arg ≠ α + 2 * Real.pi * (k : ℝ))
    (φ : C(unitInterval, ℂ))
    (hφ : ∀ t, Complex.exp (φ t) =
      ((d39RotatedCirclePath ρ α).map K.continuous) t - K 0)
    (hendpointAvoid : ∀ t : unitInterval, (t = 0 ∨ t = 1) →
      ((d39RotatedCirclePath ρ α).map K.continuous) t ∉
        {z : ℂ | ∃ q : ℝ, 0 ≤ q ∧ q ≤ s ∧ z = (q : ℂ) * u'})
    (hHitIoo : d39RotatedCircleRayHitTime α u ∈ Set.Ioo 0 1) :
    ∀ t : unitInterval,
      (∃ k : ℤ, (φ t).im = u'.arg + 2 * Real.pi * (k : ℝ)) ↔
        (t : ℝ) = d39RotatedCircleRayHitTime α u := by
  intro t
  by_cases htEnd : t = 0 ∨ t = 1
  · constructor
    · rintro ⟨k, harg⟩
      have hφ' : Complex.exp (φ t) = K (d39RotatedCirclePath ρ α t) := by
        simpa [hK0] using hφ t
      obtain ⟨q, hq, hexp⟩ :=
        d39_exp_argument_congruent_to_ray_lies_on_ray (φ t) u' hu' k harg
      have hpoint : K (d39RotatedCirclePath ρ α t) = (q : ℂ) * u' :=
        hφ'.symm.trans hexp
      have hKcircle := hKball _
        (by rw [d39_rotatedCirclePath_norm (α := α) hρ t])
      rw [hpoint, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hq] at hKcircle
      have hqs : q ≤ s := by nlinarith [norm_pos_iff.mpr hu']
      have hsegment :
          ((d39RotatedCirclePath ρ α).map K.continuous) t ∈
            {z : ℂ | ∃ q : ℝ, 0 ≤ q ∧ q ≤ s ∧ z = (q : ℂ) * u'} :=
        ⟨q, hq.le, hqs, hpoint⟩
      exact False.elim (hendpointAvoid t htEnd hsegment)
    · intro htime
      rcases htEnd with ht0 | ht1
      · subst t
        change (0 : ℝ) = d39RotatedCircleRayHitTime α u at htime
        exact False.elim ((ne_of_gt hHitIoo.1) htime.symm)
      · subst t
        change (1 : ℝ) = d39RotatedCircleRayHitTime α u at htime
        exact False.elim (((ne_of_lt hHitIoo.2).symm) htime)
  · have ht0 : 0 < (t : ℝ) := by
      have hnonneg := t.property.1
      rcases eq_or_lt_of_le hnonneg with hzero | hpos
      · exact False.elim (htEnd (Or.inl (Subtype.ext hzero.symm)))
      · exact hpos
    have ht1 : (t : ℝ) < 1 := by
      have hle := t.property.2
      rcases eq_or_lt_of_le hle with hone | hlt
      · exact False.elim (htEnd (Or.inr (Subtype.ext hone)))
      · exact hlt
    have hiff := d39_image_lift_ray_argument_has_unique_time
      K hK0 u u' r s ρ α hu hu' hρ hρr hKball himage hmiss φ hφ t ht0 ht1
    constructor
    · intro hhit
      exact hiff.mp hhit
    · intro htime
      exact hiff.mpr htime




































end DirectedDistances.PlanarMap

end
