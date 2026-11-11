/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39RadialOrder15

/-! Helper toward Proposition 5.16. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16: subtracting two fractional parts before
taking a fractional part is invariant under integer shifts. -/
theorem d39_fract_sub_fract_eq_fract_sub (a b : ℝ) :
    Int.fract (a - b) = Int.fract (Int.fract a - Int.fract b) := by
  have ha' : Int.fract a = a - (⌊a⌋ : ℝ) := Int.self_sub_floor a
  have hb' : Int.fract b = b - (⌊b⌋ : ℝ) := Int.self_sub_floor b
  have ha : a = Int.fract a + (⌊a⌋ : ℝ) := by linarith
  have hb : b = Int.fract b + (⌊b⌋ : ℝ) := by linarith
  have hshift : a - b = (Int.fract a - Int.fract b) +
      ((⌊a⌋ : ℝ) - (⌊b⌋ : ℝ)) := by
    calc
      a - b = (Int.fract a + (⌊a⌋ : ℝ)) -
          (Int.fract b + (⌊b⌋ : ℝ)) := by linarith [ha, hb]
      _ = (Int.fract a - Int.fract b) +
          ((⌊a⌋ : ℝ) - (⌊b⌋ : ℝ)) := by ring
  apply Int.fract_eq_fract.mpr
  refine ⟨⌊a⌋ - ⌊b⌋, ?_⟩
  push_cast
  linarith [hshift]

/-- Helper toward Proposition 5.16: for distinct nonzero directions, the
counterclockwise turn is `2π` times the fractional normalized angular
difference. -/
theorem d39_ccwTurn_eq_twoPi_mul_fract_arg_diff
    (u x : ℂ) (hu : u ≠ 0) (hx : x ≠ 0) (hux : u.arg ≠ x.arg) :
    ccwTurn u x = 2 * Real.pi * Int.fract ((x.arg - u.arg) / (2 * Real.pi)) := by
  have hp : 0 < 2 * Real.pi := by positivity
  have huarg := Complex.arg_mem_Ioc u
  have hxarg := Complex.arg_mem_Ioc x
  change -Real.pi < u.arg ∧ u.arg ≤ Real.pi at huarg
  change -Real.pi < x.arg ∧ x.arg ≤ Real.pi at hxarg
  have hdifflo : -(2 * Real.pi) < x.arg - u.arg := by linarith
  have hdiffhi : x.arg - u.arg < 2 * Real.pi := by linarith
  by_cases hlt : u.arg < x.arg
  · let q : ℝ := (x.arg - u.arg) / (2 * Real.pi)
    have hq0 : 0 ≤ q := by
      dsimp [q]
      exact div_nonneg (le_of_lt (sub_pos.mpr hlt)) hp.le
    have hq1 : q < 1 := by
      dsimp [q]
      rw [div_lt_iff₀ hp]
      linarith
    have hfract : Int.fract q = q := Int.fract_eq_self.mpr ⟨hq0, hq1⟩
    rw [show ccwTurn u x = x.arg - u.arg by simp [ccwTurn, hlt]]
    rw [show (x.arg - u.arg) / (2 * Real.pi) = q by rfl, hfract]
    dsimp [q]
    field_simp [ne_of_gt hp]
  · have hxl : x.arg < u.arg := lt_of_le_of_ne (le_of_not_gt hlt) hux.symm
    let q : ℝ := (x.arg - u.arg) / (2 * Real.pi)
    have hqlo : -1 < q := by
      dsimp [q]
      rw [lt_div_iff₀ hp]
      linarith
    have hqhi : q < 0 := by
      dsimp [q]
      exact div_neg_of_neg_of_pos (sub_neg.mpr hxl) hp
    have hq1 : 0 ≤ q + 1 ∧ q + 1 < 1 := by constructor <;> linarith
    have hfract : Int.fract q = Int.fract (q + 1) :=
      Int.fract_eq_fract.mpr ⟨-1, by push_cast; ring⟩
    have hfract' : Int.fract (q + 1) = q + 1 :=
      Int.fract_eq_self.mpr hq1
    rw [show ccwTurn u x = x.arg - u.arg + 2 * Real.pi by
      simp [ccwTurn, not_lt_of_ge hxl.le]]
    rw [show (x.arg - u.arg) / (2 * Real.pi) = q by rfl, hfract, hfract']
    dsimp [q]
    field_simp [ne_of_gt hp]

/-- Helper toward Proposition 5.16: distinct arguments in the principal
argument interval have distinct representatives modulo one full turn. -/
theorem d39_distinct_args_have_distinct_periodic_representatives
    (a b repA repB period : ℝ) (hperiod : period = 2 * Real.pi)
    (ha : -Real.pi < a ∧ a ≤ Real.pi) (hb : -Real.pi < b ∧ b ≤ Real.pi)
    (hab : a ≠ b)
    (hrepA : ∃ k : ℤ, repA = a + period * (k : ℝ))
    (hrepB : ∃ k : ℤ, repB = b + period * (k : ℝ)) :
    repA ≠ repB := by
  intro heq
  rcases hrepA with ⟨kA, hkA⟩
  rcases hrepB with ⟨kB, hkB⟩
  have hp : 0 < 2 * Real.pi := by positivity
  have hsum : a + (2 * Real.pi) * (kA : ℝ) =
      b + (2 * Real.pi) * (kB : ℝ) := by
    calc
      a + (2 * Real.pi) * (kA : ℝ) = a + period * (kA : ℝ) := by rw [hperiod]
      _ = repA := hkA.symm
      _ = repB := heq
      _ = b + period * (kB : ℝ) := hkB
      _ = b + (2 * Real.pi) * (kB : ℝ) := by rw [hperiod]
  have hdifflo : -(2 * Real.pi) < a - b := by linarith [ha.1, hb.2]
  have hdiffhi : a - b < 2 * Real.pi := by linarith [ha.2, hb.1]
  have hdiff : a - b = (2 * Real.pi) * ((kB - kA : ℤ) : ℝ) := by
    push_cast at hsum ⊢
    nlinarith [hsum]
  have hklo : (-1 : ℝ) < ((kB - kA : ℤ) : ℝ) := by
    have hh := div_lt_div_of_pos_right hdifflo hp
    rw [hdiff] at hh
    field_simp [ne_of_gt hp] at hh
    linarith
  have hkhi : ((kB - kA : ℤ) : ℝ) < 1 := by
    have hh := div_lt_div_of_pos_right hdiffhi hp
    rw [hdiff] at hh
    field_simp [ne_of_gt hp] at hh
    linarith
  have hkzlo : (-1 : ℤ) < kB - kA := by exact_mod_cast hklo
  have hkzhi : kB - kA < (1 : ℤ) := by exact_mod_cast hkhi
  have hkzero : kB - kA = 0 := by omega
  apply hab
  have hzero : a - b = 0 := by rw [hdiff, hkzero]; ring
  linarith

/-- Helper toward Proposition 5.16: the image turn comparison is exactly the
cyclic order of the lifted ray representatives in one turn. -/
theorem d39_image_ccwTurn_lt_iff_cyclicOrder
    (u' v' w' : ℂ) (L : C(unitInterval, ℝ))
    (hu' : u' ≠ 0) (hv' : v' ≠ 0) (hw' : w' ≠ 0)
    (repU repV repW : ℝ) (tU tV tW : unitInterval) (period L0 : ℝ)
    (hperiod : 0 < period) (hperiodEq : period = 2 * Real.pi)
    (hend : L 1 = L 0 + period)
    (huv' : u'.arg ≠ v'.arg) (huw' : u'.arg ≠ w'.arg)
    (hvw' : v'.arg ≠ w'.arg)
    (hrepU : ∃ k : ℤ, repU = u'.arg + period * (k : ℝ))
    (hrepV : ∃ k : ℤ, repV = v'.arg + period * (k : ℝ))
    (hrepW : ∃ k : ℤ, repW = w'.arg + period * (k : ℝ))
    (hwindow : L 0 < repU ∧ repU < L 0 + period ∧
      L 0 < repV ∧ repV < L 0 + period ∧
      L 0 < repW ∧ repW < L 0 + period)
    (hU : ∀ t : unitInterval, (∃ k : ℤ, L t = u'.arg + period * (k : ℝ)) ↔ t = tU)
    (hV : ∀ t : unitInterval, (∃ k : ℤ, L t = v'.arg + period * (k : ℝ)) ↔ t = tV)
    (hW : ∀ t : unitInterval, (∃ k : ℤ, L t = w'.arg + period * (k : ℝ)) ↔ t = tW) :
    ccwTurn u' w' < ccwTurn u' v' ↔
      d39CyclicOrder ((repU - L 0) / period)
        ((repW - L 0) / period) ((repV - L 0) / period) := by
  have hp : 0 < 2 * Real.pi := by positivity
  rcases hrepU with ⟨kU, hkU⟩
  rcases hrepV with ⟨kV, hkV⟩
  rcases hrepW with ⟨kW, hkW⟩
  have huarg := Complex.arg_mem_Ioc u'
  have hvarg := Complex.arg_mem_Ioc v'
  have hwarg := Complex.arg_mem_Ioc w'
  change -Real.pi < u'.arg ∧ u'.arg ≤ Real.pi at huarg
  change -Real.pi < v'.arg ∧ v'.arg ≤ Real.pi at hvarg
  change -Real.pi < w'.arg ∧ w'.arg ≤ Real.pi at hwarg
  let a : ℝ := (repU - L 0) / period
  let b : ℝ := (repW - L 0) / period
  let c : ℝ := (repV - L 0) / period
  rcases hwindow with ⟨hUlo, hUhi, hVlo, hVhi, hWlo, hWhi⟩
  have ha0 : 0 ≤ a := by dsimp [a]; exact div_nonneg (sub_nonneg.mpr hUlo.le) hperiod.le
  have ha1 : a < 1 := by dsimp [a]; rw [div_lt_iff₀ hperiod]; linarith
  have hb0 : 0 ≤ b := by dsimp [b]; exact div_nonneg (sub_nonneg.mpr hWlo.le) hperiod.le
  have hb1 : b < 1 := by dsimp [b]; rw [div_lt_iff₀ hperiod]; linarith
  have hc0 : 0 ≤ c := by dsimp [c]; exact div_nonneg (sub_nonneg.mpr hVlo.le) hperiod.le
  have hc1 : c < 1 := by dsimp [c]; rw [div_lt_iff₀ hperiod]; linarith
  have hrepUW : repU ≠ repW := d39_distinct_args_have_distinct_periodic_representatives
    u'.arg w'.arg repU repW period hperiodEq huarg hwarg huw' ⟨kU, hkU⟩
    ⟨kW, hkW⟩
  have hrepUV : repU ≠ repV := d39_distinct_args_have_distinct_periodic_representatives
    u'.arg v'.arg repU repV period hperiodEq huarg hvarg huv' ⟨kU, hkU⟩
    ⟨kV, hkV⟩
  have hrepWV : repW ≠ repV := d39_distinct_args_have_distinct_periodic_representatives
    w'.arg v'.arg repW repV period hperiodEq hwarg hvarg (Ne.symm hvw')
    ⟨kW, hkW⟩ ⟨kV, hkV⟩
  have hab : a ≠ b := by
    intro heq
    apply hrepUW
    have hmul := (div_left_inj' (ne_of_gt hperiod)).mp (by simpa [a, b] using heq)
    linarith
  have hac : a ≠ c := by
    intro heq
    apply hrepUV
    have hmul := (div_left_inj' (ne_of_gt hperiod)).mp (by simpa [a, c] using heq)
    linarith
  have hbc : b ≠ c := by
    intro heq
    apply hrepWV
    have hmul := (div_left_inj' (ne_of_gt hperiod)).mp (by simpa [b, c] using heq)
    linarith
  have hfractW : Int.fract ((w'.arg - u'.arg) / (2 * Real.pi)) =
      Int.fract ((repW - repU) / (2 * Real.pi)) := by
    apply Int.fract_eq_fract.mpr
    refine ⟨kU - kW, ?_⟩
    rw [hkW, hkU, hperiodEq]
    push_cast
    field_simp [ne_of_gt hp]
    ring
  have hfractV : Int.fract ((v'.arg - u'.arg) / (2 * Real.pi)) =
      Int.fract ((repV - repU) / (2 * Real.pi)) := by
    apply Int.fract_eq_fract.mpr
    refine ⟨kU - kV, ?_⟩
    rw [hkV, hkU, hperiodEq]
    push_cast
    field_simp [ne_of_gt hp]
    ring
  have hturnW := d39_ccwTurn_eq_twoPi_mul_fract_arg_diff u' w' hu' hw' huw'
  have hturnV := d39_ccwTurn_eq_twoPi_mul_fract_arg_diff u' v' hu' hv' huv'
  have hdiffW : b - a = (repW - repU) / (2 * Real.pi) := by
    dsimp [a, b]
    rw [hperiodEq]
    field_simp [ne_of_gt hp]
    ring
  have hdiffV : c - a = (repV - repU) / (2 * Real.pi) := by
    dsimp [a, c]
    rw [hperiodEq]
    field_simp [ne_of_gt hp]
    ring
  have hcompare : ccwTurn u' w' < ccwTurn u' v' ↔
      Int.fract (b - a) < Int.fract (c - a) := by
    rw [hturnW, hturnV, hfractW, hfractV, ← hdiffW, ← hdiffV]
    constructor <;> intro h <;> nlinarith [hp]
  rw [hcompare]
  exact (d39_fract_sub_lt_iff_cyclicOrder a b c ha0 ha1 hb0 hb1 hc0 hc1
    hab hac hbc)






















































end DirectedDistances.PlanarMap

end
