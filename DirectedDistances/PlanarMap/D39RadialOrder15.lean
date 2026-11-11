/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39RadialOrder14

/-! Helper toward Proposition 5.16: transfer the argument-lattice hit order
to the order of the corresponding path parameters. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16: two representatives in one period of a
continuous lift occur in the same order as their unique lattice-hit times. -/
theorem d39_image_lift_lattice_hit_times_order
    (L : C(unitInterval, ℝ)) (a b aRep bRep period : ℝ)
    (ta tb : unitInterval)
    (hperiod : 0 < period)
    (hrepA : ∃ m : ℤ, aRep = a + period * (m : ℝ))
    (hrepB : ∃ m : ℤ, bRep = b + period * (m : ℝ))
    (hwindow : L 0 < aRep ∧ aRep < bRep ∧ bRep < L 0 + period)
    (hend : L 1 = L 0 + period)
    (haUnique : ∀ t : unitInterval,
      (∃ k : ℤ, L t = a + period * (k : ℝ)) ↔ t = ta)
    (hbUnique : ∀ t : unitInterval,
      (∃ k : ℤ, L t = b + period * (k : ℝ)) ↔ t = tb) :
    (ta : ℝ) < (tb : ℝ) := by
  exact d39_continuous_lift_lattice_hits_order L a b aRep bRep period ta tb
    hperiod hrepA hrepB hwindow hend haUnique hbUnique

/-- Helper toward Proposition 5.16: away from the base ray, the exposed
ray-hit characterization gives its normalized fractional-part formula. -/
theorem d39_rotatedCircleRayHitTime_eq_fract_of_miss
    (α : ℝ) (a : ℂ)
    (hmiss : ∀ k : ℤ, a.arg ≠ α + 2 * Real.pi * (k : ℝ)) :
    d39RotatedCircleRayHitTime α a =
      Int.fract ((a.arg - α) / (2 * Real.pi)) := by
  let x := (a.arg - α) / (2 * Real.pi)
  have hperiod : 0 < 2 * Real.pi := by positivity
  have hnonneg : 0 ≤ Int.fract x := Int.fract_nonneg x
  have hlt : Int.fract x < 1 := Int.fract_lt_one x
  have hpos : 0 < Int.fract x := by
    by_contra hnot
    have hzero : Int.fract x = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
    have hx : x = (⌊x⌋ : ℝ) := by
      change x - (⌊x⌋ : ℝ) = 0 at hzero
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
  have hmul : 2 * Real.pi * x = a.arg - α := by
    dsimp [x]
    field_simp
  have hcast : ((-⌊x⌋ : ℤ) : ℝ) = - (⌊x⌋ : ℝ) := by push_cast; ring
  have hfract : Int.fract x = x - (⌊x⌋ : ℝ) := Int.self_sub_floor x
  have hphase : a.arg + 2 * Real.pi * ((-⌊x⌋ : ℤ) : ℝ) =
      α + 2 * Real.pi * Int.fract x := by
    calc
      a.arg + 2 * Real.pi * ((-⌊x⌋ : ℤ) : ℝ) =
          α + 2 * Real.pi * (x - (⌊x⌋ : ℝ)) := by
        rw [hcast]
        nlinarith [hmul]
      _ = α + 2 * Real.pi * Int.fract x := by rw [← hfract]
  have hlower : α < a.arg + 2 * Real.pi * ((-⌊x⌋ : ℤ) : ℝ) := by
    rw [hphase]
    nlinarith [hpos, hperiod]
  have hupper : a.arg + 2 * Real.pi * ((-⌊x⌋ : ℤ) : ℝ) < α + 2 * Real.pi := by
    rw [hphase]
    nlinarith [hlt, hperiod]
  rw [d39_rotatedCircleRayHitTime_eq_of_lift α a (-⌊x⌋) hlower hupper]
  rw [hphase]
  dsimp [x]
  field_simp [ne_of_gt hperiod]
  ring


































































end DirectedDistances.PlanarMap

end
