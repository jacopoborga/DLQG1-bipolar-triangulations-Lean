/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39RadialOrder4






public section

noncomputable section

namespace DirectedDistances.PlanarMap

open scoped ComplexConjugate

/-- Helper toward Proposition 5.16: if each consecutive cyclic turn is
strictly less than `pi`, the origin is strictly left of all three sides of
every positively scaled ray triangle. -/
theorem d39_scaled_cyclicTriangle_leftSides_of_short_turns
    (u v w : ℂ) (ε : ℝ) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hε : 0 < ε)
    (huv : 0 < ccwTurn u v) (huvπ : ccwTurn u v < Real.pi)
    (hvw : 0 < ccwTurn v w) (hvwπ : ccwTurn v w < Real.pi)
    (hwu : 0 < ccwTurn w u) (hwuπ : ccwTurn w u < Real.pi) :
    0 < (conj ((ε : ℂ) * v - (ε : ℂ) * u) * (0 - (ε : ℂ) * u)).im ∧
    0 < (conj ((ε : ℂ) * w - (ε : ℂ) * v) * (0 - (ε : ℂ) * v)).im ∧
    0 < (conj ((ε : ℂ) * u - (ε : ℂ) * w) * (0 - (ε : ℂ) * w)).im := by
  have huvdet := d39_det_pos_of_ccwTurn_lt_pi u v hu hv huv huvπ
  have hvwdet := d39_det_pos_of_ccwTurn_lt_pi v w hv hw hvw hvwπ
  have hwudet := d39_det_pos_of_ccwTurn_lt_pi w u hw hu hwu hwuπ
  have hscale (a b : ℂ) :
      (conj ((ε : ℂ) * b - (ε : ℂ) * a) *
        (0 - (ε : ℂ) * a)).im = ε ^ 2 * (conj a * b).im := by
    simp only [map_sub, map_mul, Complex.conj_ofReal, zero_sub,
      Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hscale]
    exact mul_pos (sq_pos_of_pos hε) huvdet
  · rw [hscale]
    exact mul_pos (sq_pos_of_pos hε) hvwdet
  · rw [hscale]
    exact mul_pos (sq_pos_of_pos hε) hwudet

/-- Helper toward Proposition 5.16: a positively ordered ray triangle has
winding one whenever its three directed sides have the origin strictly left. -/
theorem d39_scaled_cyclicTriangle_hasWinding_one_of_short_turns
    (u v w : ℂ) (ε : ℝ) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hε : 0 < ε)
    (huv : 0 < ccwTurn u v) (huvπ : ccwTurn u v < Real.pi)
    (hvw : 0 < ccwTurn v w) (hvwπ : ccwTurn v w < Real.pi)
    (hwu : 0 < ccwTurn w u) (hwuπ : ccwTurn w u < Real.pi) :
    HasWinding
      ((d39CyclicTrianglePolyline ((ε : ℂ) * u) ((ε : ℂ) * v)
        ((ε : ℂ) * w)).toPath.cast rfl
        (d39CyclicTrianglePolyline_closed _ _ _)) 0 1 := by
  rcases d39_scaled_cyclicTriangle_leftSides_of_short_turns u v w ε hu hv hw
      hε huv huvπ hvw hvwπ hwu hwuπ with ⟨h0, h1, h2⟩
  exact d39_cyclicTriangle_hasWinding_one_of_leftSides _ _ _ 0 h0 h1 h2

/-- Helper toward Proposition 5.16: the cyclic turn-sum characterization
turns a positive cyclic order into an explicit strict-betweenness inequality. -/
theorem d39_positive_cyclic_order_iff_turn_betweenness
    {u v w : ℂ} (huv : u.arg ≠ v.arg) (huw : u.arg ≠ w.arg)
    (hvw : v.arg ≠ w.arg) :
    ccwTurn u v + ccwTurn v w + ccwTurn w u = 2 * Real.pi ↔
      ccwTurn u v < ccwTurn u w :=
  d39_cyclic_turn_sum_eq_two_pi_iff_ordered huv huw hvw





































































































end DirectedDistances.PlanarMap

end
