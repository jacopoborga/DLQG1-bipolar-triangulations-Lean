/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39RadialOrder5
import DirectedDistances.PaperProofs.Section3.D39GeomMirror

/-! # Three-ray short turns and winding

Helpers toward Proposition 5.16. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open scoped ComplexConjugate

/-- Helper toward Proposition 5.16: a counterclockwise turn at most `pi`
has a nonnegative oriented determinant, including at both endpoints. -/
theorem d39_det_nonneg_of_ccwTurn_le_pi (u x : ℂ) (_hu : u ≠ 0) (_hx : x ≠ 0)
    (hpi : ccwTurn u x ≤ Real.pi) :
    0 ≤ (conj u * x).im := by
  rw [d39_det_eq_norm_mul_sin_ccwTurn]
  exact mul_nonneg (mul_nonneg (norm_nonneg u) (norm_nonneg x))
    (Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt (ccwTurn_pos u x)) hpi)

/-- Helper toward Proposition 5.16: if no closed half-plane contains three
nonzero rays and their positive cyclic turn sum is `2 * pi`, then each
successive turn is strictly less than `pi`. -/
theorem d39_cyclic_short_turns_of_no_closed_halfPlane
    (u v w : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : u.arg ≠ v.arg) (huw : u.arg ≠ w.arg) (hvw : v.arg ≠ w.arg)
    (hno : ∀ n : ℂ, n ≠ 0 →
      ¬ (0 ≤ (conj n * u).re ∧ 0 ≤ (conj n * v).re ∧
        0 ≤ (conj n * w).re))
    (hsum : ccwTurn u v + ccwTurn v w + ccwTurn w u = 2 * Real.pi) :
    0 < ccwTurn u v ∧ ccwTurn u v < Real.pi ∧
      0 < ccwTurn v w ∧ ccwTurn v w < Real.pi ∧
      0 < ccwTurn w u ∧ ccwTurn w u < Real.pi := by
  have hfirst (a b c : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
      (hab : a.arg ≠ b.arg) (hbc : b.arg ≠ c.arg) (hca : c.arg ≠ a.arg)
      (hno' : ∀ n : ℂ, n ≠ 0 →
        ¬ (0 ≤ (conj n * a).re ∧ 0 ≤ (conj n * b).re ∧
          0 ≤ (conj n * c).re))
      (hsum' : ccwTurn a b + ccwTurn b c + ccwTurn c a = 2 * Real.pi) :
      ccwTurn a b < Real.pi := by
    by_contra hnot
    have hlarge : Real.pi ≤ ccwTurn a b := le_of_not_gt hnot
    have hrev := ccwTurn_add_reverse a b hab
    have hcomplement : ccwTurn b c + ccwTurn c a = ccwTurn b a := by
      linarith
    have hbcSmall : ccwTurn b c ≤ Real.pi := by
      linarith [ccwTurn_pos c a]
    have hbaSmall : ccwTurn b a ≤ Real.pi := by
      linarith [ccwTurn_pos b c]
    let n : ℂ := Complex.I * b
    have hn : n ≠ 0 := mul_ne_zero Complex.I_ne_zero hb
    have hnormal (z : ℂ) : (conj n * z).re = (conj b * z).im := by
      simp only [n, map_mul, Complex.conj_I, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im,
        Complex.I_re, Complex.I_im]
      ring
    have hda : 0 ≤ (conj n * a).re := by
      rw [hnormal]
      exact d39_det_nonneg_of_ccwTurn_le_pi b a hb ha hbaSmall
    have hdb : 0 ≤ (conj n * b).re := by
      rw [hnormal]
      have hbzero : (conj b * b).im = 0 := by
        simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
        ring
      rw [hbzero]
    have hdc : 0 ≤ (conj n * c).re := by
      rw [hnormal]
      exact d39_det_nonneg_of_ccwTurn_le_pi b c hb hc hbcSmall
    exact (hno' n hn) ⟨hda, hdb, hdc⟩
  have hUV := hfirst u v w hu hv hw huv hvw (Ne.symm huw) hno hsum
  have hnoVW : ∀ n : ℂ, n ≠ 0 →
      ¬ (0 ≤ (conj n * v).re ∧ 0 ≤ (conj n * w).re ∧
        0 ≤ (conj n * u).re) := by
    intro n hn h
    exact hno n hn ⟨h.2.2, h.1, h.2.1⟩
  have hsumVW : ccwTurn v w + ccwTurn w u + ccwTurn u v = 2 * Real.pi := by
    calc
      ccwTurn v w + ccwTurn w u + ccwTurn u v =
          ccwTurn u v + ccwTurn v w + ccwTurn w u := by ring
      _ = 2 * Real.pi := hsum
  have hVW := hfirst v w u hv hw hu hvw (Ne.symm huw) huv hnoVW hsumVW
  have hnoWU : ∀ n : ℂ, n ≠ 0 →
      ¬ (0 ≤ (conj n * w).re ∧ 0 ≤ (conj n * u).re ∧
        0 ≤ (conj n * v).re) := by
    intro n hn h
    exact hno n hn ⟨h.2.1, h.2.2, h.1⟩
  have hsumWU : ccwTurn w u + ccwTurn u v + ccwTurn v w = 2 * Real.pi := by
    calc
      ccwTurn w u + ccwTurn u v + ccwTurn v w =
          ccwTurn u v + ccwTurn v w + ccwTurn w u := by ring
      _ = 2 * Real.pi := hsum
  have hWU := hfirst w u v hw hu hv (Ne.symm huw) huv hvw hnoWU hsumWU
  exact ⟨ccwTurn_pos u v, hUV, ccwTurn_pos v w, hVW,
    ccwTurn_pos w u, hWU⟩

/-- Helper toward Proposition 5.16: the no-half-plane condition makes the
origin strictly left of every side of every positively scaled cyclic ray
triangle. -/
theorem d39_scaled_cyclicTriangle_leftSides_of_no_closed_halfPlane
    (u v w : ℂ) (ε : ℝ) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : u.arg ≠ v.arg) (huw : u.arg ≠ w.arg) (hvw : v.arg ≠ w.arg)
    (hε : 0 < ε)
    (hno : ∀ n : ℂ, n ≠ 0 →
      ¬ (0 ≤ (conj n * u).re ∧ 0 ≤ (conj n * v).re ∧
        0 ≤ (conj n * w).re))
    (hsum : ccwTurn u v + ccwTurn v w + ccwTurn w u = 2 * Real.pi) :
    0 < (conj ((ε : ℂ) * v - (ε : ℂ) * u) * (0 - (ε : ℂ) * u)).im ∧
    0 < (conj ((ε : ℂ) * w - (ε : ℂ) * v) * (0 - (ε : ℂ) * v)).im ∧
    0 < (conj ((ε : ℂ) * u - (ε : ℂ) * w) * (0 - (ε : ℂ) * w)).im := by
  rcases d39_cyclic_short_turns_of_no_closed_halfPlane u v w hu hv hw
      huv huw hvw hno hsum with
    ⟨huvPos, huvPi, hvwPos, hvwPi, hwuPos, hwuPi⟩
  exact d39_scaled_cyclicTriangle_leftSides_of_short_turns u v w ε hu hv hw hε
    huvPos huvPi hvwPos hvwPi hwuPos hwuPi

/-- Helper toward Proposition 5.16: conjugation reverses the direction of a
turn between distinct rays. -/
theorem d39_ccwTurn_conj {a b : ℂ} (hab : a.arg ≠ b.arg) :
    ccwTurn (conj a) (conj b) = ccwTurn b a := by
  by_cases ha : a.arg = Real.pi
  · have hb : b.arg ≠ Real.pi := by
      intro h
      exact hab (ha.trans h.symm)
    have hbπ : b.arg < Real.pi := lt_of_le_of_ne (Complex.arg_le_pi b) hb
    have hcut : ¬ Real.pi < -b.arg := by
      have hlow := Complex.neg_pi_lt_arg b
      linarith
    simp [ccwTurn, Complex.arg_conj, ha, hb, hbπ, hcut]
    ring
  · by_cases hb : b.arg = Real.pi
    · have haπ : a.arg < Real.pi := lt_of_le_of_ne (Complex.arg_le_pi a) ha
      have hnot : ¬ Real.pi < a.arg := not_lt_of_ge haπ.le
      have hcut : -a.arg < Real.pi := by
        have hlow := Complex.neg_pi_lt_arg a
        linarith
      simp [ccwTurn, Complex.arg_conj, ha, hb, hnot, hcut]
      ring
    · by_cases hba : b.arg < a.arg
      · have hab' : ¬ a.arg < b.arg := not_lt_of_gt hba
        have hcut : -a.arg < -b.arg := neg_lt_neg hba
        simp [ccwTurn, Complex.arg_conj, ha, hb, hba, hcut]
        ring
      · have hab' : a.arg < b.arg :=
          lt_of_le_of_ne (le_of_not_gt hba) hab
        have hcut : ¬ -a.arg < -b.arg := by
          simpa only [neg_lt_neg_iff] using hba
        simp [ccwTurn, Complex.arg_conj, ha, hb, hba, hcut]
        ring

/-- Helper toward Proposition 5.16: pointwise, conjugating the three-vertex
polyline path applies conjugation to each vertex in order. -/
theorem d39_cyclicTriangle_path_map_conj_apply (a b c : ℂ) (t : unitInterval) :
    (((d39CyclicTrianglePolyline a b c).toPath.cast rfl
      (d39CyclicTrianglePolyline_closed a b c)).map Complex.continuous_conj) t =
      ((d39CyclicTrianglePolyline (conj a) (conj b) (conj c)).toPath.cast rfl
        (d39CyclicTrianglePolyline_closed (conj a) (conj b) (conj c))) t := by
  change conj (((Path.segment a b).trans
      ((Path.segment b c).trans (Path.segment c a))) t) =
    (((Path.segment (conj a) (conj b)).trans
      ((Path.segment (conj b) (conj c)).trans
        (Path.segment (conj c) (conj a)))) t)
  have hsegment (x y : ℂ) (s : unitInterval) :
      conj ((Path.segment x y) s) = (Path.segment (conj x) (conj y)) s := by
    simp [Path.segment_apply, AffineMap.lineMap_apply_module,
      RCLike.real_smul_eq_coe_mul]
  simp only [Path.trans_apply]
  split_ifs <;> simp only [hsegment]

/-- Helper toward Proposition 5.16: the positively ordered ray triangle has
winding one, and reversing its order has winding minus one, under the
no-closed-half-plane condition. -/
theorem d39_scaled_cyclicTriangle_hasWinding_pair_of_no_closed_halfPlane
    (u v w : ℂ) (ε : ℝ) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : u.arg ≠ v.arg) (huw : u.arg ≠ w.arg) (hvw : v.arg ≠ w.arg)
    (hε : 0 < ε)
    (hno : ∀ n : ℂ, n ≠ 0 →
      ¬ (0 ≤ (conj n * u).re ∧ 0 ≤ (conj n * v).re ∧
        0 ≤ (conj n * w).re))
    (hsum : ccwTurn u v + ccwTurn v w + ccwTurn w u = 2 * Real.pi) :
    HasWinding
      ((d39CyclicTrianglePolyline ((ε : ℂ) * u) ((ε : ℂ) * v)
        ((ε : ℂ) * w)).toPath.cast rfl
        (d39CyclicTrianglePolyline_closed _ _ _)) 0 1 ∧
    HasWinding
      ((d39CyclicTrianglePolyline ((ε : ℂ) * u) ((ε : ℂ) * w)
        ((ε : ℂ) * v)).toPath.cast rfl
        (d39CyclicTrianglePolyline_closed _ _ _)) 0 (-1 : ℤ) := by
  rcases d39_cyclic_short_turns_of_no_closed_halfPlane u v w hu hv hw
      huv huw hvw hno hsum with
    ⟨huvPos, huvPi, hvwPos, hvwPi, hwuPos, hwuPi⟩
  refine ⟨d39_scaled_cyclicTriangle_hasWinding_one_of_short_turns u v w ε
    hu hv hw hε huvPos huvPi hvwPos hvwPi hwuPos hwuPi, ?_⟩
  have hcu : conj u ≠ 0 := by
    intro h
    apply hu
    simpa using congrArg conj h
  have hcv : conj v ≠ 0 := by
    intro h
    apply hv
    simpa using congrArg conj h
  have hcw : conj w ≠ 0 := by
    intro h
    apply hw
    simpa using congrArg conj h
  have hturn0 : 0 < ccwTurn (conj u) (conj w) := by
    rw [d39_ccwTurn_conj huw]
    exact hwuPos
  have hturn0π : ccwTurn (conj u) (conj w) < Real.pi := by
    rw [d39_ccwTurn_conj huw]
    exact hwuPi
  have hturn1 : 0 < ccwTurn (conj w) (conj v) := by
    rw [d39_ccwTurn_conj (Ne.symm hvw)]
    exact hvwPos
  have hturn1π : ccwTurn (conj w) (conj v) < Real.pi := by
    rw [d39_ccwTurn_conj (Ne.symm hvw)]
    exact hvwPi
  have hturn2 : 0 < ccwTurn (conj v) (conj u) := by
    rw [d39_ccwTurn_conj (Ne.symm huv)]
    exact huvPos
  have hturn2π : ccwTurn (conj v) (conj u) < Real.pi := by
    rw [d39_ccwTurn_conj (Ne.symm huv)]
    exact huvPi
  let L : Path ((ε : ℂ) * conj u) ((ε : ℂ) * conj u) :=
    (d39CyclicTrianglePolyline ((ε : ℂ) * conj u) ((ε : ℂ) * conj w)
      ((ε : ℂ) * conj v)).toPath.cast rfl
      (d39CyclicTrianglePolyline_closed _ _ _)
  have hpositive : HasWinding L 0 1 :=
    d39_scaled_cyclicTriangle_hasWinding_one_of_short_turns
      (conj u) (conj w) (conj v) ε hcu hcw hcv hε
      hturn0 hturn0π hturn1 hturn1π hturn2 hturn2π
  have hcu' : conj ((ε : ℂ) * conj u) = (ε : ℂ) * u := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
  have hcw' : conj ((ε : ℂ) * conj w) = (ε : ℂ) * w := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
  have hcv' : conj ((ε : ℂ) * conj v) = (ε : ℂ) * v := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
  have hpath (t : unitInterval) : (L.map Complex.continuous_conj) t =
      ((d39CyclicTrianglePolyline ((ε : ℂ) * u) ((ε : ℂ) * w)
        ((ε : ℂ) * v)).toPath.cast rfl
        (d39CyclicTrianglePolyline_closed _ _ _)) t := by
    change (L.map Complex.continuous_conj) t =
      (d39CyclicTrianglePolyline ((ε : ℂ) * u) ((ε : ℂ) * w)
        ((ε : ℂ) * v)).toPath t
    dsimp [L]
    have h := d39_cyclicTriangle_path_map_conj_apply
      ((ε : ℂ) * conj u) ((ε : ℂ) * conj w) ((ε : ℂ) * conj v) t
    rw [hcu', hcw', hcv'] at h
    exact h
  have hnegative : HasWinding (L.map Complex.continuous_conj) 0 (-1 : ℤ) := by
    have h := (hasWinding_conj_iff L 0 1).2 hpositive
    simpa using h
  obtain ⟨φ, hφ, hinc⟩ := hnegative
  refine ⟨φ, ?_, hinc⟩
  intro t
  rw [← hpath t]
  exact hφ t


end DirectedDistances.PlanarMap

end
