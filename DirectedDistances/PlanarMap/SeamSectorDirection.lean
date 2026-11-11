/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlaneRealization

/-! # Initial directions at a seam vertex

Helpers toward Theorem 1.4 (Q-M0-repr drawing: angular sectors at seam vertices);
not a paper result. -/

public section
namespace DirectedDistances.PlanarMap

open Set

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: angular sectors at seam vertices);
not a paper result. A short point on the first segment lies in the polyline interior. -/
private theorem exists_small_interior_point (p : Polyline) (x0 y0 : ℝ)
    (hs : p.start = (⟨x0, y0⟩ : ℂ)) (hlen : 2 ≤ p.points.length)
    (hne : p.initialDirection ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t : ℝ, 0 < t ∧ t < δ ∧
      p.start + t • p.initialDirection ∈ p.interior := by
  let q : ℝ → ℂ := fun t => p.start + t • p.initialDirection
  have hp0 : p.point 0 = p.start := by
    cases p with
    | mk points hpoints =>
      cases points with
      | nil => exact False.elim (hpoints rfl)
      | cons a rest => rfl
  have hline (t : ℝ) :
      q t = AffineMap.lineMap p.start (p.point 1) t := by
    rw [AffineMap.lineMap_apply_module']
    dsimp [q]
    simp only [Polyline.initialDirection]
    abel
  have hseg (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      q t ∈ p.segmentAt 0 := by
    change q t ∈ segment ℝ (p.point 0) (p.point 1)
    rw [hp0, hline]
    exact lineMap_mem_segment ℝ p.start (p.point 1) ⟨ht0, ht1⟩
  have himage (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : q t ∈ p.image := by
    change q t ∈ {p.start} ∪ {z | ∃ i, i + 1 < p.points.length ∧
      z ∈ p.segmentAt i}
    right
    refine ⟨0, ?_, hseg t ht0 ht1⟩
    omega
  have hneStart (t : ℝ) (ht : 0 < t) : q t ≠ p.start := by
    intro h
    have hmul : (t : ℂ) * p.initialDirection = 0 := by
      dsimp [q] at h
      have h' : p.start + (t : ℂ) * p.initialDirection = p.start + 0 := by
        simpa using h
      exact add_left_cancel h'
    have htne : t ≠ 0 := ne_of_gt ht
    have hct : (t : ℂ) ≠ 0 := by exact_mod_cast htne
    exact (mul_ne_zero hct hne) hmul
  let m := min δ 1
  have hm : 0 < m := lt_min hδ zero_lt_one
  let a := m / 2
  let b := m / 4
  have ha : 0 < a ∧ a < δ ∧ a < 1 := by
    dsimp [a, m]
    constructor
    · exact half_pos hm
    constructor
    · exact (half_lt_self hm).trans_le (min_le_left _ _)
    · exact (half_lt_self hm).trans_le (min_le_right _ _)
  have hb : 0 < b ∧ b < δ ∧ b < 1 := by
    dsimp [b, m]
    constructor
    · positivity
    constructor
    · have hlt : min δ 1 / 4 < min δ 1 / 2 := by nlinarith [hm]
      exact hlt.trans ha.2.1
    · have hlt : min δ 1 / 4 < min δ 1 / 2 := by nlinarith [hm]
      exact hlt.trans ha.2.2
  have hab : q a ≠ q b := by
    intro h
    have hmul : (a : ℂ) * p.initialDirection =
        (b : ℂ) * p.initialDirection := by
      have h' := congrArg (fun z : ℂ => z - p.start) h
      dsimp [q] at h'
      simpa only [add_sub_cancel_left] using h'
    have hneab : a - b ≠ 0 := by
      dsimp [a, b]
      nlinarith [hm]
    have hcast : (a : ℂ) = b := mul_right_cancel₀ hne hmul
    have hab' : a = b := by exact_mod_cast hcast
    exact hneab (sub_eq_zero.mpr hab')
  by_cases hfinish : q a = p.finish
  · refine ⟨b, hb.1, hb.2.1, ?_⟩
    rw [Polyline.interior, Set.mem_sdiff]
    refine ⟨himage b (le_of_lt hb.1) (le_of_lt hb.2.2), ?_⟩
    intro h
    rcases Set.mem_insert_iff.mp h with hs' | hf'
    · exact (hneStart b hb.1) hs'
    · exact hab (hfinish.trans hf'.symm)
  · refine ⟨a, ha.1, ha.2.1, ?_⟩
    rw [Polyline.interior, Set.mem_sdiff]
    refine ⟨himage a (le_of_lt ha.1) (le_of_lt ha.2.2), ?_⟩
    intro h
    rcases Set.mem_insert_iff.mp h with hs' | hf'
    · exact (hneStart a ha.1) hs'
    · exact hfinish hf'

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: angular sectors at seam vertices);
not a paper result. Interior directions lie strictly above the local affine seam. -/
theorem initialDirection_above_graph (f : ℝ → ℝ) (x0 r sL sR : ℝ)
    (hr : 0 < r)
    (hR : ∀ x ∈ Icc x0 (x0 + r), f x = f x0 + sR * (x - x0))
    (hL : ∀ x ∈ Icc (x0 - r) x0, f x = f x0 + sL * (x - x0))
    (p : Polyline) (hs : p.start = (⟨x0, f x0⟩ : ℂ))
    (hlen : 2 ≤ p.points.length) (hne : p.point 1 ≠ p.start)
    (habove : ∀ z ∈ p.interior, f z.re < z.im) :
    let u := p.initialDirection
    (0 < u.re → sR * u.re < u.im) ∧
      (u.re < 0 → sL * u.re < u.im) ∧
      (u.re = 0 → 0 < u.im) := by
  dsimp only
  have hu : p.initialDirection ≠ 0 := by
    intro h
    have hp1 : p.point 1 - p.start = 0 := by
      simpa [Polyline.initialDirection] using h
    exact hne (sub_eq_zero.mp hp1)
  have hqre (t : ℝ) :
      (p.start + t • p.initialDirection).re = x0 + t * p.initialDirection.re := by
    rw [hs]
    simp
  have hqim (t : ℝ) :
      (p.start + t • p.initialDirection).im = f x0 + t * p.initialDirection.im := by
    rw [hs]
    simp
  constructor
  · intro hright
    let δ := min 1 (r / p.initialDirection.re)
    have hδ : 0 < δ := by
      dsimp [δ]
      exact lt_min zero_lt_one (div_pos hr hright)
    obtain ⟨t, ht, htδ, hinter⟩ :=
      exists_small_interior_point p x0 (f x0) hs hlen hu hδ
    have htmin : t < min 1 (r / p.initialDirection.re) := by
      simpa [δ] using htδ
    have htr : t < r / p.initialDirection.re := by
      exact (lt_min_iff.mp htmin).2
    have hprod : t * p.initialDirection.re < r :=
      (lt_div_iff₀ hright).mp htr
    have hx : x0 + t * p.initialDirection.re ∈ Icc x0 (x0 + r) := by
      constructor <;> nlinarith [mul_pos ht hright]
    have hf := hR _ hx
    have hab := habove _ hinter
    rw [hqre t, hqim t] at hab
    have hineq : f x0 + sR * (t * p.initialDirection.re) <
        f x0 + t * p.initialDirection.im := by
      calc
        f x0 + sR * (t * p.initialDirection.re) =
            f (x0 + t * p.initialDirection.re) := by rw [hf]; congr 1; ring
        _ < f x0 + t * p.initialDirection.im := hab
    have hmul : t * (sR * p.initialDirection.re) <
        t * p.initialDirection.im := by nlinarith [hineq]
    exact lt_of_mul_lt_mul_left hmul ht.le
  constructor
  · intro hleft
    let δ := min 1 (r / (-p.initialDirection.re))
    have hδ : 0 < δ := by
      dsimp [δ]
      exact lt_min zero_lt_one (div_pos hr (neg_pos.mpr hleft))
    obtain ⟨t, ht, htδ, hinter⟩ :=
      exists_small_interior_point p x0 (f x0) hs hlen hu hδ
    have htmin : t < min 1 (r / (-p.initialDirection.re)) := by
      simpa [δ] using htδ
    have htr : t < r / (-p.initialDirection.re) := by
      exact (lt_min_iff.mp htmin).2
    have hprod : t * (-p.initialDirection.re) < r :=
      (lt_div_iff₀ (neg_pos.mpr hleft)).mp htr
    have hx : x0 + t * p.initialDirection.re ∈ Icc (x0 - r) x0 := by
      constructor <;> nlinarith [mul_pos ht (neg_pos.mpr hleft)]
    have hf := hL _ hx
    have hab := habove _ hinter
    rw [hqre t, hqim t] at hab
    have hineq : f x0 + sL * (t * p.initialDirection.re) <
        f x0 + t * p.initialDirection.im := by
      calc
        f x0 + sL * (t * p.initialDirection.re) =
            f (x0 + t * p.initialDirection.re) := by rw [hf]; congr 1; ring
        _ < f x0 + t * p.initialDirection.im := hab
    have hmul : t * (sL * p.initialDirection.re) <
        t * p.initialDirection.im := by nlinarith [hineq]
    exact lt_of_mul_lt_mul_left hmul ht.le
  · intro hvertical
    obtain ⟨t, ht, ht1, hinter⟩ :=
      exists_small_interior_point p x0 (f x0) hs hlen hu zero_lt_one
    have hab := habove _ hinter
    rw [hqre t, hqim t, hvertical, mul_zero, add_zero] at hab
    have hpos : 0 < t * p.initialDirection.im := by linarith
    exact (mul_pos_iff_of_pos_left ht).mp hpos

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: angular sectors at seam vertices);
not a paper result. Interior directions lie strictly below the local affine seam. -/
theorem initialDirection_below_graph (f : ℝ → ℝ) (x0 r sL sR : ℝ)
    (hr : 0 < r)
    (hR : ∀ x ∈ Icc x0 (x0 + r), f x = f x0 + sR * (x - x0))
    (hL : ∀ x ∈ Icc (x0 - r) x0, f x = f x0 + sL * (x - x0))
    (p : Polyline) (hs : p.start = (⟨x0, f x0⟩ : ℂ))
    (hlen : 2 ≤ p.points.length) (hne : p.point 1 ≠ p.start)
    (hbelow : ∀ z ∈ p.interior, z.im < f z.re) :
    let u := p.initialDirection
    (0 < u.re → u.im < sR * u.re) ∧
      (u.re < 0 → u.im < sL * u.re) ∧
      (u.re = 0 → u.im < 0) := by
  dsimp only
  have hu : p.initialDirection ≠ 0 := by
    intro h
    have hp1 : p.point 1 - p.start = 0 := by
      simpa [Polyline.initialDirection] using h
    exact hne (sub_eq_zero.mp hp1)
  have hqre (t : ℝ) :
      (p.start + t • p.initialDirection).re = x0 + t * p.initialDirection.re := by
    rw [hs]
    simp
  have hqim (t : ℝ) :
      (p.start + t • p.initialDirection).im = f x0 + t * p.initialDirection.im := by
    rw [hs]
    simp
  constructor
  · intro hright
    let δ := min 1 (r / p.initialDirection.re)
    have hδ : 0 < δ := by
      dsimp [δ]
      exact lt_min zero_lt_one (div_pos hr hright)
    obtain ⟨t, ht, htδ, hinter⟩ :=
      exists_small_interior_point p x0 (f x0) hs hlen hu hδ
    have htr : t < r / p.initialDirection.re := by
      have htmin : t < min 1 (r / p.initialDirection.re) := by
        simpa [δ] using htδ
      exact (lt_min_iff.mp htmin).2
    have hprod : t * p.initialDirection.re < r :=
      (lt_div_iff₀ hright).mp htr
    have hx : x0 + t * p.initialDirection.re ∈ Icc x0 (x0 + r) := by
      constructor <;> nlinarith [mul_pos ht hright]
    have hf := hR _ hx
    have hab := hbelow _ hinter
    rw [hqre t, hqim t] at hab
    have hineq : f x0 + t * p.initialDirection.im <
        f x0 + sR * (t * p.initialDirection.re) := by
      calc
        f x0 + t * p.initialDirection.im <
            f (x0 + t * p.initialDirection.re) := hab
        _ = f x0 + sR * (t * p.initialDirection.re) := by rw [hf]; congr 1; ring
    have hmul : t * p.initialDirection.im <
        t * (sR * p.initialDirection.re) := by nlinarith [hineq]
    exact lt_of_mul_lt_mul_left hmul ht.le
  constructor
  · intro hleft
    let δ := min 1 (r / (-p.initialDirection.re))
    have hδ : 0 < δ := by
      dsimp [δ]
      exact lt_min zero_lt_one (div_pos hr (neg_pos.mpr hleft))
    obtain ⟨t, ht, htδ, hinter⟩ :=
      exists_small_interior_point p x0 (f x0) hs hlen hu hδ
    have htr : t < r / (-p.initialDirection.re) := by
      have htmin : t < min 1 (r / (-p.initialDirection.re)) := by
        simpa [δ] using htδ
      exact (lt_min_iff.mp htmin).2
    have hprod : t * (-p.initialDirection.re) < r :=
      (lt_div_iff₀ (neg_pos.mpr hleft)).mp htr
    have hx : x0 + t * p.initialDirection.re ∈ Icc (x0 - r) x0 := by
      constructor <;> nlinarith [mul_pos ht (neg_pos.mpr hleft)]
    have hf := hL _ hx
    have hab := hbelow _ hinter
    rw [hqre t, hqim t] at hab
    have hineq : f x0 + t * p.initialDirection.im <
        f x0 + sL * (t * p.initialDirection.re) := by
      calc
        f x0 + t * p.initialDirection.im <
            f (x0 + t * p.initialDirection.re) := hab
        _ = f x0 + sL * (t * p.initialDirection.re) := by rw [hf]; congr 1; ring
    have hmul : t * p.initialDirection.im <
        t * (sL * p.initialDirection.re) := by nlinarith [hineq]
    exact lt_of_mul_lt_mul_left hmul ht.le
  · intro hvertical
    obtain ⟨t, ht, ht1, hinter⟩ :=
      exists_small_interior_point p x0 (f x0) hs hlen hu zero_lt_one
    have hab := hbelow _ hinter
    rw [hqre t, hqim t, hvertical, mul_zero, add_zero] at hab
    have hneg : t * p.initialDirection.im < 0 := by linarith
    by_contra hnot
    have himnonneg : 0 ≤ p.initialDirection.im := le_of_not_gt hnot
    have hnonneg := mul_nonneg ht.le himnonneg
    linarith

end DirectedDistances.PlanarMap
