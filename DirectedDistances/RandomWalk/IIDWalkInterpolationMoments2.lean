/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.IIDWalkInterpolationMoments
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Polygonal interpolation moment bounds toward Lemma 4.11

Deterministic estimates for the polygonal code walk and its fourth moment
increment bound. These are supporting results toward Lemma 4.11. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory
open scoped NNReal

/-- Helper toward Lemma 4.11: on a time interval shorter than one unit, a
polygonal scalar path with unit bounded increments changes by at most the
length of the interval. -/
theorem walkLinearScalar_short_increment_le (p : ℕ → ℝ)
    (hp : ∀ k, |p (k + 1) - p k| ≤ 1) (x y : ℝ≥0)
    (hxy : x ≤ y) (hshort : (y : ℝ) - x < 1) :
    |walkLinearScalar p y - walkLinearScalar p x| ≤ (y : ℝ) - x := by
  let k := ⌊(x : ℝ)⌋₊
  let l := ⌊(y : ℝ)⌋₊
  have hxlo : (k : ℝ) ≤ (x : ℝ) := by
    dsimp [k]
    exact_mod_cast Nat.floor_le x.coe_nonneg
  have hxhi : (x : ℝ) < (k : ℝ) + 1 := by
    dsimp [k]
    exact_mod_cast Nat.lt_floor_add_one (x : ℝ)
  have hylo : (l : ℝ) ≤ (y : ℝ) := by
    dsimp [l]
    exact_mod_cast Nat.floor_le y.coe_nonneg
  have hyhi : (y : ℝ) < (l : ℝ) + 1 := by
    dsimp [l]
    exact_mod_cast Nat.lt_floor_add_one (y : ℝ)
  have hkl : k ≤ l := by
    dsimp [k, l]
    exact Nat.floor_mono (by exact_mod_cast hxy)
  have hly : l ≤ k + 1 := by
    by_contra hn
    have hkn : k + 2 ≤ l := by omega
    have hknR : (k : ℝ) + 2 ≤ (l : ℝ) := by exact_mod_cast hkn
    linarith [hshort, hxhi, hylo]
  have hcells : x ∈ Set.Icc (k : ℝ≥0) (k + 1) ∧
      y ∈ Set.Icc (l : ℝ≥0) (l + 1) := by
    constructor <;> constructor
    · exact_mod_cast hxlo
    · exact_mod_cast hxhi.le
    · exact_mod_cast hylo
    · exact_mod_cast hyhi.le
  have hcoeff₀ : 0 ≤ (k : ℝ) + 1 - x := by linarith
  have hcoeffsum : ((k : ℝ) + 1 - x) + ((y : ℝ) - ((k : ℝ) + 1)) =
      (y : ℝ) - x := by ring
  by_cases hsame : l = k
  ·
    have hcellsY : y ∈ Set.Icc (k : ℝ≥0) (k + 1) := by
      simpa [l, hsame] using hcells.2
    have hformulaX := walkLinearScalar_on_cell p k x hcells.1
    have hformulaY := walkLinearScalar_on_cell p k y hcellsY
    rw [hformulaX, hformulaY]
    have hdelta : |p (k + 1) - p k| ≤ 1 := hp k
    calc
      |(p k + ((y : ℝ) - k) * (p (k + 1) - p k)) -
          (p k + ((x : ℝ) - k) * (p (k + 1) - p k))| =
          |((y : ℝ) - x) * (p (k + 1) - p k)| := by ring_nf
      _ = ((y : ℝ) - x) * |p (k + 1) - p k| := by
        rw [abs_mul, abs_of_nonneg (show 0 ≤ (y : ℝ) - (x : ℝ) by
          exact sub_nonneg.mpr (by exact_mod_cast hxy))]
      _ ≤ (y : ℝ) - x := by
        calc
          ((y : ℝ) - x) * |p (k + 1) - p k| ≤ ((y : ℝ) - x) * 1 :=
            mul_le_mul_of_nonneg_left hdelta
              (sub_nonneg.mpr (by exact_mod_cast hxy))
          _ = (y : ℝ) - x := by ring
  · have hnext : l = k + 1 := by omega
    have hcellsY : y ∈ Set.Icc ((k + 1 : ℕ) : ℝ≥0)
        (((k + 1 : ℕ) : ℝ≥0) + 1) := by
      simpa [l, hnext, Nat.add_assoc] using hcells.2
    have hylo' : ((k + 1 : ℕ) : ℝ) ≤ (y : ℝ) := by
      simpa [l, hnext] using hylo
    have hcoeff₁ : 0 ≤ (y : ℝ) - ((k : ℝ) + 1) := by
      have hle : (k : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
      linarith [hylo']
    have hformulaX := walkLinearScalar_on_cell p k x hcells.1
    have hformulaY := walkLinearScalar_on_cell p (k + 1) y hcellsY
    rw [hformulaX, hformulaY]
    let a : ℝ := (k : ℝ) + 1 - x
    let b : ℝ := (y : ℝ) - ((k : ℝ) + 1)
    let d₀ : ℝ := p (k + 1) - p k
    let d₁ : ℝ := p (k + 2) - p (k + 1)
    have ha : 0 ≤ a := by dsimp [a]; exact hcoeff₀
    have hb : 0 ≤ b := by dsimp [b]; exact hcoeff₁
    have hd₀ : |d₀| ≤ 1 := by simpa [d₀] using hp k
    have hd₁ : |d₁| ≤ 1 := by simpa [d₁] using hp (k + 1)
    have hsum : a + b = (y : ℝ) - x := by
      dsimp [a, b]
      exact hcoeffsum
    have hrewrite :
        (p (k + 1) + ((y : ℝ) - (k + 1)) * (p (k + 2) - p (k + 1))) -
          (p k + ((x : ℝ) - k) * (p (k + 1) - p k)) = a * d₀ + b * d₁ := by
      dsimp [a, b, d₀, d₁]
      ring
    have hrewrite' :
        (p (k + 1) + ((y : ℝ) - ((k + 1 : ℕ) : ℝ)) *
          (p (k + 1 + 1) - p (k + 1))) -
          (p k + ((x : ℝ) - k) * (p (k + 1) - p k)) = a * d₀ + b * d₁ := by
      simpa [Nat.add_assoc] using hrewrite
    rw [hrewrite']
    calc
      |a * d₀ + b * d₁| ≤ |a * d₀| + |b * d₁| := abs_add_le _ _
      _ = a * |d₀| + b * |d₁| := by
        rw [abs_mul, abs_of_nonneg ha, abs_mul, abs_of_nonneg hb]
      _ ≤ a + b := by
        calc
          a * |d₀| + b * |d₁| ≤ a * 1 + b * 1 := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hd₀ ha)
              (mul_le_mul_of_nonneg_left hd₁ hb)
          _ = a + b := by ring
      _ = (y : ℝ) - x := hsum

/-- Helper toward Lemma 4.11: the scalar interpolation difference across an
interval crossing several cells is the sum of its two boundary pieces and the
integer-time block between them. -/
theorem walkLinearScalar_interval_decomposition (p : ℕ → ℝ) (x y : ℝ≥0)
    (k l : ℕ) (hk : ⌊(x : ℝ)⌋₊ = k) (hl : ⌊(y : ℝ)⌋₊ = l)
    (_hkl : k + 1 ≤ l) :
    walkLinearScalar p y - walkLinearScalar p x =
      ((k : ℝ) + 1 - x) * (p (k + 1) - p k) +
        (p l - p (k + 1)) + ((y : ℝ) - l) * (p (l + 1) - p l) := by
  have hx : x ∈ Set.Icc (k : ℝ≥0) (k + 1) := by
    constructor
    · have h := Nat.floor_le x.coe_nonneg
      rw [hk] at h
      exact_mod_cast h
    · have h := Nat.lt_floor_add_one (x : ℝ)
      rw [hk] at h
      exact_mod_cast h.le
  have hy : y ∈ Set.Icc (l : ℝ≥0) (l + 1) := by
    constructor
    · have h := Nat.floor_le y.coe_nonneg
      rw [hl] at h
      exact_mod_cast h
    · have h := Nat.lt_floor_add_one (y : ℝ)
      rw [hl] at h
      exact_mod_cast h.le
  rw [walkLinearScalar_on_cell p k x hx, walkLinearScalar_on_cell p l y hy]
  ring

/-- Helper toward Lemma 4.11: the two boundary fractions in an interpolation
decomposition lie in `[0,1]`, and the interior block length is bounded by the
elapsed time. -/
theorem walkLinearScalar_interval_coefficients (x y : ℝ≥0) (k l : ℕ)
    (hk : ⌊(x : ℝ)⌋₊ = k) (hl : ⌊(y : ℝ)⌋₊ = l)
    (hkl : k + 1 ≤ l) :
    0 ≤ (k : ℝ) + 1 - x ∧ (k : ℝ) + 1 - x ≤ 1 ∧
    0 ≤ (y : ℝ) - l ∧ (y : ℝ) - l ≤ 1 ∧
    ((l - (k + 1) : ℕ) : ℝ) ≤ (y : ℝ) - x := by
  have hxlo : (k : ℝ) ≤ (x : ℝ) := by
    have h := Nat.floor_le x.coe_nonneg
    rw [hk] at h
    exact_mod_cast h
  have hxhi : (x : ℝ) < (k : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one (x : ℝ)
    rw [hk] at h
    exact_mod_cast h
  have hylo : (l : ℝ) ≤ (y : ℝ) := by
    have h := Nat.floor_le y.coe_nonneg
    rw [hl] at h
    exact_mod_cast h
  have hyhi : (y : ℝ) < (l : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one (y : ℝ)
    rw [hl] at h
    exact_mod_cast h
  have hblock : ((l - (k + 1) : ℕ) : ℝ) ≤ (y : ℝ) - x := by
    have hkcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by norm_num
    have hblock' : (l : ℝ) - ((k + 1 : ℕ) : ℝ) ≤ (y : ℝ) - x := by
      rw [hkcast]
      linarith
    rw [Nat.cast_sub hkl]
    exact hblock'
  refine ⟨by linarith, ?_, by linarith, ?_, hblock⟩
  · linarith
  · linarith

/-- Helper toward Lemma 4.11: on a long interval, the first coordinate of the
diffusive interpolation is exactly the two affine boundary increments plus
the integer-time block increment. -/
theorem diffusiveInterpolation_fst_interval_decomposition (n : ℕ) (hn : 0 < n)
    (z : ℕ → ℤ × ℤ) (s t x y : ℝ≥0) (k l : ℕ)
    (hx : x = (n : ℝ≥0) * s) (hy : y = (n : ℝ≥0) * t)
    (hk : ⌊(x : ℝ)⌋₊ = k) (hl : ⌊(y : ℝ)⌋₊ = l)
    (hkl : k + 1 ≤ l) :
    Real.sqrt n * ((diffusiveInterpolation n z t).1 -
      (diffusiveInterpolation n z s).1) =
      ((k : ℝ) + 1 - x) * (((z (k + 1)).1 : ℝ) - (z k).1) +
        (((z l).1 : ℝ) - (z (k + 1)).1) +
          ((y : ℝ) - l) * (((z (l + 1)).1 : ℝ) - (z l).1) := by
  have hdecomp := walkLinearScalar_interval_decomposition
    (fun i => ((z i).1 : ℝ)) x y k l hk hl hkl
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  change Real.sqrt (n : ℝ) *
    (walkLinearScalar (fun i => ((z i).1 : ℝ)) ((n : ℝ≥0) * t) /
        Real.sqrt (n : ℝ) -
      walkLinearScalar (fun i => ((z i).1 : ℝ)) ((n : ℝ≥0) * s) /
        Real.sqrt (n : ℝ)) = _
  rw [← sub_div, ← hy, ← hx, hdecomp]
  field_simp [ne_of_gt hsqrt]

/-- Helper toward Lemma 4.11: the second coordinate has the same exact
long-interval affine decomposition. -/
theorem diffusiveInterpolation_snd_interval_decomposition (n : ℕ) (hn : 0 < n)
    (z : ℕ → ℤ × ℤ) (s t x y : ℝ≥0) (k l : ℕ)
    (hx : x = (n : ℝ≥0) * s) (hy : y = (n : ℝ≥0) * t)
    (hk : ⌊(x : ℝ)⌋₊ = k) (hl : ⌊(y : ℝ)⌋₊ = l)
    (hkl : k + 1 ≤ l) :
    Real.sqrt n * ((diffusiveInterpolation n z t).2 -
      (diffusiveInterpolation n z s).2) =
      ((k : ℝ) + 1 - x) * (((z (k + 1)).2 : ℝ) - (z k).2) +
        (((z l).2 : ℝ) - (z (k + 1)).2) +
          ((y : ℝ) - l) * (((z (l + 1)).2 : ℝ) - (z l).2) := by
  have hdecomp := walkLinearScalar_interval_decomposition
    (fun i => ((z i).2 : ℝ)) x y k l hk hl hkl
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  change Real.sqrt (n : ℝ) *
    (walkLinearScalar (fun i => ((z i).2 : ℝ)) ((n : ℝ≥0) * t) /
        Real.sqrt (n : ℝ) -
      walkLinearScalar (fun i => ((z i).2 : ℝ)) ((n : ℝ≥0) * s) /
        Real.sqrt (n : ℝ)) = _
  rw [← sub_div, ← hy, ← hx, hdecomp]
  field_simp [ne_of_gt hsqrt]

/-- Helper toward Lemma 4.11: the vector interpolation increment has the
boundary/block/boundary decomposition, coordinatewise in the maximum norm. -/
theorem diffusiveInterpolation_interval_decomposition (n : ℕ) (hn : 0 < n)
    (z : ℕ → ℤ × ℤ) (s t x y : ℝ≥0) (k l : ℕ)
    (hx : x = (n : ℝ≥0) * s) (hy : y = (n : ℝ≥0) * t)
    (hk : ⌊(x : ℝ)⌋₊ = k) (hl : ⌊(y : ℝ)⌋₊ = l)
    (hkl : k + 1 ≤ l) :
    Real.sqrt n • (diffusiveInterpolation n z t - diffusiveInterpolation n z s) =
      ((k : ℝ) + 1 - x) •
        ((((z (k + 1)).1 : ℝ) - (z k).1, ((z (k + 1)).2 : ℝ) - (z k).2)) +
      ((((z l).1 : ℝ) - (z (k + 1)).1, ((z l).2 : ℝ) - (z (k + 1)).2)) +
      ((y : ℝ) - l) •
        ((((z (l + 1)).1 : ℝ) - (z l).1, ((z (l + 1)).2 : ℝ) - (z l).2)) := by
  apply Prod.ext
  · simpa using diffusiveInterpolation_fst_interval_decomposition
      n hn z s t x y k l hx hy hk hl hkl
  · simpa using diffusiveInterpolation_snd_interval_decomposition
      n hn z s t x y k l hx hy hk hl hkl

/-- Helper toward Lemma 4.11: for a unit-bounded two-coordinate walk, the
diffusive interpolation increment on an interval shorter than one mesh cell
is at most `sqrt n` times the time increment in the maximum norm. -/
theorem diffusiveInterpolation_short_increment_le (n : ℕ) (hn : 0 < n)
    (z : ℕ → ℤ × ℤ)
    (hz : ∀ k, ‖((((z (k + 1)).1 : ℝ) - (z k).1,
      ((z (k + 1)).2 : ℝ) - (z k).2))‖ ≤ 1)
    (s t : ℝ≥0) (hst : s ≤ t)
    (hshort : (n : ℝ) * ((t : ℝ) - (s : ℝ)) < 1) :
    ‖diffusiveInterpolation n z t - diffusiveInterpolation n z s‖ ≤
      Real.sqrt n * ((t : ℝ) - (s : ℝ)) := by
  let x : ℝ≥0 := (n : ℝ≥0) * s
  let y : ℝ≥0 := (n : ℝ≥0) * t
  have hxy : x ≤ y := by
    exact mul_le_mul_of_nonneg_left hst (by positivity)
  have hq : (y : ℝ) - (x : ℝ) =
      (n : ℝ) * ((t : ℝ) - (s : ℝ)) := by
    dsimp [x, y]
    push_cast
    ring
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsqrtn : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hp₁ : ∀ k, |((z (k + 1)).1 : ℝ) - (z k).1| ≤ 1 := by
    intro k
    have h := hz k
    change max |((z (k + 1)).1 : ℝ) - (z k).1|
      |((z (k + 1)).2 : ℝ) - (z k).2| ≤ 1 at h
    exact (le_trans (le_max_left _ _) h)
  have hp₂ : ∀ k, |((z (k + 1)).2 : ℝ) - (z k).2| ≤ 1 := by
    intro k
    have h := hz k
    change max |((z (k + 1)).1 : ℝ) - (z k).1|
      |((z (k + 1)).2 : ℝ) - (z k).2| ≤ 1 at h
    exact (le_trans (le_max_right _ _) h)
  have h₁ := walkLinearScalar_short_increment_le
    (fun k => ((z k).1 : ℝ)) hp₁ x y hxy (by rw [hq]; exact hshort)
  have h₂ := walkLinearScalar_short_increment_le
    (fun k => ((z k).2 : ℝ)) hp₂ x y hxy (by rw [hq]; exact hshort)
  have hscaled₁ :
      |walkLinearScalar (fun k => ((z k).1 : ℝ)) y / Real.sqrt n -
        walkLinearScalar (fun k => ((z k).1 : ℝ)) x / Real.sqrt n| ≤
        Real.sqrt n * ((t : ℝ) - (s : ℝ)) := by
    rw [← sub_div, abs_div, abs_of_pos hsqrt]
    calc
      |walkLinearScalar (fun k => ((z k).1 : ℝ)) y -
        walkLinearScalar (fun k => ((z k).1 : ℝ)) x| / Real.sqrt n ≤
          ((y : ℝ) - (x : ℝ)) / Real.sqrt n :=
        div_le_div_of_nonneg_right h₁ (le_of_lt hsqrt)
      _ = Real.sqrt n * ((t : ℝ) - (s : ℝ)) := by
        rw [hq]
        calc
          ((n : ℝ) * ((t : ℝ) - (s : ℝ))) / Real.sqrt n =
              (Real.sqrt n * Real.sqrt n * ((t : ℝ) - (s : ℝ))) / Real.sqrt n := by
                nth_rewrite 1 [← hsqrtn]
                ring
          _ = Real.sqrt n * ((t : ℝ) - (s : ℝ)) := by
            field_simp [ne_of_gt hsqrt]
  have hscaled₂ :
      |walkLinearScalar (fun k => ((z k).2 : ℝ)) y / Real.sqrt n -
        walkLinearScalar (fun k => ((z k).2 : ℝ)) x / Real.sqrt n| ≤
        Real.sqrt n * ((t : ℝ) - (s : ℝ)) := by
    rw [← sub_div, abs_div, abs_of_pos hsqrt]
    calc
      |walkLinearScalar (fun k => ((z k).2 : ℝ)) y -
        walkLinearScalar (fun k => ((z k).2 : ℝ)) x| / Real.sqrt n ≤
          ((y : ℝ) - (x : ℝ)) / Real.sqrt n :=
        div_le_div_of_nonneg_right h₂ (le_of_lt hsqrt)
      _ = Real.sqrt n * ((t : ℝ) - (s : ℝ)) := by
        rw [hq]
        calc
          ((n : ℝ) * ((t : ℝ) - (s : ℝ))) / Real.sqrt n =
              (Real.sqrt n * Real.sqrt n * ((t : ℝ) - (s : ℝ))) / Real.sqrt n := by
                nth_rewrite 1 [← hsqrtn]
                ring
          _ = Real.sqrt n * ((t : ℝ) - (s : ℝ)) := by
            field_simp [ne_of_gt hsqrt]
  change max
    |walkLinearScalar (fun k => ((z k).1 : ℝ)) y / Real.sqrt n -
      walkLinearScalar (fun k => ((z k).1 : ℝ)) x / Real.sqrt n|
    |walkLinearScalar (fun k => ((z k).2 : ℝ)) y / Real.sqrt n -
      walkLinearScalar (fun k => ((z k).2 : ℝ)) x / Real.sqrt n| ≤ _
  exact max_le_iff.mpr ⟨hscaled₁, hscaled₂⟩

/-- Helper toward Lemma 4.11: a sum of three nonnegative fourth powers bounds
the fourth power of the sum, with the sharp convexity factor `27`. -/
theorem add_three_fourth_le (a b c : ℝ) :
    (a + b + c) ^ 4 ≤ 27 * (a ^ 4 + b ^ 4 + c ^ 4) := by
  let S : ℝ := a ^ 2 + b ^ 2 + c ^ 2
  have h1 : (a + b + c) ^ 2 ≤ 3 * S := by
    dsimp [S]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have h2 : S ^ 2 ≤ 3 * (a ^ 4 + b ^ 4 + c ^ 4) := by
    dsimp [S]
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 - c ^ 2),
      sq_nonneg (b ^ 2 - c ^ 2)]
  have hsum_nonneg : 0 ≤ (a + b + c) ^ 2 := sq_nonneg _
  have hS_nonneg : 0 ≤ S := by positivity
  have hthreeS_nonneg : 0 ≤ 3 * S := mul_nonneg (by norm_num) hS_nonneg
  have hsq : ((a + b + c) ^ 2) ^ 2 ≤ (3 * S) ^ 2 := by
    have hmul := mul_nonneg (sub_nonneg.mpr h1) (add_nonneg hsum_nonneg hthreeS_nonneg)
    nlinarith
  calc
    (a + b + c) ^ 4 = ((a + b + c) ^ 2) ^ 2 := by ring
    _ ≤ (3 * S) ^ 2 := hsq
    _ = 9 * S ^ 2 := by ring
    _ ≤ 27 * (a ^ 4 + b ^ 4 + c ^ 4) := by nlinarith [h2]

end DirectedDistances.RandomWalk
