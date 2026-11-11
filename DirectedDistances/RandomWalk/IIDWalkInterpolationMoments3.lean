/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.IIDWalkInterpolationMoments2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Fourth moment bound for polygonal interpolation toward Lemma 4.11 -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory
open scoped NNReal

private def codeWalkRealBlock (ω : ℕ → Fin 3) (a m : ℕ) : ℝ × ℝ :=
  (((codeWalk ω (a + m)).1 : ℝ) - (codeWalk ω a).1,
    ((codeWalk ω (a + m)).2 : ℝ) - (codeWalk ω a).2)

private theorem walkLinearScalar_abs_le_of_step_bounds (p : ℕ → ℝ)
    (hp : ∀ k, |p k| ≤ (k : ℝ))
    (hd : ∀ k, |p (k + 1) - p k| ≤ 1) (x : ℝ≥0) :
    |walkLinearScalar p x| ≤ (⌊(x : ℝ)⌋₊ : ℝ) + 1 := by
  let k := ⌊(x : ℝ)⌋₊
  have hxlo : (k : ℝ) ≤ (x : ℝ) := by
    dsimp [k]
    exact_mod_cast Nat.floor_le x.coe_nonneg
  have hxhi : (x : ℝ) < (k : ℝ) + 1 := by
    dsimp [k]
    exact_mod_cast Nat.lt_floor_add_one (x : ℝ)
  have hxcell : x ∈ Set.Icc (k : ℝ≥0) (k + 1) := by
    constructor
    · exact_mod_cast hxlo
    · exact_mod_cast hxhi.le
  rw [walkLinearScalar_on_cell p k x hxcell]
  have hθlo : 0 ≤ (x : ℝ) - k := by linarith
  have hθhi : (x : ℝ) - k ≤ 1 := by linarith
  have hθ : |(x : ℝ) - k| ≤ 1 := by rw [abs_of_nonneg hθlo]; exact hθhi
  have hprod : |(x : ℝ) - k| * |p (k + 1) - p k| ≤ 1 := by
    calc
      |(x : ℝ) - k| * |p (k + 1) - p k| ≤ 1 * 1 :=
        mul_le_mul hθ (hd k) (abs_nonneg _) (by norm_num)
      _ = 1 := by ring
  calc
    |p k + ((x : ℝ) - k) * (p (k + 1) - p k)| ≤
        |p k| + |(x : ℝ) - k| * |p (k + 1) - p k| := by
          calc
            _ ≤ |p k| + |((x : ℝ) - k) * (p (k + 1) - p k)| := abs_add_le _ _
            _ = _ := by rw [abs_mul]
    _ ≤ (k : ℝ) + 1 := by linarith [hp k]

private theorem codeWalk_coordinate_interpolation_abs_le
    (ω : ℕ → Fin 3) (n : ℕ) (t : ℝ≥0) :
    |walkLinearScalar (fun k => ((codeWalk ω k).1 : ℝ))
        ((n : ℝ≥0) * t)| ≤ (⌊((n : ℝ≥0) * t : ℝ)⌋₊ : ℝ) + 1 ∧
    |walkLinearScalar (fun k => ((codeWalk ω k).2 : ℝ))
        ((n : ℝ≥0) * t)| ≤ (⌊((n : ℝ≥0) * t : ℝ)⌋₊ : ℝ) + 1 := by
  have hblock := codeWalk_block_sub_coord_abs_le_length ω 0
  have hp₁ : ∀ k, |((codeWalk ω k).1 : ℝ)| ≤ (k : ℝ) := by
    intro k
    have h := hblock k
    have hz : |(codeWalk ω k).1| ≤ k := by simpa [codeWalk_zero] using h.1
    exact_mod_cast hz
  have hp₂ : ∀ k, |((codeWalk ω k).2 : ℝ)| ≤ (k : ℝ) := by
    intro k
    have h := hblock k
    have hz : |(codeWalk ω k).2| ≤ k := by simpa [codeWalk_zero] using h.2
    exact_mod_cast hz
  have hd₁ : ∀ k, |((codeWalk ω (k + 1)).1 : ℝ) -
      (codeWalk ω k).1| ≤ 1 := by
    intro k
    have h := (codeWalk_succ_sub_coord_abs_le_one ω k).1
    rw [← Int.cast_sub]
    exact_mod_cast h
  have hd₂ : ∀ k, |((codeWalk ω (k + 1)).2 : ℝ) -
      (codeWalk ω k).2| ≤ 1 := by
    intro k
    have h := (codeWalk_succ_sub_coord_abs_le_one ω k).2
    rw [← Int.cast_sub]
    exact_mod_cast h
  exact ⟨walkLinearScalar_abs_le_of_step_bounds _ hp₁ hd₁ _,
    walkLinearScalar_abs_le_of_step_bounds _ hp₂ hd₂ _⟩

private theorem measurable_diffusiveInterpolation_codeWalk_eval (n : ℕ)
    (t : ℝ≥0) : Measurable (fun ω : ℕ → Fin 3 =>
      diffusiveInterpolation n (codeWalk ω) t) := by
  let x : ℝ≥0 := (n : ℝ≥0) * t
  let k : ℕ := ⌊(x : ℝ)⌋₊
  have hm₁ : Measurable (fun ω : ℕ → Fin 3 => ((codeWalk ω k).1 : ℝ)) :=
    (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      (measurable_fst.comp (measurable_codeWalk.eval (a := k)))
  have hm₂ : Measurable (fun ω : ℕ → Fin 3 => ((codeWalk ω (k + 1)).1 : ℝ)) :=
    (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      (measurable_fst.comp (measurable_codeWalk.eval (a := k + 1)))
  have hm₃ : Measurable (fun ω : ℕ → Fin 3 => ((codeWalk ω k).2 : ℝ)) :=
    (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      (measurable_snd.comp (measurable_codeWalk.eval (a := k)))
  have hm₄ : Measurable (fun ω : ℕ → Fin 3 => ((codeWalk ω (k + 1)).2 : ℝ)) :=
    (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      (measurable_snd.comp (measurable_codeWalk.eval (a := k + 1)))
  change Measurable (fun ω =>
    (walkLinearScalar (fun i => ((codeWalk ω i).1 : ℝ)) x / Real.sqrt n,
      walkLinearScalar (fun i => ((codeWalk ω i).2 : ℝ)) x / Real.sqrt n))
  simp only [walkLinearScalar, x]
  fun_prop

private theorem diffusiveInterpolation_codeWalk_norm_le (n : ℕ) (hn : 0 < n)
    (ω : ℕ → Fin 3) (t : ℝ≥0) :
    ‖diffusiveInterpolation n (codeWalk ω) t‖ ≤
      (((⌊((n : ℝ≥0) * t : ℝ)⌋₊ : ℝ) + 1) / Real.sqrt n) := by
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have h₁ := (codeWalk_coordinate_interpolation_abs_le ω n t).1
  have h₂ := (codeWalk_coordinate_interpolation_abs_le ω n t).2
  change max
    |walkLinearScalar (fun k => ((codeWalk ω k).1 : ℝ)) ((n : ℝ≥0) * t) /
        Real.sqrt n|
    |walkLinearScalar (fun k => ((codeWalk ω k).2 : ℝ)) ((n : ℝ≥0) * t) /
        Real.sqrt n| ≤ _
  apply max_le_iff.mpr
  constructor
  · rw [abs_div, abs_of_pos hsqrt]
    exact div_le_div_of_nonneg_right h₁ (le_of_lt hsqrt)
  · rw [abs_div, abs_of_pos hsqrt]
    exact div_le_div_of_nonneg_right h₂ (le_of_lt hsqrt)

private theorem measurable_diffusiveInterpolation_increment_four (n : ℕ)
    (s t : ℝ≥0) : Measurable (fun ω : ℕ → Fin 3 =>
      ‖diffusiveInterpolation n (codeWalk ω) t -
        diffusiveInterpolation n (codeWalk ω) s‖ ^ 4) := by
  have hs := measurable_diffusiveInterpolation_codeWalk_eval n s
  have ht := measurable_diffusiveInterpolation_codeWalk_eval n t
  fun_prop

private theorem diffusiveInterpolation_increment_four_integrable (n : ℕ)
    (hn : 0 < n) (s t : ℝ≥0) :
    Integrable (fun ω : ℕ → Fin 3 =>
      ‖diffusiveInterpolation n (codeWalk ω) t -
        diffusiveInterpolation n (codeWalk ω) s‖ ^ 4) iidCodeMeasure := by
  let ks : ℕ := ⌊((n : ℝ≥0) * s : ℝ)⌋₊
  let kt : ℕ := ⌊((n : ℝ≥0) * t : ℝ)⌋₊
  let B : ℝ := (((ks : ℝ) + 1) + ((kt : ℝ) + 1)) / Real.sqrt n
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoint (ω : ℕ → Fin 3) :
      ‖diffusiveInterpolation n (codeWalk ω) t -
        diffusiveInterpolation n (codeWalk ω) s‖ ^ 4 ≤ B ^ 4 := by
    have hs := diffusiveInterpolation_codeWalk_norm_le n hn ω s
    have ht := diffusiveInterpolation_codeWalk_norm_le n hn ω t
    have hnorm : ‖diffusiveInterpolation n (codeWalk ω) t -
        diffusiveInterpolation n (codeWalk ω) s‖ ≤ B := by
      calc
        _ ≤ ‖diffusiveInterpolation n (codeWalk ω) t‖ +
            ‖diffusiveInterpolation n (codeWalk ω) s‖ := norm_sub_le _ _
        _ ≤ (((kt : ℝ) + 1) / Real.sqrt n) +
            (((ks : ℝ) + 1) / Real.sqrt n) := add_le_add ht hs
        _ = B := by dsimp [B, ks, kt]; ring
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm) 4
  have hmeas := measurable_diffusiveInterpolation_increment_four n s t
  apply Integrable.of_bound hmeas.aestronglyMeasurable (B ^ 4)
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ ‖diffusiveInterpolation n (codeWalk ω) t -
      diffusiveInterpolation n (codeWalk ω) s‖ ^ 4)]
  exact hpoint ω

private theorem diffusiveInterpolation_increment_four_le_long (n : ℕ)
    (hn : 0 < n) (s t : ℝ≥0) (_hst : s ≤ t)
    (hlong : 1 ≤ (n : ℝ) * ((t : ℝ) - s))
    (ω : ℕ → Fin 3) :
    ‖diffusiveInterpolation n (codeWalk ω) t -
        diffusiveInterpolation n (codeWalk ω) s‖ ^ 4 ≤
      (27 / (n : ℝ) ^ 2) * (2 +
        ‖codeWalkRealBlock ω (⌊((n : ℝ≥0) * s : ℝ)⌋₊ + 1)
          (⌊((n : ℝ≥0) * t : ℝ)⌋₊ - (⌊((n : ℝ≥0) * s : ℝ)⌋₊ + 1))‖ ^ 4) := by
  let x : ℝ≥0 := (n : ℝ≥0) * s
  let y : ℝ≥0 := (n : ℝ≥0) * t
  let k : ℕ := ⌊(x : ℝ)⌋₊
  let l : ℕ := ⌊(y : ℝ)⌋₊
  let m : ℕ := l - (k + 1)
  let α : ℝ := (k : ℝ) + 1 - x
  let β : ℝ := (y : ℝ) - l
  let U : ℝ × ℝ :=
    (((codeWalk ω (k + 1)).1 : ℝ) - (codeWalk ω k).1,
      ((codeWalk ω (k + 1)).2 : ℝ) - (codeWalk ω k).2)
  let V : ℝ × ℝ := codeWalkRealBlock ω (k + 1) m
  let W : ℝ × ℝ :=
    (((codeWalk ω (l + 1)).1 : ℝ) - (codeWalk ω l).1,
      ((codeWalk ω (l + 1)).2 : ℝ) - (codeWalk ω l).2)
  have hxyt : (y : ℝ) - x = (n : ℝ) * ((t : ℝ) - s) := by
    dsimp [x, y]
    push_cast
    ring
  have hlong' : 1 ≤ (y : ℝ) - x := by rw [hxyt]; exact hlong
  have hxplus : (x : ℝ) + 1 ≤ y := by linarith
  have hxk : (x : ℝ) < (k : ℝ) + 1 := by
    dsimp [k, x]
    exact_mod_cast (Nat.lt_floor_add_one ((n : ℝ≥0) * s : ℝ))
  have hxklo : (k : ℝ) ≤ (x : ℝ) := by
    dsimp [k, x]
    exact_mod_cast Nat.floor_le ((n : ℝ≥0) * s).coe_nonneg
  have hkle : (k : ℝ) + 1 ≤ y := by linarith
  have hkl : k + 1 ≤ l := by
    dsimp [l, y]
    apply Nat.le_floor
    exact_mod_cast hkle
  have hkm : k + 1 + m = l := by dsimp [m]; omega
  have hcoeff := walkLinearScalar_interval_coefficients x y k l rfl rfl hkl
  have hα₀ : 0 ≤ α := by simpa [α] using hcoeff.1
  have hα₁ : α ≤ 1 := by simpa [α] using hcoeff.2.1
  have hβ₀ : 0 ≤ β := by simpa [β] using hcoeff.2.2.1
  have hβ₁ : β ≤ 1 := by simpa [β] using hcoeff.2.2.2.1
  have hdecomp := diffusiveInterpolation_interval_decomposition n hn
    (codeWalk ω) s t x y k l rfl rfl rfl rfl hkl
  have hdecomp' : Real.sqrt n •
      (diffusiveInterpolation n (codeWalk ω) t -
        diffusiveInterpolation n (codeWalk ω) s) = α • U + V + β • W := by
    simpa [α, β, U, V, W, codeWalkRealBlock, hkm, x, y] using hdecomp
  have hU : ‖U‖ ≤ 1 := by
    have h := codeWalk_succ_sub_coord_abs_le_one ω k
    have h₁ : |(((codeWalk ω (k + 1)).1 : ℝ) - (codeWalk ω k).1)| ≤ 1 := by
      rw [← Int.cast_sub]
      exact_mod_cast h.1
    have h₂ : |(((codeWalk ω (k + 1)).2 : ℝ) - (codeWalk ω k).2)| ≤ 1 := by
      rw [← Int.cast_sub]
      exact_mod_cast h.2
    change max |((codeWalk ω (k + 1)).1 : ℝ) - (codeWalk ω k).1|
      |((codeWalk ω (k + 1)).2 : ℝ) - (codeWalk ω k).2| ≤ 1
    exact max_le_iff.mpr ⟨h₁, h₂⟩
  have hW : ‖W‖ ≤ 1 := by
    have h := codeWalk_succ_sub_coord_abs_le_one ω l
    have h₁ : |(((codeWalk ω (l + 1)).1 : ℝ) - (codeWalk ω l).1)| ≤ 1 := by
      rw [← Int.cast_sub]
      exact_mod_cast h.1
    have h₂ : |(((codeWalk ω (l + 1)).2 : ℝ) - (codeWalk ω l).2)| ≤ 1 := by
      rw [← Int.cast_sub]
      exact_mod_cast h.2
    change max |((codeWalk ω (l + 1)).1 : ℝ) - (codeWalk ω l).1|
      |((codeWalk ω (l + 1)).2 : ℝ) - (codeWalk ω l).2| ≤ 1
    exact max_le_iff.mpr ⟨h₁, h₂⟩
  have hsum : ‖α • U + V + β • W‖ ≤ 2 + ‖V‖ := by
    calc
      ‖α • U + V + β • W‖ ≤ ‖α • U + V‖ + ‖β • W‖ := norm_add_le _ _
      _ ≤ ‖α • U‖ + ‖V‖ + ‖β • W‖ := by gcongr; exact norm_add_le _ _
      _ ≤ 1 + ‖V‖ + 1 := by
        have ha : ‖α • U‖ ≤ 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hα₀]
          calc
            α * ‖U‖ ≤ 1 * 1 := mul_le_mul hα₁ hU (norm_nonneg _) (by norm_num)
            _ = 1 := by ring
        have hb : ‖β • W‖ ≤ 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ₀]
          calc
            β * ‖W‖ ≤ 1 * 1 := mul_le_mul hβ₁ hW (norm_nonneg _) (by norm_num)
            _ = 1 := by ring
        linarith
      _ = 2 + ‖V‖ := by ring
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hscaled : Real.sqrt (n : ℝ) *
      ‖diffusiveInterpolation n (codeWalk ω) t -
        diffusiveInterpolation n (codeWalk ω) s‖ ≤ 2 + ‖V‖ := by
    calc
      _ = ‖Real.sqrt (n : ℝ) • (diffusiveInterpolation n (codeWalk ω) t -
          diffusiveInterpolation n (codeWalk ω) s)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt]
      _ = ‖α • U + V + β • W‖ := by rw [hdecomp']
      _ ≤ 2 + ‖V‖ := hsum
  have hnorm : ‖diffusiveInterpolation n (codeWalk ω) t -
      diffusiveInterpolation n (codeWalk ω) s‖ ≤ (2 + ‖V‖) / Real.sqrt n := by
    apply (le_div_iff₀ hsqrt).2
    nlinarith [hscaled]
  have hpow : ‖diffusiveInterpolation n (codeWalk ω) t -
      diffusiveInterpolation n (codeWalk ω) s‖ ^ 4 ≤
        ((2 + ‖V‖) / Real.sqrt n) ^ 4 := by
    gcongr
  have hsqrt4 : (Real.sqrt (n : ℝ)) ^ 4 = (n : ℝ) ^ 2 := by
    calc
      (Real.sqrt (n : ℝ)) ^ 4 = ((Real.sqrt (n : ℝ)) ^ 2) ^ 2 := by ring
      _ = (n : ℝ) ^ 2 := congrArg (fun q : ℝ => q ^ 2)
        (Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ)))
  have hthree : (2 + ‖V‖) ^ 4 ≤ 27 * (2 + ‖V‖ ^ 4) := by
    have h := add_three_fourth_le 1 ‖V‖ 1
    nlinarith
  have hfinal : ((2 + ‖V‖) / Real.sqrt (n : ℝ)) ^ 4 ≤
      (27 / (n : ℝ) ^ 2) * (2 + ‖V‖ ^ 4) := by
    rw [div_pow, hsqrt4]
    calc
      (2 + ‖V‖) ^ 4 / (n : ℝ) ^ 2 ≤
          (27 * (2 + ‖V‖ ^ 4)) / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hthree (sq_nonneg (n : ℝ))
      _ = (27 / (n : ℝ) ^ 2) * (2 + ‖V‖ ^ 4) := by ring
  calc
    _ ≤ ((2 + ‖V‖) / Real.sqrt (n : ℝ)) ^ 4 := hpow
    _ ≤ (27 / (n : ℝ) ^ 2) * (2 + ‖V‖ ^ 4) := hfinal
    _ = _ := by simp [V, codeWalkRealBlock, x, y, k, l, m]

/-- Helper toward Lemma 4.11: the fourth moment of every diffusive
interpolation increment is bounded by `162` times the squared time length. -/
theorem iidCodeWalk_diffusiveInterpolation_fourth_moment_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ s t : ℝ≥0, s ≤ t →
      Integrable (fun ω : ℕ → Fin 3 =>
        ‖diffusiveInterpolation n (codeWalk ω) t -
          diffusiveInterpolation n (codeWalk ω) s‖ ^ 4) iidCodeMeasure ∧
      (∫ ω : ℕ → Fin 3,
        ‖diffusiveInterpolation n (codeWalk ω) t -
          diffusiveInterpolation n (codeWalk ω) s‖ ^ 4 ∂iidCodeMeasure) ≤
        C * ((t : ℝ) - s) ^ 2 := by
  refine ⟨162, by norm_num, ?_⟩
  intro n hn s t hst
  have hnpos : 0 < n := by omega
  have hInt := diffusiveInterpolation_increment_four_integrable n hnpos s t
  refine ⟨hInt, ?_⟩
  let d : ℝ := (t : ℝ) - s
  have hd : 0 ≤ d := by dsimp [d]; exact sub_nonneg.mpr (by exact_mod_cast hst)
  by_cases hshort : (n : ℝ) * d < 1
  · have hpoint (ω : ℕ → Fin 3) :
        ‖diffusiveInterpolation n (codeWalk ω) t -
          diffusiveInterpolation n (codeWalk ω) s‖ ^ 4 ≤ d ^ 2 := by
      have h := diffusiveInterpolation_short_increment_le n hnpos (codeWalk ω)
        (by
          intro k
          have h := codeWalk_succ_sub_coord_abs_le_one ω k
          have h₁ : |(((codeWalk ω (k + 1)).1 : ℝ) - (codeWalk ω k).1)| ≤ 1 := by
            rw [← Int.cast_sub]
            exact_mod_cast h.1
          have h₂ : |(((codeWalk ω (k + 1)).2 : ℝ) - (codeWalk ω k).2)| ≤ 1 := by
            rw [← Int.cast_sub]
            exact_mod_cast h.2
          change max |((codeWalk ω (k + 1)).1 : ℝ) - (codeWalk ω k).1|
            |((codeWalk ω (k + 1)).2 : ℝ) - (codeWalk ω k).2| ≤ 1
          exact max_le_iff.mpr ⟨h₁, h₂⟩)
        s t hst (by simpa [d] using hshort)
      have hpow : ‖diffusiveInterpolation n (codeWalk ω) t -
          diffusiveInterpolation n (codeWalk ω) s‖ ^ 4 ≤
          (Real.sqrt (n : ℝ) * d) ^ 4 := by
        gcongr
      have hsqrt4 : (Real.sqrt (n : ℝ)) ^ 4 = (n : ℝ) ^ 2 := by
        calc
          (Real.sqrt (n : ℝ)) ^ 4 = ((Real.sqrt (n : ℝ)) ^ 2) ^ 2 := by ring
          _ = (n : ℝ) ^ 2 := congrArg (fun q : ℝ => q ^ 2)
            (Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ)))
      have hnd : 0 ≤ (n : ℝ) * d := mul_nonneg (by positivity) hd
      have hndsq : ((n : ℝ) * d) ^ 2 ≤ 1 := by nlinarith
      calc
        _ ≤ (Real.sqrt (n : ℝ) * d) ^ 4 := hpow
        _ = ((n : ℝ) * d) ^ 2 * d ^ 2 := by rw [mul_pow, hsqrt4]; ring
        _ ≤ d ^ 2 := by
          calc
            _ ≤ 1 * d ^ 2 := mul_le_mul_of_nonneg_right hndsq (sq_nonneg d)
            _ = d ^ 2 := by ring
    calc
      _ ≤ ∫ _ : ℕ → Fin 3, d ^ 2 ∂iidCodeMeasure :=
        integral_mono hInt (integrable_const _) hpoint
      _ = d ^ 2 := by simp
      _ ≤ 162 * ((t : ℝ) - s) ^ 2 := by nlinarith [sq_nonneg d]
  · have hlong : 1 ≤ (n : ℝ) * d := le_of_not_gt hshort
    let x : ℝ≥0 := (n : ℝ≥0) * s
    let y : ℝ≥0 := (n : ℝ≥0) * t
    let k : ℕ := ⌊(x : ℝ)⌋₊
    let l : ℕ := ⌊(y : ℝ)⌋₊
    let m : ℕ := l - (k + 1)
    let block : (ℕ → Fin 3) → ℝ := fun ω =>
      ‖codeWalkRealBlock ω (k + 1) m‖ ^ 4
    have hxyt : (y : ℝ) - x = (n : ℝ) * d := by
      dsimp [d, x, y]
      push_cast
      ring
    have hlong' : 1 ≤ (y : ℝ) - x := by rw [hxyt]; exact hlong
    have hxplus : (x : ℝ) + 1 ≤ y := by linarith
    have hxklo : (k : ℝ) ≤ (x : ℝ) := by
      dsimp [k, x]
      exact_mod_cast Nat.floor_le ((n : ℝ≥0) * s).coe_nonneg
    have hkle : (k : ℝ) + 1 ≤ y := by linarith
    have hkl : k + 1 ≤ l := by
      dsimp [l, y]
      apply Nat.le_floor
      exact_mod_cast hkle
    have hkm : k + 1 + m = l := by dsimp [m]; omega
    have hmle : (m : ℝ) ≤ (n : ℝ) * d := by
      have hc := walkLinearScalar_interval_coefficients x y k l rfl rfl hkl
      simpa [m, hxyt] using hc.2.2.2.2
    have hblockInt : Integrable block iidCodeMeasure := by
      have h := iidCodeWalk_block_fourth_moment_integrable (k + 1) m
      simpa [block, codeWalkRealBlock] using h
    have hblockMoment : (∫ ω, block ω ∂iidCodeMeasure) ≤ 4 * (m : ℝ) ^ 2 := by
      have h := iidCodeWalk_block_fourth_moment_le (k + 1) m
      simpa [block, codeWalkRealBlock] using h
    let c : ℝ := 27 / (n : ℝ) ^ 2
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hsumInt : Integrable (fun ω => 2 + block ω) iidCodeMeasure :=
      (integrable_const 2).add hblockInt
    have hRhsInt : Integrable (fun ω => c * (2 + block ω)) iidCodeMeasure := by
      simpa [smul_eq_mul] using hsumInt.const_mul c
    have hpoint (ω : ℕ → Fin 3) :
        ‖diffusiveInterpolation n (codeWalk ω) t -
          diffusiveInterpolation n (codeWalk ω) s‖ ^ 4 ≤ c * (2 + block ω) := by
      have h := diffusiveInterpolation_increment_four_le_long n hnpos s t hst
        (by simpa [d] using hlong) ω
      simpa [c, block, codeWalkRealBlock, x, y, k, l, m] using h
    have hmono := integral_mono hInt hRhsInt hpoint
    have hEq : (∫ ω, c * (2 + block ω) ∂iidCodeMeasure) =
        c * (2 + ∫ ω, block ω ∂iidCodeMeasure) := by
      rw [integral_const_mul, integral_add (integrable_const 2) hblockInt]
      simp
    have hmoment : (∫ ω, ‖diffusiveInterpolation n (codeWalk ω) t -
        diffusiveInterpolation n (codeWalk ω) s‖ ^ 4 ∂iidCodeMeasure) ≤
        c * (2 + 4 * (m : ℝ) ^ 2) := by
      calc
        _ ≤ ∫ ω, c * (2 + block ω) ∂iidCodeMeasure := hmono
        _ = c * (2 + ∫ ω, block ω ∂iidCodeMeasure) := hEq
        _ ≤ c * (2 + 4 * (m : ℝ) ^ 2) := by
          exact mul_le_mul_of_nonneg_left (by linarith [hblockMoment]) hc
    have hnRpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hratio1 : 1 / (n : ℝ) ^ 2 ≤ d ^ 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos hnRpos)).2
      nlinarith [sq_nonneg ((n : ℝ) * d - 1)]
    have hratio2 : (m : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤ d ^ 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos hnRpos)).2
      nlinarith [sq_nonneg ((n : ℝ) * d - m)]
    calc
      _ ≤ c * (2 + 4 * (m : ℝ) ^ 2) := hmoment
      _ = 54 / (n : ℝ) ^ 2 + 108 * ((m : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
        dsimp [c]
        ring
      _ = 54 * (1 / (n : ℝ) ^ 2) + 108 * ((m : ℝ) ^ 2 / (n : ℝ) ^ 2) := by ring
      _ ≤ 54 * d ^ 2 + 108 * d ^ 2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hratio1 (by norm_num))
          (mul_le_mul_of_nonneg_left hratio2 (by norm_num))
      _ = 162 * d ^ 2 := by ring
      _ = 162 * ((t : ℝ) - s) ^ 2 := by simp [d]

end DirectedDistances.RandomWalk
