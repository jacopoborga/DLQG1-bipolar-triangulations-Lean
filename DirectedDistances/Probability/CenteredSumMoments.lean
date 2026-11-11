/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm







public section
namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory

open scoped ENNReal

/-- The partial sum of the first `n` members of a sequence of real random variables. -/
@[expose] def centeredPartialSum {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  ∑ i ∈ Finset.range n, Y i

/-- Finite fourth moments of the summands imply a finite fourth moment of each partial sum. -/
theorem centeredPartialSum_memLp_four {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hid : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) (h4 : MemLp (Y 0) 4 μ) (n : ℕ) :
    MemLp (centeredPartialSum Y n) 4 μ := by
  unfold centeredPartialSum
  apply MeasureTheory.memLp_finsetSum'
  intro i hi
  exact (hid i).memLp_iff.mpr h4

/-- Peeling off the last summand of a partial sum; generic helper. -/
theorem centeredPartialSum_succ {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℕ → Ω → ℝ) (n : ℕ) :
    centeredPartialSum Y (n + 1) = centeredPartialSum Y n + Y n := by
  funext ω
  simp [centeredPartialSum, Finset.sum_range_succ]

/-- A centered sequence of identically distributed summands has centered partial sums. -/
theorem centeredPartialSum_integral_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hid : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) (h4 : MemLp (Y 0) 4 μ)
    (hc : ∫ ω, Y 0 ω ∂μ = 0) (n : ℕ) :
    ∫ ω, centeredPartialSum Y n ω ∂μ = 0 := by
  induction n with
  | zero => simp [centeredPartialSum]
  | succ n ih =>
    have hsum := centeredPartialSum_memLp_four hid h4 n
    have hnext : MemLp (Y n) 4 μ := (hid n).memLp_iff.mpr h4
    rw [centeredPartialSum_succ]
    simp only [Pi.add_apply]
    rw [integral_add (hsum.integrable (by norm_num)) (hnext.integrable (by norm_num))]
    rw [ih, (hid n).integral_eq, hc]
    simp

/-- The second moment of a centered sum of independent, identically distributed summands. -/
theorem centeredPartialSum_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hind : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i))
    (hid : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) (h4 : MemLp (Y 0) 4 μ)
    (hc : ∫ ω, Y 0 ω ∂μ = 0) (n : ℕ) :
    ∫ ω, (centeredPartialSum Y n ω) ^ 2 ∂μ =
      (n : ℝ) * ∫ ω, (Y 0 ω) ^ 2 ∂μ := by
  induction n with
  | zero => simp [centeredPartialSum]
  | succ n ih =>
    let X := centeredPartialSum Y n
    have hX4 : MemLp X 4 μ := centeredPartialSum_memLp_four hid h4 n
    have hY4 : MemLp (Y n) 4 μ := (hid n).memLp_iff.mpr h4
    have hX2 : MemLp X 2 μ := hX4.mono_exponent (by norm_num)
    have hY2 : MemLp (Y n) 2 μ := hY4.mono_exponent (by norm_num)
    have hXsq : Integrable (fun ω => (X ω) ^ 2) μ := by
      simpa [Real.norm_eq_abs] using hX2.integrable_norm_pow (by norm_num)
    have hYsq : Integrable (fun ω => (Y n ω) ^ 2) μ := by
      simpa [Real.norm_eq_abs] using hY2.integrable_norm_pow (by norm_num)
    have hXY2 : MemLp (fun ω => X ω * Y n ω) 2 μ := by
      have hHolder : ENNReal.HolderTriple 4 4 2 := by
        constructor
        rw [← two_mul, show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
          ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      exact MemLp.mul (hpqr := hHolder) hX4 hY4
    have hXY : Integrable (fun ω => X ω * Y n ω) μ :=
      hXY2.integrable (by norm_num)
    have hInd : IndepFun X (Y n) μ := by
      simpa [X, centeredPartialSum] using
        hind.indepFun_finsetSum_of_notMem hmeas (by simp)
    have hmeanX : ∫ ω, X ω ∂μ = 0 :=
      centeredPartialSum_integral_eq_zero hid h4 hc n
    have hmeanY : ∫ ω, Y n ω ∂μ = 0 := by
      rw [(hid n).integral_eq, hc]
    have hY2eq : ∫ ω, (Y n ω) ^ 2 ∂μ = ∫ ω, (Y 0 ω) ^ 2 ∂μ := by
      simpa using ((hid n).comp (measurable_id.pow_const 2)).integral_eq
    rw [centeredPartialSum_succ]
    calc
      ∫ ω, (X ω + Y n ω) ^ 2 ∂μ =
          ∫ ω, (X ω) ^ 2 + (2 * (X ω * Y n ω) + (Y n ω) ^ 2) ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        ring
      _ = ∫ ω, (X ω) ^ 2 ∂μ +
          ∫ ω, (2 * (X ω * Y n ω) + (Y n ω) ^ 2) ∂μ :=
        integral_add hXsq ((hXY.const_mul 2).add hYsq)
      _ = ∫ ω, (X ω) ^ 2 ∂μ +
          (2 * ∫ ω, X ω * Y n ω ∂μ + ∫ ω, (Y n ω) ^ 2 ∂μ) := by
        rw [integral_add (hXY.const_mul 2) hYsq, integral_const_mul]
      _ = (n : ℝ) * ∫ ω, (Y 0 ω) ^ 2 ∂μ +
          (2 * ((∫ ω, X ω ∂μ) * ∫ ω, Y n ω ∂μ) +
            ∫ ω, (Y 0 ω) ^ 2 ∂μ) := by
        rw [hInd.integral_fun_mul_eq_mul_integral hX4.aestronglyMeasurable
          hY4.aestronglyMeasurable, ih, hY2eq]
      _ = ((n + 1 : ℕ) : ℝ) * ∫ ω, (Y 0 ω) ^ 2 ∂μ := by
        rw [hmeanX, hmeanY]
        push_cast
        ring

/-- A generic helper (not a paper result): the fourth-moment identity for centered
independent, identically distributed sums. -/
theorem centeredPartialSum_fourth_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hind : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i))
    (hid : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) (h4 : MemLp (Y 0) 4 μ)
    (hc : ∫ ω, Y 0 ω ∂μ = 0) (n : ℕ) :
    ∫ ω, (centeredPartialSum Y n ω) ^ 4 ∂μ =
      (n : ℝ) * ∫ ω, (Y 0 ω) ^ 4 ∂μ +
        3 * (n : ℝ) * ((n : ℝ) - 1) *
          (∫ ω, (Y 0 ω) ^ 2 ∂μ) ^ 2 := by
  induction n with
  | zero => simp [centeredPartialSum]
  | succ n ih =>
    let X := centeredPartialSum Y n
    have hX4 : MemLp X 4 μ := centeredPartialSum_memLp_four hid h4 n
    have hY4 : MemLp (Y n) 4 μ := (hid n).memLp_iff.mpr h4
    have hX2 : MemLp X 2 μ := hX4.mono_exponent (by norm_num)
    have hY2 : MemLp (Y n) 2 μ := hY4.mono_exponent (by norm_num)
    have hXsq : Integrable (fun ω => (X ω) ^ 2) μ := by
      simpa [Real.norm_eq_abs] using hX2.integrable_norm_pow (by norm_num)
    have hYsq : Integrable (fun ω => (Y n ω) ^ 2) μ := by
      simpa [Real.norm_eq_abs] using hY2.integrable_norm_pow (by norm_num)
    have hXfour : Integrable (fun ω => (X ω) ^ 4) μ := by
      apply (integrable_norm_iff (hX4.aestronglyMeasurable.pow 4)).mp
      simpa [Real.norm_eq_abs, abs_pow] using hX4.integrable_norm_pow (by norm_num)
    have hYfour : Integrable (fun ω => (Y n ω) ^ 4) μ := by
      apply (integrable_norm_iff (hY4.aestronglyMeasurable.pow 4)).mp
      simpa [Real.norm_eq_abs, abs_pow] using hY4.integrable_norm_pow (by norm_num)
    have hXcubeNorm : Integrable (fun ω => ‖X ω‖ ^ 3) μ :=
      integrable_norm_pow_of_le hX4.aestronglyMeasurable (by norm_num)
        hX4.integrable_norm_pow'
    have hYcubeNorm : Integrable (fun ω => ‖Y n ω‖ ^ 3) μ :=
      integrable_norm_pow_of_le hY4.aestronglyMeasurable (by norm_num)
        hY4.integrable_norm_pow'
    have hXcube : Integrable (fun ω => X ω ^ 3) μ := by
      apply (integrable_norm_iff (hX4.aestronglyMeasurable.pow 3)).mp
      simpa [Real.norm_eq_abs, abs_pow] using hXcubeNorm
    have hYcube : Integrable (fun ω => (Y n ω) ^ 3) μ := by
      apply (integrable_norm_iff (hY4.aestronglyMeasurable.pow 3)).mp
      simpa [Real.norm_eq_abs, abs_pow] using hYcubeNorm
    have hInd : IndepFun X (Y n) μ := by
      simpa [X, centeredPartialSum] using
        hind.indepFun_finsetSum_of_notMem hmeas (by simp)
    have hIndXcube : IndepFun (fun ω => X ω ^ 3) (Y n) μ := by
      change IndepFun ((fun x : ℝ => x ^ 3) ∘ X) (id ∘ Y n) μ
      exact hInd.comp (measurable_id.pow_const 3) measurable_id
    have hIndYcube : IndepFun X (fun ω => (Y n ω) ^ 3) μ := by
      change IndepFun (id ∘ X) ((fun x : ℝ => x ^ 3) ∘ Y n) μ
      exact hInd.comp measurable_id (measurable_id.pow_const 3)
    have hIndSquares : IndepFun (fun ω => X ω ^ 2) (fun ω => (Y n ω) ^ 2) μ := by
      change IndepFun ((fun x : ℝ => x ^ 2) ∘ X) ((fun x : ℝ => x ^ 2) ∘ Y n) μ
      exact hInd.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
    have hXmean : ∫ ω, X ω ∂μ = 0 :=
      centeredPartialSum_integral_eq_zero hid h4 hc n
    have hYmean : ∫ ω, Y n ω ∂μ = 0 := by
      rw [(hid n).integral_eq, hc]
    have hY2eq : ∫ ω, (Y n ω) ^ 2 ∂μ = ∫ ω, (Y 0 ω) ^ 2 ∂μ := by
      simpa using ((hid n).comp (measurable_id.pow_const 2)).integral_eq
    have hX2eq : ∫ ω, X ω ^ 2 ∂μ =
        (n : ℝ) * ∫ ω, (Y 0 ω) ^ 2 ∂μ :=
      centeredPartialSum_second_moment hind hmeas hid h4 hc n
    have hY4eq : ∫ ω, (Y n ω) ^ 4 ∂μ = ∫ ω, (Y 0 ω) ^ 4 ∂μ := by
      simpa using ((hid n).comp (measurable_id.pow_const 4)).integral_eq
    have hIndXcubeInt : Integrable (fun ω => X ω ^ 3 * Y n ω) μ :=
      hIndXcube.integrable_mul hXcube (hY4.integrable (by norm_num))
    have hIndYcubeInt : Integrable (fun ω => X ω * (Y n ω) ^ 3) μ :=
      hIndYcube.integrable_mul (hX4.integrable (by norm_num)) hYcube
    have hIndSquaresInt : Integrable (fun ω => X ω ^ 2 * (Y n ω) ^ 2) μ :=
      hIndSquares.integrable_mul hXsq hYsq
    let C1 := fun ω => 4 * (X ω ^ 3 * Y n ω)
    let C2 := fun ω => 6 * (X ω ^ 2 * (Y n ω) ^ 2)
    let C3 := fun ω => 4 * (X ω * (Y n ω) ^ 3)
    have hC1 : Integrable C1 μ := hIndXcubeInt.const_mul 4
    have hC2 : Integrable C2 μ := hIndSquaresInt.const_mul 6
    have hC3 : Integrable C3 μ := hIndYcubeInt.const_mul 4
    have hRest : Integrable
        (fun ω => C1 ω + (C2 ω + (C3 ω + (Y n ω) ^ 4))) μ :=
      hC1.add (hC2.add (hC3.add hYfour))
    have hRest23 :
        ∫ ω, C2 ω + (C3 ω + (Y n ω) ^ 4) ∂μ =
          ∫ ω, C2 ω ∂μ + (∫ ω, C3 ω ∂μ + ∫ ω, (Y n ω) ^ 4 ∂μ) := by
      calc
        _ = ∫ ω, C2 ω ∂μ + ∫ ω, C3 ω + (Y n ω) ^ 4 ∂μ :=
          integral_add hC2 (hC3.add hYfour)
        _ = _ := congrArg (fun z => (∫ ω, C2 ω ∂μ) + z)
          (integral_add hC3 hYfour)
    have hRestIntegral :
        ∫ ω, C1 ω + (C2 ω + (C3 ω + (Y n ω) ^ 4)) ∂μ =
          4 * ∫ ω, X ω ^ 3 * Y n ω ∂μ +
            (6 * ∫ ω, X ω ^ 2 * (Y n ω) ^ 2 ∂μ +
              (4 * ∫ ω, X ω * (Y n ω) ^ 3 ∂μ + ∫ ω, (Y n ω) ^ 4 ∂μ)) := by
      calc
        _ = ∫ ω, C1 ω ∂μ + ∫ ω, C2 ω + (C3 ω + (Y n ω) ^ 4) ∂μ :=
          integral_add hC1 (hC2.add (hC3.add hYfour))
        _ = ∫ ω, C1 ω ∂μ +
            (∫ ω, C2 ω ∂μ +
              (∫ ω, C3 ω ∂μ + ∫ ω, (Y n ω) ^ 4 ∂μ)) := by
          exact congrArg (fun z => (∫ ω, C1 ω ∂μ) + z) hRest23
        _ = _ := by simp [C1, C2, C3, integral_const_mul]
    have hExpansion :
        ∫ ω, (X ω + Y n ω) ^ 4 ∂μ =
          ∫ ω, X ω ^ 4 ∂μ +
            (4 * ∫ ω, X ω ^ 3 * Y n ω ∂μ +
              (6 * ∫ ω, X ω ^ 2 * (Y n ω) ^ 2 ∂μ +
                (4 * ∫ ω, X ω * (Y n ω) ^ 3 ∂μ +
                  ∫ ω, (Y n ω) ^ 4 ∂μ))) := by
      calc
        ∫ ω, (X ω + Y n ω) ^ 4 ∂μ =
            ∫ ω, X ω ^ 4 +
              (C1 ω + (C2 ω + (C3 ω + (Y n ω) ^ 4))) ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          simp only [C1, C2, C3]
          ring
        _ = ∫ ω, X ω ^ 4 ∂μ +
            ∫ ω, C1 ω + (C2 ω + (C3 ω + (Y n ω) ^ 4)) ∂μ :=
          integral_add hXfour hRest
        _ = _ := by rw [hRestIntegral]
    rw [centeredPartialSum_succ]
    calc
      ∫ ω, (X ω + Y n ω) ^ 4 ∂μ =
          ∫ ω, X ω ^ 4 ∂μ +
            (4 * ∫ ω, X ω ^ 3 * Y n ω ∂μ +
              (6 * ∫ ω, X ω ^ 2 * (Y n ω) ^ 2 ∂μ +
                (4 * ∫ ω, X ω * (Y n ω) ^ 3 ∂μ +
                  ∫ ω, (Y n ω) ^ 4 ∂μ))) := hExpansion
      _ = (n : ℝ) * ∫ ω, (Y 0 ω) ^ 4 ∂μ +
            3 * (n : ℝ) * ((n : ℝ) - 1) *
              (∫ ω, (Y 0 ω) ^ 2 ∂μ) ^ 2 +
              (4 * ((∫ ω, X ω ^ 3 ∂μ) * ∫ ω, Y n ω ∂μ) +
                (6 * ((∫ ω, X ω ^ 2 ∂μ) * ∫ ω, (Y n ω) ^ 2 ∂μ) +
                  (4 * ((∫ ω, X ω ∂μ) * ∫ ω, (Y n ω) ^ 3 ∂μ) +
                    ∫ ω, (Y 0 ω) ^ 4 ∂μ))) := by
          rw [hIndXcube.integral_fun_mul_eq_mul_integral
                hXcube.aestronglyMeasurable hY4.aestronglyMeasurable,
              hIndSquares.integral_fun_mul_eq_mul_integral
                hXsq.aestronglyMeasurable hYsq.aestronglyMeasurable,
              hIndYcube.integral_fun_mul_eq_mul_integral
                hX4.aestronglyMeasurable hYcube.aestronglyMeasurable,
              hY2eq, hY4eq, hX2eq, ih]
      _ = ((n + 1 : ℕ) : ℝ) * ∫ ω, (Y 0 ω) ^ 4 ∂μ +
            3 * ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1) *
              (∫ ω, (Y 0 ω) ^ 2 ∂μ) ^ 2 := by
          rw [hYmean, hXmean, hX2eq, hY2eq]
          push_cast
          ring

/-- A generic helper (not a paper result): the fourth moment is bounded quadratically
for every positive sum length. -/
theorem centeredPartialSum_fourth_moment_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hind : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i))
    (hid : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) (h4 : MemLp (Y 0) 4 μ)
    (hc : ∫ ω, Y 0 ω ∂μ = 0) {n : ℕ} (hn : 1 ≤ n) :
    ∫ ω, (centeredPartialSum Y n ω) ^ 4 ∂μ ≤
      (n : ℝ) ^ 2 *
        (∫ ω, (Y 0 ω) ^ 4 ∂μ + 3 * (∫ ω, (Y 0 ω) ^ 2 ∂μ) ^ 2) := by
  rw [centeredPartialSum_fourth_moment hind hmeas hid h4 hc n]
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h4nonneg : 0 ≤ ∫ ω, (Y 0 ω) ^ 4 ∂μ :=
    integral_nonneg (fun ω => by positivity)
  have h2sq : 0 ≤ (∫ ω, (Y 0 ω) ^ 2 ∂μ) ^ 2 := sq_nonneg _
  have hprod : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) * ∫ ω, (Y 0 ω) ^ 4 ∂μ :=
    mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hn')) h4nonneg
  have hterm : 0 ≤ 3 * (n : ℝ) * (∫ ω, (Y 0 ω) ^ 2 ∂μ) ^ 2 := by
    positivity
  nlinarith [hprod, hterm]

end DirectedDistances.Probability
