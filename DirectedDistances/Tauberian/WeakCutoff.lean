/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! # A bounded reciprocal cutoff under weak convergence

Desmoothing infrastructure for the Laplace Tauberian argument: on `[0,1]`,
weak convergence implies convergence against `if a ≤ y then y⁻¹ else 0`
when the limiting measure has no atom at `a > 0`. No moment or desired
cutoff-integral convergence is assumed. -/

public section
namespace DirectedDistances.Tauberian

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

/-- A nonnegative reciprocal cutoff has a fixed finite bound. -/
theorem reciprocal_cutoff_bounds {a : ℝ} (ha : 0 < a) (y : Icc (0 : ℝ) 1) :
    0 ≤ (if a ≤ (y : ℝ) then (y : ℝ)⁻¹ else 0) ∧
      (if a ≤ (y : ℝ) then (y : ℝ)⁻¹ else 0) ≤ a⁻¹ := by
  by_cases h : a ≤ (y : ℝ)
  · simp only [h, ↓reduceIte]
    exact ⟨inv_nonneg.mpr (ha.le.trans h), inv_anti₀ ha h⟩
  · simp only [h, ↓reduceIte, le_refl, inv_nonneg.mpr ha.le, and_self]

/-- The reciprocal cutoff is Borel measurable, including its jump point. -/
theorem measurable_reciprocal_cutoff (a : ℝ) :
    Measurable (fun y : Icc (0 : ℝ) 1 => if a ≤ (y : ℝ) then (y : ℝ)⁻¹ else 0) :=
  Measurable.ite (measurableSet_le measurable_const measurable_subtype_coe)
    measurable_subtype_coe.inv measurable_const

/-- The reciprocal cutoff has an actual integral against every probability
measure on the unit interval. -/
theorem integrable_reciprocal_cutoff {a : ℝ} (ha : 0 < a)
    (μ : ProbabilityMeasure (Icc (0 : ℝ) 1)) :
    Integrable (fun y : Icc (0 : ℝ) 1 => if a ≤ (y : ℝ) then (y : ℝ)⁻¹ else 0)
      (μ : Measure (Icc (0 : ℝ) 1)) := by
  apply (integrable_const a⁻¹).mono' (measurable_reciprocal_cutoff a).aestronglyMeasurable
  exact ae_of_all _ fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (reciprocal_cutoff_bounds ha y).1]
    exact (reciprocal_cutoff_bounds ha y).2

/-- Away from the threshold, the cutoff is continuous; its only possible
discontinuity is the point carrying the explicit no-atom condition. -/
theorem continuousAt_reciprocal_cutoff {a : ℝ} (ha : 0 < a)
    (y : Icc (0 : ℝ) 1) (hy : (y : ℝ) ≠ a) :
    ContinuousAt (fun z : Icc (0 : ℝ) 1 => if a ≤ (z : ℝ) then (z : ℝ)⁻¹ else 0) y := by
  by_cases h : a < (y : ℝ)
  · apply (continuous_subtype_val.continuousAt.inv₀ (ne_of_gt (ha.trans h))).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const continuous_subtype_val).mem_nhds h] with z hz
    exact ite_eq_left hz.le
  · apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    have hya : (y : ℝ) < a := lt_of_le_of_ne (le_of_not_gt h) hy
    filter_upwards [(isOpen_lt continuous_subtype_val continuous_const).mem_nhds hya] with z hz
    exact ite_eq_right (not_le.mpr hz)

/-- Two sequences of continuous tests with converging limiting integrals
squeeze an arbitrary integrable test under weak convergence. -/
theorem tendsto_integral_of_continuous_sandwich
    {Ω ι : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [BorelSpace Ω]
    {l : Filter ι} {μs : ι → ProbabilityMeasure Ω} {ν : ProbabilityMeasure Ω}
    (hweak : Tendsto μs l (𝓝 ν)) (h : Ω → ℝ)
    (hi : ∀ μ : ProbabilityMeasure Ω, Integrable h (μ : Measure Ω))
    (lo up : ℕ → (Ω →ᵇ ℝ))
    (hlo : ∀ n x, lo n x ≤ h x) (hup : ∀ n x, h x ≤ up n x)
    (hl : Tendsto (fun n => ∫ x, lo n x ∂(ν : Measure Ω)) atTop
      (𝓝 (∫ x, h x ∂(ν : Measure Ω))))
    (hu : Tendsto (fun n => ∫ x, up n x ∂(ν : Measure Ω)) atTop
      (𝓝 (∫ x, h x ∂(ν : Measure Ω)))) :
    Tendsto (fun i => ∫ x, h x ∂(μs i : Measure Ω)) l
      (𝓝 (∫ x, h x ∂(ν : Measure Ω))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((Metric.tendsto_nhds.mp hl (ε / 2) (half_pos hε)).and
      (Metric.tendsto_nhds.mp hu (ε / 2) (half_pos hε)))
  have htests := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak
  filter_upwards [Metric.tendsto_nhds.mp (htests (lo N)) (ε / 2) (half_pos hε),
    Metric.tendsto_nhds.mp (htests (up N)) (ε / 2) (half_pos hε)] with i hli hui
  have hlow := integral_mono ((lo N).integrable _) (hi (μs i)) (hlo N)
  have hupp := integral_mono (hi (μs i)) ((up N).integrable _) (hup N)
  have hN' := hN N le_rfl
  rw [Real.dist_eq, abs_lt] at hli hui ⊢
  rcases hN' with ⟨hNl, hNu⟩
  rw [Real.dist_eq, abs_lt] at hNl hNu
  constructor <;> linarith only [hli.1, hli.2, hui.1, hui.2,
    hNl.1, hNl.2, hNu.1, hNu.2, hlow, hupp]

/-- Weak convergence controls the reciprocal cutoff whenever the limiting
probability has no mass at its sole possible discontinuity. The parameter
filter is arbitrary, and hence includes approach to zero from above. -/
theorem tendsto_integral_reciprocal_cutoff {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure (Icc (0 : ℝ) 1)}
    {ν : ProbabilityMeasure (Icc (0 : ℝ) 1)}
    (hweak : Tendsto μs l (𝓝 ν)) {a : ℝ} (ha : 0 < a) (_ha1 : a < 1)
    (hna : (ν : Measure (Icc (0 : ℝ) 1)) {y | (y : ℝ) = a} = 0) :
    Tendsto
      (fun i => ∫ y : Icc (0 : ℝ) 1,
        (if a ≤ (y : ℝ) then (y : ℝ)⁻¹ else 0) ∂(μs i : Measure (Icc (0 : ℝ) 1))) l
      (𝓝 (∫ y : Icc (0 : ℝ) 1,
        (if a ≤ (y : ℝ) then (y : ℝ)⁻¹ else 0) ∂(ν : Measure (Icc (0 : ℝ) 1)))) := by
  let g : Icc (0 : ℝ) 1 →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun y => (max a (y : ℝ))⁻¹,
      (continuous_const.max continuous_subtype_val).inv₀
        (fun y => ne_of_gt (ha.trans_le (le_max_left _ _)))⟩
  have hg0 (y : Icc (0 : ℝ) 1) : 0 ≤ g y :=
    inv_nonneg.mpr (ha.le.trans (le_max_left _ _))
  have hgb (y : Icc (0 : ℝ) 1) : g y ≤ a⁻¹ := inv_anti₀ ha (le_max_left _ _)
  have hC : IsClosed {y : Icc (0 : ℝ) 1 | a ≤ (y : ℝ)} :=
    isClosed_le continuous_const continuous_subtype_val
  have hD : IsClosed {y : Icc (0 : ℝ) 1 | (y : ℝ) ≤ a} :=
    isClosed_le continuous_subtype_val continuous_const
  let rC (n : ℕ) : Icc (0 : ℝ) 1 →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun y => (hC.apprSeq n y : ℝ),
      NNReal.continuous_coe.comp (hC.apprSeq n).continuous⟩
  let rD (n : ℕ) : Icc (0 : ℝ) 1 →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun y => (hD.apprSeq n y : ℝ),
      NNReal.continuous_coe.comp (hD.apprSeq n).continuous⟩
  have hrC (n : ℕ) (y : Icc (0 : ℝ) 1) : 0 ≤ rC n y ∧ rC n y ≤ 1 :=
    ⟨(hC.apprSeq n y).coe_nonneg, HasOuterApproxClosed.apprSeq_apply_le_one hC n y⟩
  have hrD (n : ℕ) (y : Icc (0 : ℝ) 1) : 0 ≤ rD n y ∧ rD n y ≤ 1 :=
    ⟨(hD.apprSeq n y).coe_nonneg, HasOuterApproxClosed.apprSeq_apply_le_one hD n y⟩
  let lo (n : ℕ) := g * (1 - rD n)
  let up (n : ℕ) := g * rC n
  have hlow (n : ℕ) (y : Icc (0 : ℝ) 1) :
      lo n y ≤ if a ≤ (y : ℝ) then (y : ℝ)⁻¹ else 0 := by
    change g y * (1 - rD n y) ≤ _
    by_cases hy : a ≤ (y : ℝ)
    · have hgy : g y = (y : ℝ)⁻¹ := by dsimp [g]; rw [max_eq_right hy]
      rw [ite_eq_left hy, ← hgy]
      exact mul_le_of_le_one_right (hg0 y) (sub_le_self _ (hrD n y).1)
    · have hd : rD n y = 1 := by
        change (hD.apprSeq n y : ℝ) = 1
        exact_mod_cast HasOuterApproxClosed.apprSeq_apply_eq_one hD n (le_of_not_ge hy)
      rw [ite_eq_right hy, hd, sub_self, mul_zero]
  have hupp (n : ℕ) (y : Icc (0 : ℝ) 1) :
      (if a ≤ (y : ℝ) then (y : ℝ)⁻¹ else 0) ≤ up n y := by
    change _ ≤ g y * rC n y
    by_cases hy : a ≤ (y : ℝ)
    · have hc : rC n y = 1 := by
        change (hC.apprSeq n y : ℝ) = 1
        exact_mod_cast HasOuterApproxClosed.apprSeq_apply_eq_one hC n hy
      rw [ite_eq_left hy, hc, mul_one]
      dsimp [g]
      rw [max_eq_right hy]
    · rw [ite_eq_right hy]
      exact mul_nonneg (hg0 y) (hrC n y).1
  have hbound (r : ℝ) (y : Icc (0 : ℝ) 1) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
      ‖g y * r‖ ≤ a⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg0 y) hr)]
    exact (mul_le_of_le_one_right (hg0 y) hr1).trans (hgb y)
  have hlimC (y : Icc (0 : ℝ) 1) : Tendsto (fun n => rC n y) atTop
      (𝓝 (if a ≤ (y : ℝ) then (1 : ℝ) else 0)) := by
    have ht := (tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq hC)) y
    have ht' := NNReal.continuous_coe.continuousAt.tendsto.comp ht
    change Tendsto (fun n => (hC.apprSeq n y : ℝ)) atTop _
    simpa only [Function.comp_def, Set.indicator_apply, Set.mem_ofPred_eq, apply_ite,
      NNReal.coe_one, NNReal.coe_zero] using ht'
  have hlimD (y : Icc (0 : ℝ) 1) : Tendsto (fun n => rD n y) atTop
      (𝓝 (if (y : ℝ) ≤ a then (1 : ℝ) else 0)) := by
    have ht := (tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq hD)) y
    have ht' := NNReal.continuous_coe.continuousAt.tendsto.comp ht
    change Tendsto (fun n => (hD.apprSeq n y : ℝ)) atTop _
    simpa only [Function.comp_def, Set.indicator_apply, Set.mem_ofPred_eq, apply_ite,
      NNReal.coe_one, NNReal.coe_zero] using ht'
  apply tendsto_integral_of_continuous_sandwich hweak _
    (integrable_reciprocal_cutoff ha) lo up hlow hupp
  · apply tendsto_integral_of_dominated_convergence (fun _ => a⁻¹)
      (fun n => (lo n).continuous.measurable.aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ fun y => hbound _ y (sub_nonneg.mpr (hrD n y).2)
        (sub_le_self _ (hrD n y).1))
    have hne : ∀ᵐ (y : Icc (0 : ℝ) 1) ∂(ν : Measure (Icc (0 : ℝ) 1)), (y : ℝ) ≠ a := by
      simpa only [ae_iff, not_not] using hna
    filter_upwards [hne] with y hy
    change Tendsto (fun n => g y * (1 - rD n y)) atTop _
    have ht := ((tendsto_const_nhds (x := (1 : ℝ))).sub (hlimD y)).const_mul (g y)
    by_cases hya : a ≤ (y : ℝ)
    · have hgt : ¬(y : ℝ) ≤ a := not_le.mpr (lt_of_le_of_ne hya (Ne.symm hy))
      have hgy : g y = (y : ℝ)⁻¹ := by dsimp [g]; rw [max_eq_right hya]
      rw [ite_eq_left hya, ← hgy]
      simpa only [ite_eq_right hgt, sub_zero, mul_one] using ht
    · simpa only [ite_eq_right hya, ite_eq_left (le_of_not_ge hya), sub_self, mul_zero] using ht
  · apply tendsto_integral_of_dominated_convergence (fun _ => a⁻¹)
      (fun n => (up n).continuous.measurable.aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ fun y => hbound _ y (hrC n y).1 (hrC n y).2)
    apply ae_of_all
    intro y
    change Tendsto (fun n => g y * rC n y) atTop _
    have ht := (hlimC y).const_mul (g y)
    by_cases hya : a ≤ (y : ℝ)
    · have hgy : g y = (y : ℝ)⁻¹ := by dsimp [g]; rw [max_eq_right hya]
      rw [ite_eq_left hya, ← hgy]
      simpa only [ite_eq_left hya, mul_one] using ht
    · simpa only [ite_eq_right hya, mul_zero] using ht

end DirectedDistances.Tauberian
