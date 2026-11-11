/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.GeneratingFunctionLaw
public import DirectedDistances.Tauberian.MonotoneDensity







public section
namespace DirectedDistances.Tauberian
open MeasureTheory Filter Set
open scoped Topology

/-- The strict real cutoff uses the next natural index, with asymptotic
relative size one. -/
theorem tendsto_floor_add_one_div :
    Tendsto (fun R : ℝ => ((⌊R⌋₊ + 1 : ℕ) : ℝ) / R) atTop (𝓝 1) := by
  have h := (tendsto_nat_floor_div_atTop (R := ℝ)).add tendsto_inv_atTop_zero
  simpa only [Nat.cast_add, Nat.cast_one, add_div, one_div, add_zero] using h

/-- A natural-index power limit gives its strict real-cutoff power limit,
with no restriction on the real exponent. -/
theorem tendsto_power_limit_real_cutoff (S : ℕ → ℝ) {C ρ : ℝ}
    (hS : Tendsto (fun N : ℕ => S N / (N : ℝ) ^ ρ) atTop (𝓝 C)) :
    Tendsto (fun R : ℝ => S (⌊R⌋₊ + 1) / R ^ ρ) atTop (𝓝 C) := by
  have hidx : Tendsto (fun R : ℝ => ⌊R⌋₊ + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop
  have hp := (Real.continuousAt_rpow_const 1 ρ (Or.inl one_ne_zero)).tendsto.comp
    tendsto_floor_add_one_div
  have hh := (hS.comp hidx).mul hp
  have hh' : Tendsto
      (fun R : ℝ => (S (⌊R⌋₊ + 1) / ((⌊R⌋₊ + 1 : ℕ) : ℝ) ^ ρ) *
        (((⌊R⌋₊ + 1 : ℕ) : ℝ) / R) ^ ρ) atTop (𝓝 C) := by
    simpa only [Function.comp_apply, Real.one_rpow, mul_one] using hh
  apply hh'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hn : (0 : ℝ) < ((⌊R⌋₊ + 1 : ℕ) : ℝ) := by positivity
  rw [Real.div_rpow hn.le hR.le]
  field_simp [(Real.rpow_pos_of_pos hn ρ).ne', (Real.rpow_pos_of_pos hR ρ).ne']

/-- The strict real tail event is precisely the disjoint union of the
fibers starting at `floor R + 1`, including integer and zero cutoffs. -/
theorem real_tail_eq_iUnion_probability_fiber {Ω : Type*} (X : Ω → ℕ)
    {R : ℝ} (hR : 0 ≤ R) :
    {ω | R < (X ω : ℝ)} = ⋃ j : ℕ, X ⁻¹' {j + (⌊R⌋₊ + 1)} := by
  ext ω
  simp only [mem_ofPred_eq, mem_iUnion, mem_preimage, mem_singleton_iff]
  rw [← Nat.floor_lt hR]
  constructor
  · intro h
    refine ⟨X ω - (⌊R⌋₊ + 1), ?_⟩
    omega
  · rintro ⟨j, hj⟩
    omega

/-- The real tail probability equals the actual shifted sum of fiber masses.
No distributional identification or summability premise is assumed. -/
theorem probability_real_tail_eq_tsum_fiber {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℕ}
    (hX : Measurable X) {R : ℝ} (hR : 0 ≤ R) :
    μ.real {ω | R < (X ω : ℝ)} =
      ∑' j : ℕ, μ.real (X ⁻¹' {j + (⌊R⌋₊ + 1)}) := by
  have hd : Pairwise (fun i j : ℕ => Disjoint (X ⁻¹' {i + (⌊R⌋₊ + 1)})
      (X ⁻¹' {j + (⌊R⌋₊ + 1)})) := by
    intro i j hij
    apply Set.disjoint_left.2
    intro ω hi hj
    simp only [mem_preimage, mem_singleton_iff] at hi hj
    exact hij (by omega)
  rw [real_tail_eq_iUnion_probability_fiber X hR, Measure.real,
    measure_iUnion hd (fun j => hX (measurableSet_singleton _)),
    ENNReal.tsum_toReal_eq (fun j => measure_ne_top μ _)]
  rfl


/-- The shifted fiber series genuinely sums to the real tail probability. -/
theorem hasSum_probability_fiber_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℕ}
    (hX : Measurable X) {R : ℝ} (hR : 0 ≤ R) :
    HasSum (fun j : ℕ => μ.real (X ⁻¹' {j + (⌊R⌋₊ + 1)}))
      (μ.real {ω | R < (X ω : ℝ)}) := by
  rw [probability_real_tail_eq_tsum_fiber hX hR]
  exact ((summable_nat_add_iff (⌊R⌋₊ + 1)).2
    (hasSum_probability_fiber hX).summable).hasSum

/-- A proved sequence tail limit transfers to the literal real tail
probability of the same natural-valued random variable. -/
theorem tendsto_probability_real_tail_of_fiber_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℕ}
    (hX : Measurable X) {C ρ : ℝ}
    (hS : Tendsto (fun N : ℕ =>
      (∑' j : ℕ, μ.real (X ⁻¹' {j + N})) / (N : ℝ) ^ ρ) atTop (𝓝 C)) :
    Tendsto (fun R : ℝ => μ.real {ω | R < (X ω : ℝ)} / R ^ ρ) atTop (𝓝 C) := by
  apply (tendsto_power_limit_real_cutoff
    (fun N => ∑' j : ℕ, μ.real (X ⁻¹' {j + N})) hS).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  rw [probability_real_tail_eq_tsum_fiber hX hR]

/-- A normalized real power limit gives the corresponding literal little-o
remainder, with the nonzero denominator proved on the eventual domain. -/
theorem isLittleO_sub_mul_rpow_of_tendsto {F : ℝ → ℝ} {C ρ : ℝ}
    (hF : Tendsto (fun R : ℝ => F R / R ^ ρ) atTop (𝓝 C)) :
    (fun R : ℝ => F R - C * R ^ ρ) =o[atTop] (fun R : ℝ => R ^ ρ) := by
  have hzero : ∀ᶠ R : ℝ in atTop, R ^ ρ = 0 → F R - C * R ^ ρ = 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact fun h => ((Real.rpow_pos_of_pos hR ρ).ne' h).elim
  apply (Asymptotics.isLittleO_iff_tendsto' hzero).2
  have ht : Tendsto (fun R : ℝ => F R / R ^ ρ - C) atTop (𝓝 0) := by
    simpa only [sub_self] using hF.sub_const C
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [sub_div, mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos hR ρ).ne']

/-- The source real-tail asymptotic remainder follows from a proved natural
fiber-tail limit, for the actual probability and every real exponent. -/
theorem probability_real_tail_isLittleO_of_fiber_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℕ}
    (hX : Measurable X) {C ρ : ℝ}
    (hS : Tendsto (fun N : ℕ =>
      (∑' j : ℕ, μ.real (X ⁻¹' {j + N})) / (N : ℝ) ^ ρ) atTop (𝓝 C)) :
    (fun R : ℝ => μ.real {ω | R < (X ω : ℝ)} - C * R ^ ρ) =o[atTop]
      (fun R : ℝ => R ^ ρ) :=
  isLittleO_sub_mul_rpow_of_tendsto (tendsto_probability_real_tail_of_fiber_tail hX hS)

end DirectedDistances.Tauberian
