/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.PowerCos
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Compact-interval scaling of regularly varying tails

Necessary analytic dependencies for the revised proof of Appendix A.4,
`lem:bound-im-part`. This file handles compact cutoffs; oscillatory infinite
tails require separate monotonicity estimates. In particular a pointwise
little-o bound is never integrated over the entire half-line in absolute value. -/

public section
namespace DirectedDistances.Tauberian

open Set MeasureTheory Filter
open scoped Topology Interval

/-- The next positive mesh point tends to the point being discretized. -/
theorem tendsto_next_mesh_point {u : ℝ} (hu : 0 < u) :
    Tendsto (fun t : ℝ => (((⌊u / t⌋₊ + 1 : ℕ) : ℝ) * t))
      (𝓝[>] 0) (𝓝 u) := by
  have ht0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun _ => u) (h := fun t => u + t)
    tendsto_const_nhds (by simpa using (tendsto_const_nhds.add ht0))
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have h := Nat.lt_floor_add_one (u / t)
    simpa only [Nat.cast_add, Nat.cast_one] using ((div_lt_iff₀ ht).1 h).le
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have h := Nat.floor_le (div_nonneg hu.le ht.le)
    have h' := (le_div_iff₀ ht).1 h
    push_cast
    nlinarith only [h']

/-- The mesh index diverges when the positive scale tends to zero. -/
theorem tendsto_next_mesh_index {u : ℝ} (hu : 0 < u) :
    Tendsto (fun t : ℝ => ⌊u / t⌋₊ + 1) (𝓝[>] 0) atTop := by
  apply tendsto_atTop.2
  intro n
  have ht0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ t : ℝ in 𝓝[>] 0, t < u / ((n : ℝ) + 1) from
      ht0.eventually (Iio_mem_nhds (by positivity)))] with t ht hsmall
  change 0 < t at ht
  have h : (n : ℝ) < u / t := by
    apply (lt_div_iff₀ ht).2
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).1 hsmall
    nlinarith only [hh, ht]
  exact (Nat.le_floor h.le).trans (Nat.le_succ _)

/-- Convergence of the power-normalized sequence supplies one bound for every
positive index, including its finite initial segment. -/
theorem exists_bound_power_normalized_sequence (S : ℕ → ℝ) {c ν : ℝ}
    (hlim : Tendsto (fun n : ℕ => S n / (n : ℝ) ^ (-ν)) atTop (𝓝 c)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖S (n + 1)‖ ≤ C * ((n + 1 : ℕ) : ℝ) ^ (-ν) := by
  have hh := hlim.comp (tendsto_add_atTop_nat 1)
  obtain ⟨C, hCpos, hC⟩ := hh.cauchySeq.isBounded_range.exists_pos_norm_le
  refine ⟨C, hCpos, ?_⟩
  intro n
  have hp : 0 < ((n + 1 : ℕ) : ℝ) ^ (-ν) := Real.rpow_pos_of_pos (by positivity) _
  have hb := hC _ (mem_range_self n)
  dsimp only [Function.comp_apply] at hb
  simp only [norm_div, Real.norm_eq_abs, abs_of_pos hp] at hb
  simpa only [Real.norm_eq_abs] using (div_le_iff₀ hp).1 hb

/-- Pointwise scaling at every positive spatial point, using the original
sequence asymptotic rather than assuming a staircase limit. -/
theorem tendsto_scaled_staircase (S : ℕ → ℝ) {c ν u : ℝ} (hu : 0 < u)
    (hlim : Tendsto (fun n : ℕ => S n / (n : ℝ) ^ (-ν)) atTop (𝓝 c)) :
    Tendsto (fun t : ℝ => t ^ (-ν) * S (⌊u / t⌋₊ + 1)) (𝓝[>] 0)
      (𝓝 (c * u ^ (-ν))) := by
  have hp := (Real.continuousAt_rpow_const u (-ν) (Or.inl hu.ne')).tendsto.comp
    (tendsto_next_mesh_point hu)
  have hh := (hlim.comp (tendsto_next_mesh_index hu)).mul hp
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have hn : 0 < ((⌊u / t⌋₊ + 1 : ℕ) : ℝ) := by positivity
  dsimp only [Function.comp_apply]
  rw [Real.mul_rpow hn.le ht.le]
  have hn' := (Real.rpow_pos_of_pos hn (-ν)).ne'
  field_simp

/-- A global sequence bound gives an integrable spatial majorant independent
of the positive mesh size. -/
theorem norm_scaled_staircase_le (S : ℕ → ℝ) {ν C t u : ℝ}
    (hν : 0 ≤ ν) (hC : 0 ≤ C)
    (hS : ∀ n : ℕ, ‖S (n + 1)‖ ≤ C * ((n + 1 : ℕ) : ℝ) ^ (-ν))
    (ht : 0 < t) (hu : 0 < u) :
    ‖t ^ (-ν) * S (⌊u / t⌋₊ + 1)‖ ≤ C * u ^ (-ν) := by
  have hn : 0 < ((⌊u / t⌋₊ + 1 : ℕ) : ℝ) := by positivity
  have hu' : u ≤ ((⌊u / t⌋₊ + 1 : ℕ) : ℝ) * t := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((div_lt_iff₀ ht).1 (Nat.lt_floor_add_one (u / t))).le
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht _)]
  calc
    _ ≤ t ^ (-ν) * (C * ((⌊u / t⌋₊ + 1 : ℕ) : ℝ) ^ (-ν)) :=
      mul_le_mul_of_nonneg_left (hS _) (Real.rpow_nonneg ht.le _)
    _ = C * (((⌊u / t⌋₊ + 1 : ℕ) : ℝ) * t) ^ (-ν) := by
      rw [Real.mul_rpow hn.le ht.le]
      ring
    _ ≤ C * u ^ (-ν) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hu hu' (neg_nonpos.2 hν)) hC

/-- Dominated convergence on a compact positive interval. The same global
power majorant controls every mesh size; its singularity is integrable because
`ν < 1`. This is a compact result, not an absolute tail estimate at infinity. -/
theorem tendsto_integral_scaled_staircase_cos_cutoff (S : ℕ → ℝ) {c ν A : ℝ}
    (hν₀ : 0 ≤ ν) (hν₁ : ν < 1) (hA : 0 ≤ A)
    (hlim : Tendsto (fun n : ℕ => S n / (n : ℝ) ^ (-ν)) atTop (𝓝 c)) :
    Tendsto (fun t : ℝ => ∫ u : ℝ in (0 : ℝ)..A,
      (t ^ (-ν) * S (⌊u / t⌋₊ + 1)) * Real.cos u)
      (𝓝[>] 0) (𝓝 (∫ u : ℝ in (0 : ℝ)..A,
        (c * u ^ (-ν)) * Real.cos u)) := by
  obtain ⟨C, hC, hS⟩ := exists_bound_power_normalized_sequence S hlim
  simp only [intervalIntegral.integral_of_le hA]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => C * u ^ (-ν))
  · apply Eventually.of_forall
    intro t
    exact (((measurable_of_countable (fun n : ℕ => S (n + 1))).comp
      (Nat.measurable_floor.comp (measurable_id.div_const t))).const_mul
        (t ^ (-ν))).mul Real.continuous_cos.measurable |>.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [norm_mul]
    calc
      _ ≤ ‖t ^ (-ν) * S (⌊u / t⌋₊ + 1)‖ * 1 :=
        mul_le_mul_of_nonneg_left
          (by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one u) (norm_nonneg _)
      _ ≤ C * u ^ (-ν) := by
        rw [mul_one]
        exact norm_scaled_staircase_le S hν₀ hC.le hS ht hu.1
  · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hA).1
      (intervalIntegrable_rpow_neg hν₁)).const_mul C
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (tendsto_scaled_staircase S hu.1 hlim).mul_const (Real.cos u)

end DirectedDistances.Tauberian
