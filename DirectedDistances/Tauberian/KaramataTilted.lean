/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.KaramataMoments
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Topology.ContinuousMap.Compact

/-! # Actual exponentially tilted laws for the Laplace Tauberian argument

The scale carrier is strictly positive. All normalization denominators are
proved finite and strictly positive before a law is constructed. The family
has its literal normalized exponential weights, not a default branch. -/

public section
namespace DirectedDistances.Tauberian

open Set MeasureTheory Filter
open scoped Topology ENNReal

/-- Bounded nonnegative coefficients have a genuinely summable Laplace series
at every positive scale. -/
theorem summable_bounded_laplace (a : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a n)
    (ha₁ : ∀ n, a n ≤ 1) {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ => a n * Real.exp (-s * (n : ℝ))) := by
  have hg : Summable (fun n : ℕ => Real.exp (-s * (n : ℝ))) := by
    simpa only [mul_comm] using Real.summable_exp_nat_mul_iff.2 (neg_neg_of_pos hs)
  apply hg.of_nonneg_of_le
    (fun n => mul_nonneg (ha₀ n) (Real.exp_pos _).le)
  intro n
  exact (mul_le_mul_of_nonneg_right (ha₁ n) (Real.exp_pos _).le).trans_eq (one_mul _)

/-- One positive coefficient makes every positive-scale normalizer positive. -/
theorem bounded_laplace_pos (a : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a n)
    (ha₁ : ∀ n, a n ≤ 1) (hapos : ∃ n, 0 < a n) {s : ℝ} (hs : 0 < s) :
    0 < ∑' n : ℕ, a n * Real.exp (-s * (n : ℝ)) := by
  obtain ⟨n, hn⟩ := hapos
  exact (summable_bounded_laplace a ha₀ ha₁ hs).tsum_pos
    (fun n => mul_nonneg (ha₀ n) (Real.exp_pos _).le)
    n (mul_pos hn (Real.exp_pos _))

/-- A nonzero power-law limit rules out an identically zero coefficient
sequence, so positivity is a proved consequence of the Tauberian input. -/
theorem exists_pos_of_laplace_power_limit (a : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a n)
    {τ η : ℝ} (hη : 0 < η)
    (hlim : Tendsto (fun s : ℝ => s ^ τ *
      (∑' n : ℕ, a n * Real.exp (-s * (n : ℝ)))) (𝓝[>] (0 : ℝ)) (𝓝 η)) :
    ∃ n, 0 < a n := by
  by_contra hnot
  have hz (n : ℕ) : a n = 0 := le_antisymm (not_lt.1 (not_exists.1 hnot n)) (ha₀ n)
  simp only [hz, zero_mul, tsum_zero, mul_zero] at hlim
  exact hη.ne' (tendsto_nhds_unique hlim (tendsto_const_nhds (x := (0 : ℝ))))

/-- The ratio law follows from the actual power-law normalizer limit. -/
theorem tendsto_laplace_scale_ratio {Z : ℝ → ℝ} {τ η r : ℝ} (hη : η ≠ 0)
    (hr : 0 < r) (hlim : Tendsto (fun s : ℝ => s ^ τ * Z s)
      (𝓝[>] (0 : ℝ)) (𝓝 η)) :
    Tendsto (fun s : ℝ => Z (r * s) / Z s) (𝓝[>] (0 : ℝ)) (𝓝 (r ^ (-τ))) := by
  have hscale : Tendsto (fun s : ℝ => r * s) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have hc : Continuous (fun s : ℝ => r * s) := continuous_const.mul continuous_id
      simpa only [mul_zero] using (hc.tendsto 0).mono_left
        (y := 𝓝[>] (0 : ℝ)) nhdsWithin_le_nhds
    · filter_upwards [eventually_mem_nhdsWithin] with s hs
      exact mul_pos hr hs
  have hscaled := hlim.comp hscale
  have hh := (hscaled.div hlim hη).const_mul (r ^ (-τ))
  simp only [div_self hη, mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  have hR : r ^ τ ≠ 0 := (Real.rpow_pos_of_pos hr τ).ne'
  have hS : s ^ τ ≠ 0 := (Real.rpow_pos_of_pos hs τ).ne'
  change r ^ (-τ) * (((r * s) ^ τ * Z (r * s)) / (s ^ τ * Z s)) = Z (r * s) / Z s
  rw [Real.mul_rpow hr.le hs.le, Real.rpow_neg hr.le]
  calc
    (r ^ τ)⁻¹ * (r ^ τ * s ^ τ * Z (r * s) / (s ^ τ * Z s)) =
        (r ^ τ)⁻¹ * (r ^ τ * ((s ^ τ * Z (r * s)) / (s ^ τ * Z s))) := by ring
    _ = (s ^ τ * Z (r * s)) / (s ^ τ * Z s) := inv_mul_cancel_left₀ hR _
    _ = Z (r * s) / Z s := mul_div_mul_left _ _ hS

/-- The literal normalized positive-scale weights sum to one. -/
theorem normalized_laplace_hasSum (a : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a n)
    (ha₁ : ∀ n, a n ≤ 1) (hapos : ∃ n, 0 < a n) {s : ℝ} (hs : 0 < s) :
    HasSum (fun n : ℕ => a n * Real.exp (-s * (n : ℝ)) /
      (∑' m : ℕ, a m * Real.exp (-s * (m : ℝ)))) 1 := by
  have hz := (bounded_laplace_pos a ha₀ ha₁ hapos hs).ne'
  simpa only [div_self hz] using
    (summable_bounded_laplace a ha₀ ha₁ hs).hasSum.div_const
      (∑' m : ℕ, a m * Real.exp (-s * (m : ℝ)))

/-- Normalized weight positivity is proved on every positive scale. -/
theorem normalized_laplace_nonneg (a : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a n)
    (ha₁ : ∀ n, a n ≤ 1) (hapos : ∃ n, 0 < a n) {s : ℝ} (hs : 0 < s) (n : ℕ) :
    0 ≤ a n * Real.exp (-s * (n : ℝ)) /
      (∑' m : ℕ, a m * Real.exp (-s * (m : ℝ))) :=
  div_nonneg (mul_nonneg (ha₀ n) (Real.exp_pos _).le)
    (bounded_laplace_pos a ha₀ ha₁ hapos hs).le

/-- The literal probability masses of the positive-scale tilted law. Their
normalization was proved before this probability object is constructed. -/
@[expose] noncomputable def tiltedLaplacePMF (a : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a n)
    (ha₁ : ∀ n, a n ≤ 1) (hapos : ∃ n, 0 < a n) (s : {s : ℝ // 0 < s}) : PMF ℕ := by
  let w := fun n : ℕ => a n * Real.exp (-(s : ℝ) * (n : ℝ)) /
    (∑' m : ℕ, a m * Real.exp (-(s : ℝ) * (m : ℝ)))
  have hw : HasSum w 1 := normalized_laplace_hasSum a ha₀ ha₁ hapos s.property
  have hn (n : ℕ) : 0 ≤ w n := normalized_laplace_nonneg a ha₀ ha₁ hapos s.property n
  refine ⟨fun n => ENNReal.ofReal (w n), ?_⟩
  have ht : (∑' n : ℕ, ENNReal.ofReal (w n)) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hn hw.summable, hw.tsum_eq, ENNReal.ofReal_one]
  have hh : HasSum (fun n : ℕ => ENNReal.ofReal (w n))
      (∑' n : ℕ, ENNReal.ofReal (w n)) := CompleteLattice.summable.hasSum
  simpa only [ht] using hh

/-- The PMF exposes exactly its normalized exponential weights. -/
theorem tiltedLaplacePMF_apply (a : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a n)
    (ha₁ : ∀ n, a n ≤ 1) (hapos : ∃ n, 0 < a n) (s : {s : ℝ // 0 < s}) (n : ℕ) :
    tiltedLaplacePMF a ha₀ ha₁ hapos s n = ENNReal.ofReal
      (a n * Real.exp (-(s : ℝ) * (n : ℝ)) /
        (∑' m : ℕ, a m * Real.exp (-(s : ℝ) * (m : ℝ)))) := rfl

/-- Every positive-scale exponential image lies in the actual compact carrier. -/
@[expose] noncomputable def laplaceExpPoint (s : {s : ℝ // 0 < s}) (n : ℕ) : Icc (0 : ℝ) 1 :=
  ⟨Real.exp (-(s : ℝ) * (n : ℝ)), (Real.exp_pos _).le,
    Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.2 s.property.le) (Nat.cast_nonneg n))⟩

/-- The compactly supported tilted probability law, on positive scales only. -/
@[expose] noncomputable def tiltedLaplaceLaw (a : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a n)
    (ha₁ : ∀ n, a n ≤ 1) (hapos : ∃ n, 0 < a n) (s : {s : ℝ // 0 < s}) :
    ProbabilityMeasure (Icc (0 : ℝ) 1) :=
  (tiltedLaplacePMF a ha₀ ha₁ hapos s).toMeasure.toProbabilityMeasure.map (laplaceExpPoint s)

/-- The image map retains exactly `exp(-s*n)`. -/
theorem laplaceExpPoint_coe (s : {s : ℝ // 0 < s}) (n : ℕ) :
    (laplaceExpPoint s n : ℝ) = Real.exp (-(s : ℝ) * (n : ℝ)) := rfl

/-- The actual compact tilted law has the exact Laplace-ratio monomial moments. -/
theorem integral_tiltedLaplaceLaw_monomial (a : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a n)
    (ha₁ : ∀ n, a n ≤ 1) (hapos : ∃ n, 0 < a n) (s : {s : ℝ // 0 < s}) (k : ℕ) :
    (∫ y : Icc (0 : ℝ) 1, (y : ℝ) ^ k
      ∂(tiltedLaplaceLaw a ha₀ ha₁ hapos s : Measure (Icc (0 : ℝ) 1))) =
      (∑' n : ℕ, a n * Real.exp (-(((k : ℝ) + 1) * (s : ℝ)) * (n : ℝ))) /
        (∑' n : ℕ, a n * Real.exp (-(s : ℝ) * (n : ℝ))) := by
  let p := tiltedLaplacePMF a ha₀ ha₁ hapos s
  have hpoint : Measurable (laplaceExpPoint s) := measurable_of_countable _
  have htest : Integrable (fun y : Icc (0 : ℝ) 1 => (y : ℝ) ^ k)
      (tiltedLaplaceLaw a ha₀ ha₁ hapos s : Measure (Icc (0 : ℝ) 1)) :=
    (BoundedContinuousFunction.mkOfCompact
      ⟨fun y : Icc (0 : ℝ) 1 => (y : ℝ) ^ k, continuous_subtype_val.pow k⟩).integrable _
  have hm : StronglyMeasurable (fun y : Icc (0 : ℝ) 1 => (y : ℝ) ^ k) :=
    (continuous_subtype_val.pow k).stronglyMeasurable
  change Integrable (fun y : Icc (0 : ℝ) 1 => (y : ℝ) ^ k)
    (p.toMeasure.map (laplaceExpPoint s)) at htest
  have hi : Integrable (fun n : ℕ => (laplaceExpPoint s n : ℝ) ^ k) p.toMeasure :=
    (integrable_map_measure hm.aestronglyMeasurable hpoint.aemeasurable).1 htest
  change (∫ y : Icc (0 : ℝ) 1, (y : ℝ) ^ k ∂(p.toMeasure.map (laplaceExpPoint s))) = _
  rw [integral_map_of_stronglyMeasurable hpoint hm, PMF.integral_eq_tsum p _ hi]
  have hpw (n : ℕ) : (p n).toReal =
      a n * Real.exp (-(s : ℝ) * (n : ℝ)) /
        (∑' m : ℕ, a m * Real.exp (-(s : ℝ) * (m : ℝ))) := by
    change (tiltedLaplacePMF a ha₀ ha₁ hapos s n).toReal = _
    rw [tiltedLaplacePMF_apply, ENNReal.toReal_ofReal
      (normalized_laplace_nonneg a ha₀ ha₁ hapos s.property n)]
  simp_rw [hpw, laplaceExpPoint_coe, smul_eq_mul]
  rw [← tsum_div_const]
  apply tsum_congr
  intro n
  rw [← Real.exp_nat_mul]
  have he : Real.exp (-(s : ℝ) * (n : ℝ)) *
      Real.exp ((k : ℝ) * (-(s : ℝ) * (n : ℝ))) =
        Real.exp (-(((k : ℝ) + 1) * (s : ℝ)) * (n : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = a n * (Real.exp (-(s : ℝ) * (n : ℝ)) *
        Real.exp ((k : ℝ) * (-(s : ℝ) * (n : ℝ)))) /
          (∑' m : ℕ, a m * Real.exp (-(s : ℝ) * (m : ℝ))) := by ring
    _ = _ := by rw [he]

/-- The power-law input constructs an actual tilted family and proves every
moment identity and limiting moment. No family or moment convergence is assumed. -/
theorem exists_tiltedLaplaceLaw_moments (a : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a n)
    (ha₁ : ∀ n, a n ≤ 1) {τ η : ℝ} (_hτ : 0 < τ) (hη : 0 < η)
    (hlim : Tendsto (fun s : ℝ => s ^ τ *
      (∑' n : ℕ, a n * Real.exp (-s * (n : ℝ)))) (𝓝[>] (0 : ℝ)) (𝓝 η)) :
    ∃ μs : {s : ℝ // 0 < s} → ProbabilityMeasure (Icc (0 : ℝ) 1),
      (∀ (s : {s : ℝ // 0 < s}) (k : ℕ),
        (∫ y : Icc (0 : ℝ) 1, (y : ℝ) ^ k ∂(μs s : Measure (Icc (0 : ℝ) 1))) =
          (∑' n : ℕ, a n * Real.exp (-(((k : ℝ) + 1) * (s : ℝ)) * (n : ℝ))) /
            (∑' n : ℕ, a n * Real.exp (-(s : ℝ) * (n : ℝ)))) ∧
      ∀ k : ℕ, Tendsto
        (fun s : {s : ℝ // 0 < s} => ∫ y : Icc (0 : ℝ) 1, (y : ℝ) ^ k
          ∂(μs s : Measure (Icc (0 : ℝ) 1)))
        (Filter.comap (fun s : {s : ℝ // 0 < s} => (s : ℝ)) (𝓝[>] (0 : ℝ)))
        (𝓝 (((k : ℝ) + 1) ^ (-τ))) := by
  have hapos := exists_pos_of_laplace_power_limit a ha₀ hη hlim
  let μs := tiltedLaplaceLaw a ha₀ ha₁ hapos
  refine ⟨μs, (fun s k => integral_tiltedLaplaceLaw_monomial a ha₀ ha₁ hapos s k), ?_⟩
  intro k
  have hr : 0 < (k : ℝ) + 1 := by positivity
  have hh := tendsto_laplace_scale_ratio hη.ne' hr hlim
  have hc : Tendsto (fun s : {s : ℝ // 0 < s} => (s : ℝ))
      (Filter.comap (fun s : {s : ℝ // 0 < s} => (s : ℝ)) (𝓝[>] (0 : ℝ)))
      (𝓝[>] (0 : ℝ)) := tendsto_comap
  simpa only [μs, Function.comp_def, integral_tiltedLaplaceLaw_monomial] using hh.comp hc

end DirectedDistances.Tauberian
