/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.TauberianPower
public import DirectedDistances.Tauberian.RegularVariationAbel
import DirectedDistances.Tauberian.ImproperAbel







public section
namespace DirectedDistances.Tauberian
open Filter
open scoped Topology

/-- The imaginary part of the actual PGF on the circle equals its genuine
sine series. Complex summability is proved before taking the imaginary part. -/
theorem im_pgf_exp_eq_sine_tsum {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hs : Summable f) (t : ℝ) :
    (∑' k : ℕ, (f k : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ^ k).im =
      ∑' k : ℕ, f k * Real.sin ((k : ℝ) * t) := by
  have hc := hasSum_weighted_pow hf hs
    (le_of_eq (Complex.norm_exp_ofReal_mul_I t))
  rw [Complex.im_tsum hc.summable]
  apply tsum_congr
  intro k
  rw [← Complex.exp_nat_mul, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, Complex.exp_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, add_zero, mul_one, Real.exp_zero, one_mul]

/-- The source two-sided boundary remainder itself supplies the positive-angle
normalized sine limit; this is not an additional asymptotic premise. -/
theorem tendsto_sine_div_rpow_of_boundary {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hs : HasSum f 1) {ν : ℝ} {c : ℂ}
    (hb : (fun t : ℝ =>
      (∑' k, (f k : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ^ k) - 1 -
        (if 0 < t then c else starRingEnd ℂ c) * (((|t| : ℝ) ^ ν : ℝ) : ℂ))
        =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν)) :
    Tendsto (fun t : ℝ => (∑' k : ℕ, f k * Real.sin ((k : ℝ) * t)) / t ^ ν)
      (𝓝[>] (0 : ℝ)) (𝓝 c.im) := by
  have hp := (boundary_quotients_of_isLittleO
    (ψ := fun z : ℂ => ∑' k : ℕ, (f k : ℂ) * z ^ k) hb).1
  have ht := Complex.continuous_im.continuousAt.tendsto.comp hp
  apply ht.congr'
  apply Filter.Eventually.of_forall
  intro t
  change (((∑' k : ℕ, (f k : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ^ k) - 1) /
    ((t ^ ν : ℝ) : ℂ)).im = _
  rw [Complex.div_ofReal_im, Complex.sub_im, Complex.one_im, sub_zero,
    im_pgf_exp_eq_sine_tsum hf hs.summable]

/-- Conditional coefficient identification from an actual natural-tail limit.
The boundary normalization and oscillatory integral limits are both derived. -/
theorem im_eq_gamma_sin_of_boundary_and_tail {f : ℕ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hs : HasSum f 1)
    {ν : ℝ} (hν₀ : 0 < ν) (hν₁ : ν < 1) {c : ℂ} {C : ℝ}
    (hTail : Tendsto (fun N : ℕ => (∑' j : ℕ, f (j + N)) /
      (N : ℝ) ^ (-ν)) atTop (𝓝 C))
    (hb : (fun t : ℝ =>
      (∑' k, (f k : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ^ k) - 1 -
        (if 0 < t then c else starRingEnd ℂ c) * (((|t| : ℝ) ^ ν : ℝ) : ℂ))
        =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν)) :
    c.im = C * (Real.Gamma (1 - ν) * Real.sin (Real.pi * ν / 2)) := by
  have hF := fun (t : ℝ) (ht : 0 < t) => tendsto_integral_tail_cos f hs.summable hf ht
  have hab := tendsto_scaled_improper_staircase_cos
    (fun N : ℕ => ∑' j : ℕ, f (j + N))
    (fun t : ℝ => ∑' k : ℕ, f k * Real.sin ((k : ℝ) * t))
    (real_tail_antitone f hs.summable hf) (real_tail_nonneg f hf)
    hν₀ hν₁ hTail hF
  have hb' := tendsto_sine_div_rpow_of_boundary hf hs hb
  have hab' : Tendsto
      (fun t : ℝ => (∑' k : ℕ, f k * Real.sin ((k : ℝ) * t)) / t ^ ν)
      (𝓝[>] (0 : ℝ))
      (𝓝 (C * (Real.Gamma (1 - ν) * Real.sin (Real.pi * ν / 2)))) := by
    apply hab.congr'
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    rw [Real.rpow_neg (show 0 ≤ t from ht.le), div_eq_mul_inv, mul_comm]
  exact tendsto_nhds_unique hb' hab'

/-- The actual A.2 boundary expansion forces a strictly positive imaginary
coefficient. Its tail power limit and positive leading constant are conclusions
of the checked Tauberian argument, rather than extra hypotheses. -/
theorem im_pos_of_boundary_pgf_expansion {f : ℕ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hs : HasSum f 1)
    {ν : ℝ} (hν₀ : 0 < ν) (hν₁ : ν < 1) {c : ℂ} (hc : c.re ≠ 0)
    (hb : (fun t : ℝ =>
      (∑' k, (f k : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ^ k) - 1 -
        (if 0 < t then c else starRingEnd ℂ c) * (((|t| : ℝ) ^ ν : ℝ) : ℂ))
        =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν)) :
    0 < c.im := by
  have hTail := tendsto_tail_power_of_boundary_expansion hf hs hν₀ hν₁ hc hb
  have hident := im_eq_gamma_sin_of_boundary_and_tail hf hs hν₀ hν₁ hTail hb
  rw [hident]
  have hΓ := Real.Gamma_pos_of_pos (sub_pos.mpr hν₁)
  have hη := (tail_laplace_of_boundary_expansion hf hs hν₀ hν₁ hc hb).1
  have hC : 0 < -(c.re / Real.Gamma (1 - ν)) / Real.cos (Real.pi * ν / 2) := by
    have hp := div_pos hη hΓ
    convert hp using 1
    ring
  exact mul_pos hC (gamma_sin_coefficient_pos hν₀ hν₁)

end DirectedDistances.Tauberian
