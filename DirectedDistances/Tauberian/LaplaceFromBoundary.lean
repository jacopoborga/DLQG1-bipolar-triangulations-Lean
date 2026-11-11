/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.TauberianSign
public import DirectedDistances.Tauberian.TailGeneratingFunction
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Supporting lemmas for paper labels `lem-tauberian` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.Tauberian
open Filter
open scoped Topology

/-- The exponential scale agrees to first order with its disk radius. -/
theorem tendsto_one_sub_exp_neg_div :
    Tendsto (fun s : ℝ => (1 - Real.exp (-s)) / s)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hd : HasDerivAt (fun s : ℝ => 1 - Real.exp (-s)) 1 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).neg.exp).const_sub 1)
  simpa only [zero_add, neg_zero, Real.exp_zero, sub_self, sub_zero,
    smul_eq_mul, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right

/-- A real radial expansion gives the actual normalized PGF defect limit. -/
theorem tendsto_pgf_defect_of_radial {f : ℕ → ℝ} {ν b : ℝ}
    (hrad : (fun r : ℝ =>
      (∑' k, (f k : ℂ) * (((1 - r : ℝ) : ℂ)) ^ k) - 1 -
        (b : ℂ) * (((r ^ ν : ℝ)) : ℂ))
        =o[𝓝[>] (0 : ℝ)] (fun r : ℝ => r ^ ν)) :
    Tendsto (fun r : ℝ => (1 - ∑' k, f k * (1 - r) ^ k) / r ^ ν)
      (𝓝[>] (0 : ℝ)) (𝓝 (-b)) := by
  have hr : (fun r : ℝ => (∑' k, f k * (1 - r) ^ k) - 1 - b * r ^ ν)
      =o[𝓝[>] (0 : ℝ)] (fun r : ℝ => r ^ ν) := by
    apply Complex.isLittleO_ofReal_left.mp
    convert hrad using 1
    ext r
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one,
      Complex.ofReal_tsum, Complex.ofReal_pow]
  have hh := hr.tendsto_div_nhds_zero.neg.sub_const b
  simp only [neg_zero, zero_sub] at hh
  apply hh.congr'
  filter_upwards [eventually_mem_nhdsWithin] with r hr
  have hn : r ^ ν ≠ 0 := (Real.rpow_pos_of_pos hr ν).ne'
  field_simp
  ring

/-- The PGF defect produces the exponential Laplace input for the actual tail
coefficients, including laws with infinite mean. -/
theorem tendsto_tail_laplace_of_pgf_defect {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hs : HasSum f 1) {ν η : ℝ}
    (hlim : Tendsto (fun r : ℝ =>
      (1 - ∑' k, f k * (1 - r) ^ k) / r ^ ν)
      (𝓝[>] (0 : ℝ)) (𝓝 η)) :
    Tendsto (fun s : ℝ => s ^ (1 - ν) *
      (∑' k : ℕ, (∑' j : ℕ, f (j + (k + 1))) * Real.exp (-s * (k : ℝ))))
      (𝓝[>] (0 : ℝ)) (𝓝 η) := by
  have hrmap : Tendsto (fun s : ℝ => 1 - Real.exp (-s))
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have hc : Continuous (fun s : ℝ => 1 - Real.exp (-s)) :=
        continuous_const.sub (Real.continuous_exp.comp continuous_id.neg)
      simpa only [neg_zero, Real.exp_zero, sub_self] using
        (hc.tendsto 0).mono_left (y := 𝓝[>] (0 : ℝ)) nhdsWithin_le_nhds
    · filter_upwards [eventually_mem_nhdsWithin] with s hs
      exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hs))
  have hpow := tendsto_one_sub_exp_neg_div.rpow_const
    (p := ν - 1) (Or.inl one_ne_zero)
  simp only [Real.one_rpow] at hpow
  have hh := (hlim.comp hrmap).mul hpow
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_mem_nhdsWithin] with s hs0
  have he : 0 < Real.exp (-s) := Real.exp_pos _
  have he1 : Real.exp (-s) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hs0)
  have hr : 0 < 1 - Real.exp (-s) := sub_pos.mpr he1
  have hid := one_sub_tsum_weighted_pow_eq_tail hf hs he.le he1
  have hid' : 1 - (∑' n : ℕ, f n * Real.exp (-s) ^ n) =
      (1 - Real.exp (-s)) *
        (∑' k : ℕ, (∑' j : ℕ, f (j + (k + 1))) * Real.exp (-s * (k : ℝ))) := by
    convert hid using 1
    congr 1
    apply tsum_congr
    intro k
    rw [← Real.exp_nat_mul]
    congr 2
    ring
  dsimp only [Function.comp_def]
  rw [sub_sub_cancel, hid', Real.div_rpow hr.le hs0.le,
    Real.rpow_sub hr ν 1, Real.rpow_one, Real.rpow_sub hs0 ν 1,
    Real.rpow_one, Real.rpow_sub hs0 1 ν, Real.rpow_one]
  have hrn := (Real.rpow_pos_of_pos hr ν).ne'
  have hsn := (Real.rpow_pos_of_pos hs0 ν).ne'
  field_simp

/-- The exact boundary hypothesis of A.2 produces a positive normalizer
coefficient and the actual tail Laplace asymptotic used by Karamata. -/
theorem tail_laplace_of_boundary_expansion {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hs : HasSum f 1)
    {ν : ℝ} (hν₀ : 0 < ν) (hν₁ : ν < 1) {c : ℂ} (hc : c.re ≠ 0)
    (hb : (fun t : ℝ =>
      (∑' k, (f k : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ^ k) - 1 -
        (if 0 < t then c else starRingEnd ℂ c) * (((|t| : ℝ) ^ ν : ℝ) : ℂ))
        =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν)) :
    0 < -(c.re / Real.cos (Real.pi * ν / 2)) ∧
      Tendsto (fun s : ℝ => s ^ (1 - ν) *
        (∑' k : ℕ, (∑' j : ℕ, f (j + (k + 1))) * Real.exp (-s * (k : ℝ))))
        (𝓝[>] (0 : ℝ)) (𝓝 (-(c.re / Real.cos (Real.pi * ν / 2)))) := by
  have hsign := re_neg_of_boundary_pgf_expansion hf hs hν₀ hν₁ hc hb
  have hcos : 0 < Real.cos (Real.pi * ν / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have hh := mul_pos Real.pi_pos hν₀
      linarith only [hh, Real.pi_pos]
    · have hh := mul_lt_mul_of_pos_left hν₁ Real.pi_pos
      linarith only [hh]
  refine ⟨neg_pos.mpr (div_neg_of_neg_of_pos hsign hcos), ?_⟩
  obtain ⟨-, hrad⟩ := radial_asymptotic_of_boundary
    (ψ := fun z : ℂ => ∑' k, (f k : ℂ) * z ^ k)
    (continuousOn_tsum_weighted_pow hf hs.summable)
    (differentiableOn_tsum_weighted_pow hf hs.summable) hν₀ hν₁ hc hb
  exact tendsto_tail_laplace_of_pgf_defect hf hs (tendsto_pgf_defect_of_radial hrad)

end DirectedDistances.Tauberian
