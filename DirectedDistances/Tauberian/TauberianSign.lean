/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.ProbabilityGeneratingFunction
public import DirectedDistances.Tauberian.PoissonBoundary

/-! # The sign clause of Appendix A.2

Revised manuscript `lem-tauberian`,
under the two-sided boundary expansion `eqn-tauberian` of the literal
probability generating series, the coefficient satisfies `re c < 0`.

The proof derives disk continuity and holomorphy from the generating series
itself, applies the radial asymptotic of Lemma A.1, and compares it with the
bound `‖φ(1 - r)‖ ≤ 1`. This module does not prove the tail asymptotic
`eqn-prob-asymp` of A.2. -/

public section

namespace DirectedDistances.Tauberian

open Filter Metric
open scoped Topology

/-- A probability generating series has norm at most one on the closed unit
disk. -/
theorem norm_weighted_pgf_le_one {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hs : HasSum f 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖∑' k, (f k : ℂ) * z ^ k‖ ≤ 1 :=
  tsum_of_norm_bounded hs (norm_weighted_pow_le hf hz)

/-- Revised Appendix A, Lemma A.2 (`lem-tauberian`), sign clause: if the
probability generating series satisfies the two-sided boundary expansion
`eqn-tauberian` with `re c ≠ 0` and `0 < ν < 1`, then `re c < 0`. -/
theorem re_neg_of_boundary_pgf_expansion {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hs : HasSum f 1) {ν : ℝ} (hν₀ : 0 < ν) (hν₁ : ν < 1) {c : ℂ}
    (hc : c.re ≠ 0)
    (hb : (fun t : ℝ =>
      (∑' k, (f k : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ^ k) - 1 -
        (if 0 < t then c else starRingEnd ℂ c) * (((|t| : ℝ) ^ ν : ℝ) : ℂ))
        =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν)) :
    c.re < 0 := by
  obtain ⟨-, hrad⟩ := radial_asymptotic_of_boundary
    (ψ := fun z : ℂ => ∑' k, (f k : ℂ) * z ^ k)
    (continuousOn_tsum_weighted_pow hf hs.summable)
    (differentiableOn_tsum_weighted_pow hf hs.summable) hν₀ hν₁ hc hb
  have hrad' : (fun r : ℝ => (∑' k, (f k : ℂ) * (((1 - r : ℝ) : ℂ)) ^ k) - 1 -
      ((c.re / Real.cos (Real.pi * ν / 2) : ℝ) : ℂ) * (((r ^ ν : ℝ)) : ℂ))
        =o[𝓝[>] (0 : ℝ)] (fun r : ℝ => r ^ ν) := hrad
  generalize hbdef : c.re / Real.cos (Real.pi * ν / 2) = b at hrad'
  by_contra hneg
  have hcpos : 0 < c.re := lt_of_le_of_ne (not_lt.mp hneg) (Ne.symm hc)
  have hcos : 0 < Real.cos (Real.pi * ν / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have hh := mul_pos Real.pi_pos hν₀
      linarith only [hh, Real.pi_pos]
    · have hh := mul_lt_mul_of_pos_left hν₁ Real.pi_pos
      linarith only [hh]
  have hbpos : 0 < b := by
    rw [← hbdef]
    exact div_pos hcpos hcos
  have hr1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < 1 :=
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  have hr0 : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Set.Ioi (0 : ℝ) :=
    eventually_mem_nhdsWithin
  obtain ⟨r, hrb, hr1', hr0'⟩ :=
    ((hrad'.bound (half_pos hbpos)).and (hr1.and hr0)).exists
  have hrpos : 0 < r := hr0'
  have hpow : 0 < r ^ ν := Real.rpow_pos_of_pos hrpos ν
  have key : ‖(∑' k, (f k : ℂ) * (((1 - r : ℝ) : ℂ)) ^ k) - 1 -
      (b : ℂ) * (((r ^ ν : ℝ)) : ℂ)‖ ≤ b / 2 * ‖r ^ ν‖ := hrb
  rw [Real.norm_of_nonneg hpow.le] at key
  have hz : ‖(((1 - r : ℝ) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (show (0 : ℝ) ≤ 1 - r by linarith)]
    linarith
  have hS := norm_weighted_pgf_le_one hf hs hz
  have hSre := Complex.re_le_norm (∑' k, (f k : ℂ) * (((1 - r : ℝ) : ℂ)) ^ k)
  have hre := Complex.re_le_norm
    (-((∑' k, (f k : ℂ) * (((1 - r : ℝ) : ℂ)) ^ k) - 1 -
      (b : ℂ) * (((r ^ ν : ℝ)) : ℂ)))
  rw [norm_neg] at hre
  simp only [Complex.neg_re, Complex.sub_re, Complex.one_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero] at hre
  have hprod := mul_pos hbpos hpow
  linarith

end DirectedDistances.Tauberian
