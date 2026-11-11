/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.TailGeneratingFunction
import Mathlib.Analysis.SpecialFunctions.Exp







public section
namespace DirectedDistances.Tauberian

open Filter Asymptotics
open scoped Topology

/-- The exponential linearization has a genuine quadratic bound along the
entire two-sided angular approach to zero. -/
theorem exp_angle_linear_error_isBigO_sq :
    (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I)
      =O[𝓝[≠] (0 : ℝ)] (fun t : ℝ => |t| ^ 2) := by
  apply IsBigO.of_bound 1
  have hsmall : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), |t| ≤ 1 :=
    ((continuous_abs.continuousAt (x := (0 : ℝ))).eventually_le_const (by norm_num)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hsmall] with t ht
  have h := Complex.norm_exp_sub_one_sub_id_le (x := (t : ℂ) * Complex.I)
    (by simpa only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs] using ht)
  simpa only [one_mul, Real.norm_eq_abs, abs_pow, abs_abs, norm_mul,
    Complex.norm_real, Complex.norm_I, mul_one] using h

/-- A quadratic error is negligible compared with order `1+ν` whenever ν<1. -/
theorem abs_sq_isLittleO_abs_rpow_one_add {ν : ℝ} (hν : ν < 1) :
    (fun t : ℝ => |t| ^ 2) =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => |t| ^ (1 + ν)) := by
  have hp : 0 < 1 - ν := sub_pos.mpr hν
  have ht : Tendsto (fun t : ℝ => |t| ^ (1 - ν)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 (1 - ν) (Or.inr hp.le)).tendsto.comp
      (show Tendsto (fun t : ℝ => |t|) (𝓝[≠] (0 : ℝ)) (𝓝 0) from
        by simpa only [abs_zero] using
          (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds)
    simpa only [abs_zero, Function.comp_def, Real.zero_rpow hp.ne'] using h
  apply isLittleO_of_tendsto'
    (eventually_mem_nhdsWithin.mono (fun t ht hz => by
      have ht0 : t ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
      exact False.elim ((Real.rpow_pos_of_pos (abs_pos.mpr ht0) _).ne' hz)))
  apply ht.congr'
  filter_upwards [eventually_mem_nhdsWithin] with t ht0
  have htne : t ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht0
  rw [show 1 - ν = (2 : ℝ) - (1 + ν) by ring,
    Real.rpow_sub (abs_pos.mpr htne), Real.rpow_two]

/-- The exponential normalization error is below the manuscript's
higher-order boundary scale, with no angular sign restriction. -/
theorem exp_angle_linear_error_isLittleO {ν : ℝ} (hν : ν < 1) :
    (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I)
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => |t| ^ (1 + ν)) :=
  exp_angle_linear_error_isBigO_sq.trans_isLittleO (abs_sq_isLittleO_abs_rpow_one_add hν)

/-- Dividing the signed higher-order coefficient by the linear imaginary
term gives the conjugate normalized coefficient on negative angles. -/
theorem signed_boundary_coefficient_normalization {c₁ ν t : ℝ} {c₂ : ℂ}
    (hc₁ : c₁ ≠ 0) (ht : t ≠ 0) :
    ((c₁ : ℂ) * Complex.I) * (t : ℂ) *
      ((if 0 < t then c₂ / ((c₁ : ℂ) * Complex.I)
        else starRingEnd ℂ (c₂ / ((c₁ : ℂ) * Complex.I))) *
          ((|t| ^ ν : ℝ) : ℂ)) =
      (if 0 < t then c₂ else starRingEnd ℂ c₂) * ((|t| ^ (1 + ν) : ℝ) : ℂ) := by
  have hc : ((c₁ : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hc₁) Complex.I_ne_zero
  rw [Real.rpow_add (abs_pos.mpr ht), Real.rpow_one, Complex.ofReal_mul]
  by_cases htp : 0 < t
  · rw [ite_eq_left htp, ite_eq_left htp, abs_of_pos htp]
    field_simp [Complex.ofReal_ne_zero.mpr hc₁]
  · rw [ite_eq_right htp, ite_eq_right htp, abs_of_neg (lt_of_le_of_ne (le_of_not_gt htp) ht)]
    simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
    field_simp [Complex.ofReal_ne_zero.mpr hc₁]

/-- The angular exponential difference has a uniform linear lower bound
near zero. In particular it never vanishes on the punctured small interval. -/
theorem abs_half_le_norm_exp_angle_sub_one {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |t| / 2 ≤ ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ := by
  have hq := Complex.norm_exp_sub_one_sub_id_le (x := (t : ℂ) * Complex.I)
    (by simpa only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs] using (ht.trans (by norm_num : (1 : ℝ) / 2 ≤ 1)))
  have htri : ‖(t : ℂ) * Complex.I‖ ≤ ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ +
      ‖Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I‖ := by
    convert norm_sub_le (Complex.exp ((t : ℂ) * Complex.I) - 1)
      (Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I) using 1
    congr 1
    ring
  simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs] at hq htri
  nlinarith only [hq, htri, ht, abs_nonneg t]

/-- The reciprocal angular denominator has at most inverse-linear growth. -/
theorem inv_normalized_exp_angle_isBigO {c₁ : ℝ} (hc₁ : 0 < c₁) :
    (fun t : ℝ => ((c₁ : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) - 1))⁻¹)
      =O[𝓝[≠] (0 : ℝ)] (fun t : ℝ => |t|⁻¹) := by
  apply IsBigO.of_bound (2 / c₁)
  have hsmall : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), |t| ≤ 1 / 2 :=
    ((continuous_abs.continuousAt (x := (0 : ℝ))).eventually_le_const (by norm_num)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hsmall, eventually_mem_nhdsWithin] with t ht ht0
  have htne : t ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht0
  have hap : 0 < |t| := abs_pos.mpr htne
  have hl := abs_half_le_norm_exp_angle_sub_one ht
  calc
    _ = c₁⁻¹ * ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖⁻¹ := by
      rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc₁, mul_inv]
    _ ≤ c₁⁻¹ * (|t| / 2)⁻¹ :=
      mul_le_mul_of_nonneg_left (inv_anti₀ (half_pos hap) hl) (inv_nonneg.mpr hc₁.le)
    _ = (2 / c₁) * ‖|t|⁻¹‖ := by
      rw [Real.norm_eq_abs, abs_inv, abs_abs]
      field_simp

/-- The original higher-order expansion gives the lower-order expansion of
the literal divided boundary function. This helper performs the full error
calculation and preserves the negative-angle conjugate coefficient. -/
theorem normalized_boundary_quotient_expansion {F : ℝ → ℂ}
    {c₁ ν : ℝ} (hc₁ : 0 < c₁) (hν₀ : 0 < ν) (hν₁ : ν < 1) {c₂ : ℂ}
    (hb : (fun t : ℝ => F t - 1 - ((c₁ : ℂ) * Complex.I) * (t : ℂ) -
      (if 0 < t then c₂ else starRingEnd ℂ c₂) * ((|t| ^ (1 + ν) : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => |t| ^ (1 + ν))) :
    (fun t : ℝ => (F t - 1) / ((c₁ : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) - 1)) - 1 -
      (if 0 < t then c₂ / ((c₁ : ℂ) * Complex.I)
        else starRingEnd ℂ (c₂ / ((c₁ : ℂ) * Complex.I))) * ((|t| ^ ν : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => |t| ^ ν) := by
  let B (t : ℝ) := (if 0 < t then c₂ / ((c₁ : ℂ) * Complex.I)
    else starRingEnd ℂ (c₂ / ((c₁ : ℂ) * Complex.I))) * ((|t| ^ ν : ℝ) : ℂ)
  have hB : B =O[𝓝[≠] (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) := by
    apply IsBigO.of_bound ‖c₂ / ((c₁ : ℂ) * Complex.I)‖
    have hsmall : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), |t| ≤ 1 :=
      ((continuous_abs.continuousAt (x := (0 : ℝ))).eventually_le_const (by norm_num)).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hsmall] with t ht
    change ‖(if 0 < t then _ else _) * _‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) ν), norm_one, mul_one]
    have hp : |t| ^ ν ≤ 1 := Real.rpow_le_one (abs_nonneg t) ht hν₀.le
    split
    · exact mul_le_of_le_one_right (norm_nonneg _) hp
    · rw [Complex.norm_conj]
      exact mul_le_of_le_one_right (norm_nonneg _) hp
  have he := (exp_angle_linear_error_isLittleO hν₁).const_mul_left (c₁ : ℂ)
  have heB := he.mul_isBigO hB
  simp only [mul_one] at heB
  have hraw := (hb.sub he).sub heB
  have hnum : (fun t : ℝ => F t - 1 -
      (c₁ : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) - 1) * (1 + B t))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => |t| ^ (1 + ν)) := by
    apply hraw.congr' _ Filter.EventuallyEq.rfl
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    have htne : t ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
    have ha := signed_boundary_coefficient_normalization (c₂ := c₂) (ν := ν) hc₁.ne' htne
    change ((c₁ : ℂ) * Complex.I) * (t : ℂ) * B t = _ at ha
    rw [← ha]
    ring
  have hres := hnum.mul_isBigO (inv_normalized_exp_angle_isBigO hc₁)
  apply hres.congr'
  · have hsmall : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), |t| ≤ 1 / 2 :=
      ((continuous_abs.continuousAt (x := (0 : ℝ))).eventually_le_const (by norm_num)).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hsmall, eventually_mem_nhdsWithin] with t ht ht0
    have htne : t ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht0
    have hE : Complex.exp ((t : ℂ) * Complex.I) - 1 ≠ 0 :=
      norm_pos_iff.mp ((half_pos (abs_pos.mpr htne)).trans_le
        (abs_half_le_norm_exp_angle_sub_one ht))
    have hd := mul_ne_zero (Complex.ofReal_ne_zero.mpr hc₁.ne') hE
    change (F t - 1 - (c₁ : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) - 1) * (1 + B t)) *
      ((c₁ : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) - 1))⁻¹ =
      (F t - 1) / ((c₁ : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) - 1)) - 1 - B t
    field_simp [Complex.ofReal_ne_zero.mpr hc₁.ne', hE]
    ring
  · filter_upwards [eventually_mem_nhdsWithin] with t ht0
    have htne : t ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht0
    rw [Real.rpow_add (abs_pos.mpr htne), Real.rpow_one]
    field_simp

/-- The genuine probability generating series of the actual normalized tails
has the manuscript's order-ν boundary expansion, once the actual finite mean
has been identified with c₁. The first-moment production is a separate theorem. -/
theorem normalized_tail_boundary_expansion {f : ℕ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hs : HasSum f 1)
    (hm : Summable (fun k : ℕ => (k : ℝ) * f k))
    {c₁ ν : ℝ} (hc₁ : 0 < c₁) (hmean : (∑' k : ℕ, (k : ℝ) * f k) = c₁)
    (hν₀ : 0 < ν) (hν₁ : ν < 1) {c₂ : ℂ}
    (hb : (fun t : ℝ =>
      (∑' k : ℕ, (f k : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ^ k) - 1 -
      ((c₁ : ℂ) * Complex.I) * (t : ℂ) -
      (if 0 < t then c₂ else starRingEnd ℂ c₂) * ((|t| ^ (1 + ν) : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => |t| ^ (1 + ν))) :
    (fun t : ℝ =>
      (∑' k : ℕ, (((∑' j : ℕ, f (j + (k + 1))) /
        (∑' n : ℕ, (n : ℝ) * f n) : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ^ k) - 1 -
      (if 0 < t then c₂ / ((c₁ : ℂ) * Complex.I)
        else starRingEnd ℂ (c₂ / ((c₁ : ℂ) * Complex.I))) * ((|t| ^ ν : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => |t| ^ ν) := by
  have hq := normalized_boundary_quotient_expansion hc₁ hν₀ hν₁ hb
  apply hq.congr' _ Filter.EventuallyEq.rfl
  have hsmall : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), |t| ≤ 1 / 2 :=
    ((continuous_abs.continuousAt (x := (0 : ℝ))).eventually_le_const (by norm_num)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hsmall, eventually_mem_nhdsWithin] with t ht ht0
  have htne : t ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht0
  have hE : Complex.exp ((t : ℂ) * Complex.I) ≠ 1 := sub_ne_zero.mp
    (norm_pos_iff.mp ((half_pos (abs_pos.mpr htne)).trans_le
      (abs_half_le_norm_exp_angle_sub_one ht)))
  have hg := tsum_normalized_tail_weighted_pow_eq_quotient hf hs hm
    (by rw [hmean]; exact hc₁) (le_of_eq (Complex.norm_exp_ofReal_mul_I t)) hE
  rw [hmean] at hg
  rw [hmean, hg]

/-- The real part of the normalized coefficient is the original imaginary
part divided by the same positive mean. -/
theorem normalized_boundary_coefficient_re {c₁ : ℝ} (hc₁ : c₁ ≠ 0) (c₂ : ℂ) :
    (c₂ / ((c₁ : ℂ) * Complex.I)).re = c₂.im / c₁ := by
  rw [Complex.div_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, zero_add,
    Complex.normSq_apply]
  field_simp [hc₁]
  ring

/-- Nonreal c₂ gives a normalized coefficient outside the imaginary axis,
as required to apply the manuscript's holomorphic boundary lemma to G. -/
theorem normalized_boundary_coefficient_re_ne_zero {c₁ : ℝ} (hc₁ : c₁ ≠ 0)
    {c₂ : ℂ} (hc₂ : c₂.im ≠ 0) :
    (c₂ / ((c₁ : ℂ) * Complex.I)).re ≠ 0 := by
  rw [normalized_boundary_coefficient_re hc₁]
  exact div_ne_zero hc₂ hc₁

end DirectedDistances.Tauberian
