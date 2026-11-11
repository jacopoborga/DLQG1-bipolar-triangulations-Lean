/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Tauberian.NonnegativeFirstMoment
public import DirectedDistances.Tauberian.PGFFirstMoment
import Mathlib.Analysis.Calculus.Deriv.Slope







public section
namespace DirectedDistances.Tauberian
open Filter Asymptotics
open scoped Topology

/-- An absolute power of order strictly greater than one is little-o of the
signed real argument along the two-sided punctured neighborhood of zero. -/
theorem abs_rpow_one_add_isLittleO_id {ν : ℝ} (hν : 0 < ν) :
    (fun t : ℝ => |t| ^ (1 + ν)) =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => t) := by
  have hp : Tendsto (fun t : ℝ => |t| ^ ν) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have habs : Tendsto (fun t : ℝ => |t|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      simpa only [abs_zero] using
        (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have h := (Real.continuousAt_rpow_const 0 ν (Or.inr hν.le)).tendsto.comp habs
    simpa only [Function.comp_def, Real.zero_rpow hν.ne'] using h
  apply (isLittleO_iff_tendsto (fun t ht => by
    rw [ht, abs_zero, Real.zero_rpow (by linarith only [hν])])).2
  apply tendsto_zero_iff_norm_tendsto_zero.2
  apply hp.congr'
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
  rw [norm_div, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _),
    Real.norm_eq_abs, Real.rpow_add (abs_pos.mpr ht0), Real.rpow_one]
  exact (mul_div_cancel_left₀ _ (abs_ne_zero.mpr ht0)).symm

/-- The full two-sided source expansion, including its conjugate coefficient
on negative arguments, produces the derivative at zero. -/
theorem hasDerivAt_of_higher_order_boundary {F : ℝ → ℂ} (hF0 : F 0 = 1)
    {c₁ ν : ℝ} (hν : 0 < ν) {c₂ : ℂ}
    (hb : (fun t : ℝ => F t - 1 - ((c₁ : ℂ) * Complex.I) * (t : ℂ) -
      (if 0 < t then c₂ else starRingEnd ℂ c₂) * ((|t| ^ (1 + ν) : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => |t| ^ (1 + ν))) :
    HasDerivAt F ((c₁ : ℂ) * Complex.I) 0 := by
  have hc : (fun t : ℝ =>
      (if 0 < t then c₂ else starRingEnd ℂ c₂) * ((|t| ^ (1 + ν) : ℝ) : ℂ))
      =O[𝓝[≠] (0 : ℝ)] (fun t : ℝ => |t| ^ (1 + ν)) := by
    apply IsBigO.of_bound ‖c₂‖
    apply Filter.Eventually.of_forall
    intro t
    rw [norm_mul, Complex.norm_real]
    split
    · exact le_refl _
    · rw [Complex.norm_conj]
  have hr := (hb.isBigO.add hc).trans_isLittleO (abs_rpow_one_add_isLittleO_id hν)
  have hr' : (fun t : ℝ => F t - 1 - ((c₁ : ℂ) * Complex.I) * (t : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => t) := by
    convert hr using 1
    funext t
    ring
  rw [hasDerivAt_iff_tendsto_slope]
  have ht := hr'.tendsto_inv_smul_nhds_zero.add_const ((c₁ : ℂ) * Complex.I)
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_mem_nhdsWithin] with t ht0
  have htne : t ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht0
  rw [slope_def_module, hF0, sub_zero, Complex.real_smul, Complex.real_smul,
    Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr htne]
  ring

/-- The genuine probability generating series at `exp(it)` has the source
linear derivative, produced by the higher-order boundary expansion alone. -/
theorem hasDerivAt_characteristic_of_higher_order_boundary {f : ℕ → ℝ}
    (hs : HasSum f 1) {c₁ ν : ℝ} (hν : 0 < ν) {c₂ : ℂ}
    (hb : (fun t : ℝ =>
      (∑' k : ℕ, (f k : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ^ k) - 1 -
      ((c₁ : ℂ) * Complex.I) * (t : ℂ) -
      (if 0 < t then c₂ else starRingEnd ℂ c₂) * ((|t| ^ (1 + ν) : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => |t| ^ (1 + ν))) :
    HasDerivAt (fun t : ℝ =>
      ∑' k : ℕ, (f k : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ^ k)
      ((c₁ : ℂ) * Complex.I) 0 := by
  apply hasDerivAt_of_higher_order_boundary _ hν hb
  simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_pow, mul_one,
    Complex.ofReal_one] using (Complex.hasSum_ofReal.mpr hs).tsum_eq

/-- Revised A.3's boundary expansion produces a summable actual first moment
and identifies its sum with `c₁`. No moment or derivative premise is used. -/
theorem first_moment_of_higher_order_boundary {f : ℕ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hs : HasSum f 1)
    {c₁ ν : ℝ} (hν : 0 < ν) {c₂ : ℂ}
    (hb : (fun t : ℝ =>
      (∑' k : ℕ, (f k : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ^ k) - 1 -
      ((c₁ : ℂ) * Complex.I) * (t : ℂ) -
      (if 0 < t then c₂ else starRingEnd ℂ c₂) * ((|t| ^ (1 + ν) : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => |t| ^ (1 + ν))) :
    Summable (fun k : ℕ => (k : ℝ) * f k) ∧
      (∑' k : ℕ, (k : ℝ) * f k) = c₁ := by
  have hd := hasDerivAt_characteristic_of_higher_order_boundary hs hν hb
  apply first_moment_of_characteristic_derivative f hf hs
  convert hd using 1
  funext t
  apply tsum_congr
  intro k
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

end DirectedDistances.Tauberian
