/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import DirectedDistances.Tauberian.RecursionDiscriminant
import Mathlib.Tactic.Linarith

/-! Supporting lemmas for paper labels `lem:nonreal2` (see CORRESPONDENCE.md). -/










public section
namespace DirectedDistances.PaperProofs.Section6
open Filter
open scoped Topology

/-- Every normalized nonnegative integer mass function with f(0)<1 has a
positive-mass nonzero atom. -/
theorem exists_nonzero_pos_mass {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hs : HasSum f 1) (hzero : f 0 < 1) :
    ∃ k : ℤ, k ≠ 0 ∧ 0 < f k := by
  by_contra h
  have hvanish : ∀ k : ℤ, k ≠ 0 → f k = 0 := by
    intro k hk
    exact le_antisymm (le_of_not_gt (fun hp => h ⟨k, hk, hp⟩)) (hf k)
  have hsingle : HasSum f (f 0) := hasSum_single 0 hvanish
  have heq : (1 : ℝ) = f 0 := hs.unique hsingle
  exact (ne_of_lt hzero) heq.symm

/-- Absolute summability of the actual cosine series follows from the mass
normalization and the pointwise bound |cos|≤1. -/
theorem summable_integer_cosine_mass {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hs : Summable f) (t : ℝ) :
    Summable (fun k : ℤ => f k * Real.cos (t * (k : ℝ))) := by
  apply hs.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf k)]
  exact mul_le_of_le_one_right (hf k) (Real.abs_cos_le_one _)

/-- The actual characteristic cosine series is continuous by its summable
uniform mass bound. -/
theorem continuous_integer_cosine_mass {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hs : Summable f) :
    Continuous (fun t : ℝ => ∑' k : ℤ, f k * Real.cos (t * (k : ℝ))) := by
  apply continuous_tsum
    (fun k => continuous_const.mul
      (Real.continuous_cos.comp (continuous_id.mul continuous_const))) hs
  intro k t
  change ‖f k * Real.cos (t * (k : ℝ))‖ ≤ f k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf k)]
  exact mul_le_of_le_one_right (hf k) (Real.abs_cos_le_one _)

/-- A single positive-mass nonzero atom forces the actual cosine series
strictly below one on a whole positive interval. -/
theorem exists_integer_cosine_mass_lt_one {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hs : HasSum f 1) (hzero : f 0 < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      (∑' k : ℤ, f k * Real.cos (t * (k : ℝ))) < 1 := by
  obtain ⟨k, hk, hfk⟩ := exists_nonzero_pos_mass hf hs hzero
  have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hkabs : 0 < |(k : ℝ)| := abs_pos.mpr hkreal
  refine ⟨Real.pi / |(k : ℝ)|, div_pos Real.pi_pos hkabs, ?_⟩
  intro t ht htd
  have habs : |t * (k : ℝ)| < Real.pi := by
    rw [abs_mul, abs_of_pos ht]
    exact (lt_div_iff₀ hkabs).mp htd
  have hx : 0 < |t * (k : ℝ)| := abs_pos.mpr (mul_ne_zero ht.ne' hkreal)
  have hcos : Real.cos (t * (k : ℝ)) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) habs.le hx
    simpa only [Real.cos_abs, Real.cos_zero] using h
  have hlt := Summable.tsum_lt_tsum
    (fun j : ℤ => show f j * Real.cos (t * (j : ℝ)) ≤ f j from
      mul_le_of_le_one_right (hf j) (Real.cos_le_one _))
    (mul_lt_of_lt_one_right hfk hcos)
    (summable_integer_cosine_mass hf hs.summable t) hs.summable
  exact hs.tsum_eq ▸ hlt

/-- The genuine series has both bounds required by the negative-discriminant
argument: 1/4<F(t)<1 for every sufficiently small positive t. -/
theorem exists_integer_cosine_mass_interval {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hs : HasSum f 1) (hzero : f 0 < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      (1 / 4 : ℝ) < (∑' k : ℤ, f k * Real.cos (t * (k : ℝ))) ∧
      (∑' k : ℤ, f k * Real.cos (t * (k : ℝ))) < 1 := by
  obtain ⟨δ₁, hδ₁, hgap⟩ := exists_integer_cosine_mass_lt_one hf hs hzero
  have hvalue : (∑' k : ℤ, f k * Real.cos ((0 : ℝ) * (k : ℝ))) = 1 := by
    simpa only [zero_mul, Real.cos_zero, mul_one] using hs.tsum_eq
  have hlim := (continuous_integer_cosine_mass hf hs.summable).continuousAt (x := 0) |>.tendsto
  have hev : ∀ᶠ t : ℝ in 𝓝 0,
      (1 / 4 : ℝ) < (∑' k : ℤ, f k * Real.cos (t * (k : ℝ))) := by
    apply hlim.eventually
    apply eventually_gt_nhds
    rw [hvalue]
    norm_num
  obtain ⟨δ₂, hδ₂, hlow⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro t ht htd
  refine ⟨hlow ?_, hgap t ht (lt_of_lt_of_le htd (min_le_left _ _))⟩
  simpa only [Real.dist_eq, sub_zero, abs_of_pos ht] using
    (lt_of_lt_of_le htd (min_le_right _ _))

/-- Absolute summability of the genuine complex integer characteristic
series, without a moment assumption. -/
theorem summable_integer_characteristic_mass {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hs : Summable f) (t : ℝ) :
    Summable (fun k : ℤ => (f k : ℂ) *
      Complex.exp (((t * (k : ℝ) : ℝ) : ℂ) * Complex.I)) := by
  apply hs.of_norm_bounded
  intro k
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf k),
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The real part is the actual cosine series; summability is proved before
commuting real part and infinite sum. -/
theorem re_integer_characteristic_mass {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hs : Summable f) (t : ℝ) :
    (∑' k : ℤ, (f k : ℂ) *
      Complex.exp (((t * (k : ℝ) : ℝ) : ℂ) * Complex.I)).re =
      ∑' k : ℤ, f k * Real.cos (t * (k : ℝ)) := by
  rw [Complex.re_tsum (summable_integer_characteristic_mass hf hs t)]
  apply tsum_congr
  intro k
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.exp_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, add_zero, Real.exp_zero, one_mul]

/-- Symmetry of the actual mass function forces the actual characteristic
series to be real. -/
theorem im_integer_characteristic_mass_eq_zero {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hs : Summable f) (hsymm : ∀ k : ℤ, f (-k) = f k) (t : ℝ) :
    (∑' k : ℤ, (f k : ℂ) *
      Complex.exp (((t * (k : ℝ) : ℝ) : ℂ) * Complex.I)).im = 0 := by
  rw [Complex.im_tsum (summable_integer_characteristic_mass hf hs t)]
  have heq : (∑' k : ℤ, f k * Real.sin (t * (k : ℝ))) =
      -(∑' k : ℤ, f k * Real.sin (t * (k : ℝ))) := by
    calc
      _ = ∑' k : ℤ, f (-k) * Real.sin (t * ((-k : ℤ) : ℝ)) :=
        ((Equiv.neg ℤ).tsum_eq _).symm
      _ = ∑' k : ℤ, -(f k * Real.sin (t * (k : ℝ))) := by
        apply tsum_congr
        intro k
        simp only [hsymm, Int.cast_neg, mul_neg, Real.sin_neg]
      _ = _ := tsum_neg
  have hzero : (∑' k : ℤ, f k * Real.sin (t * (k : ℝ))) = 0 := by
    linarith only [heq]
  convert hzero using 1
  apply tsum_congr
  intro k
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, Complex.exp_im, Complex.mul_re, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, Real.exp_zero, one_mul]

/-- Analytic closure of the discriminant argument for a genuine symmetric
integer mass function. The characteristic series is real and its discriminant
is negative on one positive interval; every actual root of the corresponding
complex quadratic therefore has nonzero imaginary part. The quadratic is used
only inside the universal statement about its roots, not assumed for the mass
function itself. This is the analytic core of Lemma 6.7, not its source-law
identification or the missing recursive equation. -/
theorem exists_integer_characteristic_discriminant_neg {f : ℤ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hs : HasSum f 1) (hsymm : ∀ k : ℤ, f (-k) = f k)
    (hzero : f 0 < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      let F : ℂ := ∑' k : ℤ, (f k : ℂ) *
        Complex.exp (((t * (k : ℝ) : ℝ) : ℂ) * Complex.I)
      F.im = 0 ∧ (3 * F.re - 1) ^ 2 - 4 * F.re ^ 3 < 0 ∧
      ∀ z : ℂ, F ^ 2 * z ^ 2 + (3 * F - 1) * z + F = 0 → z.im ≠ 0 := by
  obtain ⟨δ, hδ, hinterval⟩ := exists_integer_cosine_mass_interval hf hs hzero
  refine ⟨δ, hδ, ?_⟩
  intro t ht htd
  dsimp only
  let F : ℂ := ∑' k : ℤ, (f k : ℂ) *
    Complex.exp (((t * (k : ℝ) : ℝ) : ℂ) * Complex.I)
  obtain ⟨hlow, hhigh⟩ := hinterval t ht htd
  have hre : F.re = ∑' k : ℤ, f k * Real.cos (t * (k : ℝ)) :=
    re_integer_characteristic_mass hf hs.summable t
  have him : F.im = 0 := im_integer_characteristic_mass_eq_zero hf hs.summable hsymm t
  have hlow' : (1 / 4 : ℝ) < F.re := hre.symm ▸ hlow
  have hone : F.re ≠ 1 := ne_of_lt (hre.symm ▸ hhigh)
  have hcast : (F.re : ℂ) = F := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simpa only [Complex.ofReal_im] using him.symm
  refine ⟨him, DirectedDistances.Tauberian.recursion_discriminant_neg hlow' hone, ?_⟩
  intro z hq
  apply DirectedDistances.Tauberian.im_ne_zero_of_recursion_quadratic hlow' hone
  simpa only [hcast] using hq

end DirectedDistances.PaperProofs.Section6
