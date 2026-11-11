/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Asymptotics.Ring
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import DirectedDistances.Recursive.CharacteristicCubic
import DirectedDistances.Recursive.LDPNondegenerate
import DirectedDistances.PaperProofs.Section6.Next.CharacteristicDiscriminant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring






public section
namespace DirectedDistances.Recursive

open Filter Asymptotics
open scoped Topology

/-- The characteristic series of an integer-valued probability mass function. -/
@[expose] noncomputable def integerCF (p : ℤ → ℝ) (t : ℝ) : ℂ :=
  ∑' k : ℤ, (p k : ℂ) *
    Complex.exp ((((t * (k : ℝ) : ℝ) : ℂ) * Complex.I))

/-- The negative-index part of the transform used in Proposition 6.2 -/
@[expose] noncomputable def negativeCF (p : ℤ → ℝ) (t : ℝ) : ℂ :=
  ∑' k : {k : ℤ // k ≤ -1}, (p k : ℂ) *
    Complex.exp ((((t * (k : ℝ) : ℝ) : ℂ) * Complex.I))

/-- The constant and exponential terms in `eq:real-part-fhat`, Proposition 6.2 -/
@[expose] noncomputable def ldpOffset (f : ℤ → ℝ) (t : ℝ) : ℂ :=
  (f 0 : ℂ) - (((3 + f 0) / 2 : ℝ) : ℂ) *
    Complex.exp ((t : ℂ) * Complex.I)

/-- The source LDP transform `Ĥ⁻` in Proposition 6.2 -/
@[expose] noncomputable def ldpHat (f : ℤ → ℝ) (t : ℝ) : ℂ :=
  negativeCF f t + ldpOffset f t

/-- The real coefficient in `eq:real-part-fhat`, Proposition 6.2 -/
@[expose] noncomputable def ldpK (f : ℤ → ℝ) (t : ℝ) : ℝ :=
  -(f 0) + (3 + f 0) * Real.cos t

/-- The displayed coefficient satisfies `3 - K = (3 + f 0)(1 - cos t)` in -/
theorem ldpK_factorization (f : ℤ → ℝ) (t : ℝ) :
    3 - ldpK f t = (3 + f 0) * (1 - Real.cos t) := by
  simp only [ldpK]
  ring

/-- Real part of the actual characteristic series; Proposition 6.2, -/
theorem integerCF_re {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hs : Summable f) (t : ℝ) :
    (integerCF f t).re = ∑' k : ℤ, f k * Real.cos (t * (k : ℝ)) := by
  simpa only [integerCF] using
    DirectedDistances.PaperProofs.Section6.re_integer_characteristic_mass hf hs t

/-- Symmetry makes the actual characteristic series real; Proposition 6.2, -/
theorem integerCF_im {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hs : Summable f) (hsymm : ∀ k : ℤ, f (-k) = f k) (t : ℝ) :
    (integerCF f t).im = 0 := by
  simpa only [integerCF] using
    DirectedDistances.PaperProofs.Section6.im_integer_characteristic_mass_eq_zero
      hf hs hsymm t

/-- Identify the characteristic series with its real cosine series under the
source symmetry assumption; Proposition 6.2, -/
theorem integerCF_eq_ofReal_cosine {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hs : Summable f) (hsymm : ∀ k : ℤ, f (-k) = f k) (t : ℝ) :
    integerCF f t =
      (∑' k : ℤ, f k * Real.cos (t * (k : ℝ)) : ℝ) := by
  apply Complex.ext
  · exact integerCF_re hf hs t
  · simpa only [Complex.ofReal_im] using integerCF_im hf hs hsymm t

/-- The real characteristic transform is bounded above by one for every -/
theorem integerCF_re_le_one {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hfs : HasSum f 1) (t : ℝ) : (integerCF f t).re ≤ 1 := by
  rw [integerCF_re hf hfs.summable t]
  have hcos := DirectedDistances.PaperProofs.Section6.summable_integer_cosine_mass
    hf hfs.summable t
  have hle := hcos.tsum_le_tsum
    (fun k => mul_le_of_le_one_right (hf k) (Real.cos_le_one _)) hfs.summable
  rw [hfs.tsum_eq] at hle
  exact hle

/-- Continuity of the actual transform at the origin gives its normalized -/
theorem integerCF_tendsto_one {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hfs : HasSum f 1) (hsymm : ∀ k : ℤ, f (-k) = f k) :
    Tendsto (fun t : ℝ => integerCF f t) (𝓝 0) (𝓝 (1 : ℂ)) := by
  let R : ℝ → ℝ := fun t => ∑' k : ℤ, f k * Real.cos (t * (k : ℝ))
  have hcont := DirectedDistances.PaperProofs.Section6.continuous_integer_cosine_mass
    hf hfs.summable
  have hR : Tendsto R (𝓝 0) (𝓝 1) := by
    have h : Tendsto R (𝓝 0) (𝓝 (R 0)) := by
      simpa only [R] using (hcont.continuousAt (x := 0)).tendsto
    have hzero : R 0 = 1 := by
      dsimp [R]
      simpa only [zero_mul, Real.cos_zero, mul_one] using hfs.tsum_eq
    simpa only [hzero] using h
  have hcoe := Complex.continuous_ofReal.continuousAt.tendsto.comp hR
  apply hcoe.congr'
  filter_upwards with t
  change (R t : ℂ) = integerCF f t
  exact (integerCF_eq_ofReal_cosine hf hfs.summable hsymm t).symm

/-- The cosine quotient has its second-order limit at zero, used in -/
theorem one_sub_cos_div_sq_tendsto_half :
    Tendsto (fun t : ℝ => (1 - Real.cos t) / t ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
  have hs := Real.tendsto_sin_div_nhdsNE_zero
  -- The double-angle identity reduces the quotient to the square of `sin u / u`.
  have hsin : Tendsto (fun t : ℝ => Real.sin (t / 2) / (t / 2))
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    apply hs.comp
    refine tendsto_nhdsWithin_iff.mpr ?_
    constructor
    · have hid : Tendsto (fun t : ℝ => t) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using hid.div_const (2 : ℝ)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact div_ne_zero (by simpa using ht) (by norm_num)
  have hsq := hsin.pow 2
  have hquot : (fun t : ℝ => (1 - Real.cos t) / t ^ 2) =
      fun t => (1 / 2 : ℝ) * (Real.sin (t / 2) / (t / 2)) ^ 2 := by
    funext t
    by_cases ht : t = 0
    · simp [ht]
    · have ht2 : t / 2 ≠ 0 := div_ne_zero ht (by norm_num)
      have hid : 1 - Real.cos t = 2 * Real.sin (t / 2) ^ 2 := by
        rw [Real.sin_sq_eq_half_sub]
        have harg : 2 * (t / 2) = t := by ring
        rw [harg]
        ring
      rw [hid]
      field_simp
  simpa [hquot] using hsq.const_mul (1 / 2 : ℝ)

section LDP

variable {f g : ℤ → ℝ}
variable (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
variable (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
variable (hsymm : ∀ x, f (-x) = f x)
variable (hgsupp : ∀ y, 0 ≤ y → g y = 0)
variable (hrec : ∀ x y : ℤ, y ≤ -1 →
  3 * f x * g y =
    f x * f y +
    f x * ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1), g (y + j) * g (-j) +
    (if y = -1 then
      (∑' j : ℕ, f ((j : ℤ) + x + 1) * f (-(j : ℤ))) + g (-x - 1)
     else 0))
variable (hLdpQuad : ∀ t : ℝ,
  (integerCF f t) ^ 2 * (ldpHat f t) ^ 2 +
    (3 * integerCF f t - 1) * ldpHat f t + integerCF f t = 0)
variable (hLdpReal : ∀ t : ℝ,
  (ldpHat f t).re = ((integerCF f t).re - ldpK f t) / 2)

/-- The source quadratic and its real-part identity force the exact cubic
relation for the actual LDP characteristic transform. This uses the master
recursion only through the checked nondegeneracy input. Proposition 6.2, -/
theorem ldp_cubic_relation_of_master
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x)
    (hgsupp : ∀ y, 0 ≤ y → g y = 0)
    (hrec : ∀ x y : ℤ, y ≤ -1 →
      3 * f x * g y =
        f x * f y +
        f x * ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1), g (y + j) * g (-j) +
        (if y = -1 then
          (∑' j : ℕ, f ((j : ℤ) + x + 1) * f (-(j : ℤ))) + g (-x - 1)
         else 0))
    (hLdpQuad : ∀ t : ℝ,
      (integerCF f t) ^ 2 * (ldpHat f t) ^ 2 +
        (3 * integerCF f t - 1) * ldpHat f t + integerCF f t = 0)
    (hLdpReal : ∀ t : ℝ,
      (ldpHat f t).re = ((integerCF f t).re - ldpK f t) / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      (integerCF f t - 1) ^ 3 +
        ((((3 + f 0) * (1 - Real.cos t) : ℝ) : ℂ) *
          (integerCF f t) ^ 2) = 0 := by
  obtain ⟨hf_lt, _⟩ := ldp_pmf_nondegenerate_of_master
    hf hfs hg hgs hsymm hgsupp hrec
  have hf0lt : f 0 < 1 := hf_lt 0
  obtain ⟨δ, hδ, hdisc⟩ :=
    DirectedDistances.PaperProofs.Section6.exists_integer_characteristic_discriminant_neg
      hf hfs hsymm hf0lt
  refine ⟨δ, hδ, ?_⟩
  intro t ht htd
  obtain ⟨_, _, hroot⟩ := hdisc t ht htd
  have hFim : (integerCF f t).im = 0 := integerCF_im hf hfs.summable hsymm t
  have hFcast : ((integerCF f t).re : ℂ) = integerCF f t := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simpa only [Complex.ofReal_im] using hFim.symm
  have hquad :
      (integerCF f t) ^ 2 * (ldpHat f t) ^ 2 +
        (3 * integerCF f t - 1) * ldpHat f t + integerCF f t = 0 := hLdpQuad t
  have hroot_im : (ldpHat f t).im ≠ 0 := by
    apply hroot (ldpHat f t)
    simpa only [integerCF] using hquad
  have hcubic := characteristic_cubic_identity_of_quadratic
    (integerCF f t).re (ldpK f t) (ldpHat f t)
    (hLdpReal t) hroot_im (by simpa only [hFcast] using hquad)
  have hcubic' :
      ((integerCF f t).re - 1) ^ 3 +
        (3 - ldpK f t) * (integerCF f t).re ^ 2 = 0 := by
    linear_combination hcubic
  have hK : 3 - ldpK f t = (3 + f 0) * (1 - Real.cos t) := by
    dsimp [ldpK]
    ring
  rw [← hFcast, ← hK]
  exact_mod_cast hcubic'

/-- The cubic balance forces the normalized LDP defect cubed to converge to
`(3 + f 0) / 2`. Proposition 6.2, -/
theorem ldp_normalized_cubic_tendsto
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x)
    (hgsupp : ∀ y, 0 ≤ y → g y = 0)
    (hrec : ∀ x y : ℤ, y ≤ -1 →
      3 * f x * g y =
        f x * f y +
        f x * ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1), g (y + j) * g (-j) +
        (if y = -1 then
          (∑' j : ℕ, f ((j : ℤ) + x + 1) * f (-(j : ℤ))) + g (-x - 1)
         else 0))
    (hLdpQuad : ∀ t : ℝ,
      (integerCF f t) ^ 2 * (ldpHat f t) ^ 2 +
        (3 * integerCF f t - 1) * ldpHat f t + integerCF f t = 0)
    (hLdpReal : ∀ t : ℝ,
      (ldpHat f t).re = ((integerCF f t).re - ldpK f t) / 2) :
    Tendsto
      (fun t : ℝ => ((1 - (integerCF f t).re) / t ^ (2 / 3 : ℝ)) ^ 3)
      (𝓝[>] (0 : ℝ)) (𝓝 ((3 + f 0) / 2)) := by
  obtain ⟨δ, hδ, hrel⟩ := ldp_cubic_relation_of_master
    hf hfs hg hgs hsymm hgsupp hrec hLdpQuad hLdpReal
  let u : ℝ → ℝ := fun t => (1 - (integerCF f t).re) / t ^ (2 / 3 : ℝ)
  let q : ℝ → ℝ := fun t => (3 + f 0) *
    ((1 - Real.cos t) / t ^ 2) * (integerCF f t).re ^ 2
  have hden (t : ℝ) (ht : 0 < t) : (t ^ (2 / 3 : ℝ)) ^ 3 = t ^ 2 := by
    calc
      (t ^ (2 / 3 : ℝ)) ^ 3 = (t ^ (2 / 3 : ℝ)) ^ (3 : ℝ) :=
        (Real.rpow_natCast _ _).symm
      _ = t ^ ((2 / 3 : ℝ) * 3) := (Real.rpow_mul ht.le _ _).symm
      _ = t ^ (2 : ℝ) := by congr 1; norm_num
      _ = t ^ 2 := Real.rpow_natCast t 2
  have hbalance (t : ℝ) (ht : 0 < t) (htd : t < δ) : u t ^ 3 = q t := by
    have hrelC := hrel t ht htd
    have hFcast : ((integerCF f t).re : ℂ) = integerCF f t := by
      apply Complex.ext
      · simp only [Complex.ofReal_re]
      · simpa only [Complex.ofReal_im] using
          (integerCF_im hf hfs.summable hsymm t).symm
    have hrelR :
        ((integerCF f t).re - 1) ^ 3 +
          (3 + f 0) * (1 - Real.cos t) * (integerCF f t).re ^ 2 = 0 := by
      rw [← hFcast] at hrelC
      exact_mod_cast hrelC
    have hbalance' : (1 - (integerCF f t).re) ^ 3 =
        (3 + f 0) * (1 - Real.cos t) * (integerCF f t).re ^ 2 := by
      have hcube : ((integerCF f t).re - 1) ^ 3 =
          -((1 - (integerCF f t).re) ^ 3) := by ring
      rw [hcube] at hrelR
      linarith only [hrelR]
    change ((1 - (integerCF f t).re) / t ^ (2 / 3 : ℝ)) ^ 3 =
      (3 + f 0) * ((1 - Real.cos t) / t ^ 2) * (integerCF f t).re ^ 2
    calc
      _ = (1 - (integerCF f t).re) ^ 3 / t ^ 2 := by rw [div_pow, hden t ht]
      _ = ((3 + f 0) * (1 - Real.cos t) * (integerCF f t).re ^ 2) / t ^ 2 := by
        rw [hbalance']
      _ = (3 + f 0) * ((1 - Real.cos t) / t ^ 2) *
          (integerCF f t).re ^ 2 := by ring
  have hcos : Tendsto (fun t : ℝ => (1 - Real.cos t) / t ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
    apply one_sub_cos_div_sq_tendsto_half.mono_left
    exact nhdsWithin_mono 0 (by intro t ht; exact ne_of_gt ht)
  have hF : Tendsto (fun t : ℝ => (integerCF f t).re)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp
      (integerCF_tendsto_one hf hfs hsymm)
    exact h.mono_left nhdsWithin_le_nhds
  have hq : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 ((3 + f 0) / 2)) := by
    change Tendsto (fun t : ℝ => (3 + f 0) *
      ((1 - Real.cos t) / t ^ 2) * (integerCF f t).re ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 ((3 + f 0) / 2))
    have hconst : Tendsto (fun _ : ℝ => 3 + f 0)
        (𝓝[>] (0 : ℝ)) (𝓝 (3 + f 0)) := tendsto_const_nhds
    have h := (hconst.mul hcos).mul (hF.mul hF)
    simpa [q, one_pow, mul_one, div_eq_mul_inv, one_div, mul_assoc, pow_two] using h
  apply hq.congr'
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
  exact (hbalance t ht.1 ht.2).symm

/-- The source real transform expansion of Proposition 6.2,
from the exact quadratic, not supplied as an asymptotic premise. -/
theorem ldp_real_transform_expansion
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x)
    (hgsupp : ∀ y, 0 ≤ y → g y = 0)
    (hrec : ∀ x y : ℤ, y ≤ -1 →
      3 * f x * g y =
        f x * f y +
        f x * ∑ j ∈ Finset.Icc (1 : ℤ) (-y - 1), g (y + j) * g (-j) +
        (if y = -1 then
          (∑' j : ℕ, f ((j : ℤ) + x + 1) * f (-(j : ℤ))) + g (-x - 1)
         else 0))
    (hLdpQuad : ∀ t : ℝ,
      (integerCF f t) ^ 2 * (ldpHat f t) ^ 2 +
        (3 * integerCF f t - 1) * ldpHat f t + integerCF f t = 0)
    (hLdpReal : ∀ t : ℝ,
      (ldpHat f t).re = ((integerCF f t).re - ldpK f t) / 2) :
    let κ : ℝ := 3 + f 0
    let a : ℝ := (κ / 2) ^ (1 / 3 : ℝ)
    0 < κ ∧
      (fun t : ℝ => integerCF f t -
        ((1 : ℂ) - (a : ℂ) * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)))
        =o[𝓝[>] (0 : ℝ)]
          (fun t : ℝ => ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)) := by
  dsimp only
  obtain ⟨_, hf0pos⟩ := ldp_pmf_nondegenerate_of_master
    hf hfs hg hgs hsymm hgsupp hrec
  have hκ : 0 < 3 + f 0 := by linarith
  constructor
  · exact hκ
  · let a : ℝ := ((3 + f 0) / 2) ^ (1 / 3 : ℝ)
    let u : ℝ → ℝ := fun t =>
      (1 - (integerCF f t).re) / t ^ (2 / 3 : ℝ)
    have hbase : 0 < (3 + f 0) / 2 := div_pos hκ (by norm_num)
    have hcube := ldp_normalized_cubic_tendsto
      hf hfs hg hgs hsymm hgsupp hrec hLdpQuad hLdpReal
    have hroot : Tendsto (fun t : ℝ => (u t ^ 3) ^ (1 / 3 : ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 a) := by
      have h := (Real.continuousAt_rpow_const ((3 + f 0) / 2)
        (1 / 3 : ℝ) (Or.inl hbase.ne')).tendsto.comp hcube
      simpa only [Function.comp_def, u, a] using h
    have hu : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 a) := by
      apply hroot.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      have hu_nonneg : 0 ≤ u t := by
        dsimp [u]
        apply div_nonneg
        · linarith [integerCF_re_le_one hf hfs t]
        · exact (Real.rpow_pos_of_pos ht _).le
      have heq : u t = (u t ^ 3) ^ (1 / 3 : ℝ) := by
        calc
          u t = u t ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = u t ^ ((3 : ℝ) * (1 / 3 : ℝ)) := by congr 1; norm_num
          _ = (u t ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := Real.rpow_mul hu_nonneg _ _
          _ = (u t ^ 3) ^ (1 / 3 : ℝ) :=
            congrArg (fun x : ℝ => x ^ (1 / 3 : ℝ)) (Real.rpow_natCast (u t) 3)
      exact heq.symm
    have hau : Tendsto (fun t : ℝ => ((a - u t : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
      have hreal : Tendsto (fun t : ℝ => a - u t)
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have ha : Tendsto (fun _ : ℝ => a) (𝓝[>] (0 : ℝ)) (𝓝 a) :=
          tendsto_const_nhds
        simpa only [sub_self] using ha.sub hu
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    have hsmall : (fun t : ℝ => ((a - u t : ℝ) : ℂ)) =o[𝓝[>] (0 : ℝ)]
        (fun _ => (1 : ℂ)) := (isLittleO_one_iff ℂ).2 hau
    have hprod := hsmall.mul_isBigO
      (isBigO_refl (fun t : ℝ => ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)))
    have hscale : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        (1 : ℂ) * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ) =
          ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ) := by
      filter_upwards with t
      simp
    have hnum : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        ((a - u t : ℝ) : ℂ) * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ) =
          integerCF f t -
            ((1 : ℂ) - (a : ℂ) * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have hFcast : integerCF f t = ((integerCF f t).re : ℂ) := by
        apply Complex.ext
        · simp only [Complex.ofReal_re]
        · simpa only [Complex.ofReal_im] using
            (integerCF_im hf hfs.summable hsymm t)
      rw [hFcast]
      dsimp [u]
      have hpow : t ^ (2 / 3 : ℝ) ≠ 0 :=
        (Real.rpow_pos_of_pos ht _).ne'
      push_cast
      field_simp [hpow]
      ring
    have hfinal := hprod.congr' hnum hscale
    simpa only [one_mul] using hfinal

end LDP

end DirectedDistances.Recursive
