/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Recursive.SDPExpansionF
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Asymptotics.Ring
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import DirectedDistances.PaperProofs.Section6.Next.CharacteristicDiscriminant
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Real characteristic transform dichotomy for the SDP expansion

This proves the analytic dichotomy in Proposition 6.8, -/

public section
namespace DirectedDistances.Recursive.SDPExpansion

open Filter Asymptotics
open scoped Topology

/-- The real part of the SDP characteristic series, by the cosine-mass -/
theorem sdp_integerCF_re {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hs : Summable f) (t : ℝ) :
    (integerCF f t).re = ∑' k : ℤ, f k * Real.cos (t * (k : ℝ)) := by
  simpa only [integerCF] using
    DirectedDistances.PaperProofs.Section6.re_integer_characteristic_mass hf hs t

/-- Symmetry makes the SDP characteristic series real. -/
theorem sdp_integerCF_im {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hs : Summable f) (hsymm : ∀ k : ℤ, f (-k) = f k) (t : ℝ) :
    (integerCF f t).im = 0 := by
  simpa only [integerCF] using
    DirectedDistances.PaperProofs.Section6.im_integer_characteristic_mass_eq_zero
      hf hs hsymm t

/-- The real part of a nonnegative SDP characteristic mass is at most its
total mass. -/
theorem sdp_integerCF_re_le_one {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hfs : HasSum f (1 : ℝ)) (t : ℝ) : (integerCF f t).re ≤ 1 := by
  rw [sdp_integerCF_re hf hfs.summable t]
  have hcos := DirectedDistances.PaperProofs.Section6.summable_integer_cosine_mass
    hf hfs.summable t
  have hle := hcos.tsum_le_tsum
    (fun k => mul_le_of_le_one_right (hf k) (Real.cos_le_one _)) hfs.summable
  rw [hfs.tsum_eq] at hle
  exact hle

/-- The symmetric SDP characteristic series tends to one at the origin. -/
theorem sdp_integerCF_tendsto_one {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
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
  apply Complex.ext
  · exact (sdp_integerCF_re hf hfs.summable t).symm
  · simpa only [Complex.ofReal_im] using
      (sdp_integerCF_im hf hfs.summable hsymm t).symm

/-- The second-order cosine quotient at zero, restricted to positive inputs. -/
theorem sdp_one_sub_cos_div_sq_tendsto_half :
    Tendsto (fun t : ℝ => (1 - Real.cos t) / t ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
  have hs := Real.tendsto_sin_div_nhdsNE_zero
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
  have hne := hsq.const_mul (1 / 2 : ℝ)
  have hne' : Tendsto (fun t : ℝ => (1 - Real.cos t) / t ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
    simpa [hquot] using hne
  exact hne'.mono_left (nhdsWithin_mono 0 fun t ht => ne_of_gt ht)

/-- The fourth-order cosine quotient follows by squaring the second-order
limit; this avoids a separate cosine Taylor theorem. -/
theorem sdp_four_one_sub_cos_sq_div_fourth_tendsto_one :
    Tendsto (fun t : ℝ => 4 * (1 - Real.cos t) ^ 2 / t ^ 4)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
  have h := (sdp_one_sub_cos_div_sq_tendsto_half.pow 2).const_mul (4 : ℝ)
  have h' : Tendsto (fun t : ℝ => 4 * ((1 - Real.cos t) / t ^ 2) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    convert h using 1
    norm_num
  apply h'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hpow : t ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt ht)
  field_simp [hpow]

section SDP

variable {f g : ℤ → ℝ}
variable (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
variable (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
variable (hsymm : ∀ x, f (-x) = f x)
variable (hgsupp : ∀ y, y < -1 → g y = 0)
variable (hrec : ∀ x y : ℤ, -1 ≤ y →
  3 * f x * g y =
    f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j)) +
    (if y = -1 then
      (∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
        (g (-1)) ^ 2 * f (x + 1) + g (x - 1)
     else 0))
variable (hSdpQuad : ∀ t : ℝ,
  (integerCF f t) ^ 2 * (sdpHat f g t) ^ 2 +
    (3 * integerCF f t - 1) * sdpHat f g t + integerCF f t = 0)
variable (hSdpReal : ∀ t : ℝ,
  (sdpHat f g t).re = ((integerCF f t).re - sdpK f g t) / 2)



theorem sdp_normalized_cubic_tendsto
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x)
    (hgsupp : ∀ y, y < -1 → g y = 0)
    (hrec : ∀ x y : ℤ, -1 ≤ y →
      3 * f x * g y =
        f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j)) +
        (if y = -1 then
          (∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
            (g (-1)) ^ 2 * f (x + 1) + g (x - 1)
         else 0))
    (hSdpQuad : ∀ t : ℝ,
      (integerCF f t) ^ 2 * (sdpHat f g t) ^ 2 +
        (3 * integerCF f t - 1) * sdpHat f g t + integerCF f t = 0)
    (hSdpReal : ∀ t : ℝ,
      (sdpHat f g t).re = ((integerCF f t).re - sdpK f g t) / 2) :
    let κ : ℝ := 3 - 6 * (g (-1)) ^ 2 - f 0
    Tendsto
      (fun t : ℝ => ((1 - (integerCF f t).re) / t ^ (2 / 3 : ℝ)) ^ 3)
      (𝓝[>] (0 : ℝ)) (𝓝 (κ / 2)) := by
  dsimp only
  obtain ⟨δ, hδ, hrel⟩ := sdp_cubic_gap_identity_near_zero
    hf hfs hg hgs hsymm hgsupp hrec hSdpQuad hSdpReal
  let κ : ℝ := 3 - 6 * (g (-1)) ^ 2 - f 0
  let q : ℝ := (g (-1)) ^ 2
  let u : ℝ → ℝ := fun t => (1 - (integerCF f t).re) / t ^ (2 / 3 : ℝ)
  let v : ℝ → ℝ := fun t => (1 - Real.cos t) / t ^ 2
  let w : ℝ → ℝ := fun t => κ + 4 * q * (1 - Real.cos t)
  have hden (t : ℝ) (ht : 0 < t) :
      (t ^ (2 / 3 : ℝ)) ^ 3 = t ^ 2 := by
    calc
      (t ^ (2 / 3 : ℝ)) ^ 3 = (t ^ (2 / 3 : ℝ)) ^ (3 : ℝ) :=
        (Real.rpow_natCast _ _).symm
      _ = t ^ ((2 / 3 : ℝ) * 3) := (Real.rpow_mul ht.le _ _).symm
      _ = t ^ (2 : ℝ) := by congr 1; norm_num
      _ = t ^ 2 := Real.rpow_natCast t 2
  have hbalance (t : ℝ) (ht : 0 < t) (htd : t < δ) :
      u t ^ 3 = v t * w t * (integerCF f t).re ^ 2 := by
    have hrelC := hrel t ht htd
    have hrelR :
        ((integerCF f t).re - 1) ^ 3 +
          (1 - Real.cos t) * (κ + 4 * q * (1 - Real.cos t)) *
            (integerCF f t).re ^ 2 = 0 := by
      simpa only [κ, q] using hrelC
    have hdef : (1 - (integerCF f t).re) ^ 3 =
        (1 - Real.cos t) * (κ + 4 * q * (1 - Real.cos t)) *
          (integerCF f t).re ^ 2 := by
      have hcube : ((integerCF f t).re - 1) ^ 3 =
          -((1 - (integerCF f t).re) ^ 3) := by ring
      rw [hcube] at hrelR
      linarith only [hrelR]
    change ((1 - (integerCF f t).re) / t ^ (2 / 3 : ℝ)) ^ 3 =
      ((1 - Real.cos t) / t ^ 2) *
        (κ + 4 * q * (1 - Real.cos t)) * (integerCF f t).re ^ 2
    calc
      _ = (1 - (integerCF f t).re) ^ 3 / t ^ 2 := by rw [div_pow, hden t ht]
      _ = ((1 - Real.cos t) * (κ + 4 * q * (1 - Real.cos t)) *
          (integerCF f t).re ^ 2) / t ^ 2 := by rw [hdef]
      _ = ((1 - Real.cos t) / t ^ 2) *
          (κ + 4 * q * (1 - Real.cos t)) * (integerCF f t).re ^ 2 := by ring
  have hcos : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
    exact sdp_one_sub_cos_div_sq_tendsto_half
  have hF : Tendsto (fun t : ℝ => (integerCF f t).re)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp
      (sdp_integerCF_tendsto_one hf hfs hsymm)
    exact h.mono_left nhdsWithin_le_nhds
  have honecos : Tendsto (fun t : ℝ => 1 - Real.cos t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Tendsto Real.cos (𝓝 0) (𝓝 (1 : ℝ)) := by
      simpa using Real.continuous_cos.continuousAt.tendsto (x := 0)
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hc
    simpa only [sub_self] using h.mono_left nhdsWithin_le_nhds
  have hw : Tendsto w (𝓝[>] (0 : ℝ)) (𝓝 κ) := by
    simpa only [w, add_zero, mul_zero] using
      (tendsto_const_nhds (x := κ)).add
        ((tendsto_const_nhds (x := 4 * q)).mul honecos)
  have hq : Tendsto (fun t : ℝ => v t * w t * (integerCF f t).re ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (κ / 2)) := by
    have h := (hcos.mul hw).mul (hF.mul hF)
    convert h using 1
    · funext t
      ring
    · congr 1
      ring
  apply hq.congr'
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
  exact (hbalance t ht.1 ht.2).symm



theorem sdp_zero_kappa_normalized_cubic_tendsto
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x)
    (hgsupp : ∀ y, y < -1 → g y = 0)
    (hrec : ∀ x y : ℤ, -1 ≤ y →
      3 * f x * g y =
        f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j)) +
        (if y = -1 then
          (∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
            (g (-1)) ^ 2 * f (x + 1) + g (x - 1)
         else 0))
    (hSdpQuad : ∀ t : ℝ,
      (integerCF f t) ^ 2 * (sdpHat f g t) ^ 2 +
        (3 * integerCF f t - 1) * sdpHat f g t + integerCF f t = 0)
    (hSdpReal : ∀ t : ℝ,
      (sdpHat f g t).re = ((integerCF f t).re - sdpK f g t) / 2)
    (hκ :
    3 - 6 * (g (-1)) ^ 2 - f 0 = 0) :
    Tendsto
      (fun t : ℝ => ((1 - (integerCF f t).re) / t ^ (4 / 3 : ℝ)) ^ 3)
      (𝓝[>] (0 : ℝ)) (𝓝 ((g (-1)) ^ 2)) := by
  obtain ⟨δ, hδ, hrel⟩ := sdp_cubic_gap_identity_near_zero
    hf hfs hg hgs hsymm hgsupp hrec hSdpQuad hSdpReal
  let q : ℝ := (g (-1)) ^ 2
  let u : ℝ → ℝ := fun t => (1 - (integerCF f t).re) / t ^ (4 / 3 : ℝ)
  have hden (t : ℝ) (ht : 0 < t) :
      (t ^ (4 / 3 : ℝ)) ^ 3 = t ^ 4 := by
    calc
      (t ^ (4 / 3 : ℝ)) ^ 3 = (t ^ (4 / 3 : ℝ)) ^ (3 : ℝ) :=
        (Real.rpow_natCast _ _).symm
      _ = t ^ ((4 / 3 : ℝ) * 3) := (Real.rpow_mul ht.le _ _).symm
      _ = t ^ (4 : ℝ) := by congr 1; norm_num
      _ = t ^ 4 := Real.rpow_natCast t 4
  have hbalance (t : ℝ) (ht : 0 < t) (htd : t < δ) :
      u t ^ 3 = q * (4 * (1 - Real.cos t) ^ 2 / t ^ 4) *
        (integerCF f t).re ^ 2 := by
    have hrelC := hrel t ht htd
    have hrelR :
        ((integerCF f t).re - 1) ^ 3 +
          (1 - Real.cos t) * (0 + 4 * q * (1 - Real.cos t)) *
            (integerCF f t).re ^ 2 = 0 := by
      rw [hκ] at hrelC
      simpa only [q, zero_add] using hrelC
    have hdef : (1 - (integerCF f t).re) ^ 3 =
        4 * q * (1 - Real.cos t) ^ 2 * (integerCF f t).re ^ 2 := by
      have hcube : ((integerCF f t).re - 1) ^ 3 =
          -((1 - (integerCF f t).re) ^ 3) := by ring
      rw [hcube] at hrelR
      nlinarith only [hrelR]
    change ((1 - (integerCF f t).re) / t ^ (4 / 3 : ℝ)) ^ 3 =
      q * (4 * (1 - Real.cos t) ^ 2 / t ^ 4) * (integerCF f t).re ^ 2
    calc
      _ = (1 - (integerCF f t).re) ^ 3 / t ^ 4 := by rw [div_pow, hden t ht]
      _ = (4 * q * (1 - Real.cos t) ^ 2 * (integerCF f t).re ^ 2) / t ^ 4 := by
        rw [hdef]
      _ = q * (4 * (1 - Real.cos t) ^ 2 / t ^ 4) *
          (integerCF f t).re ^ 2 := by ring
  have hcos : Tendsto (fun t : ℝ => 4 * (1 - Real.cos t) ^ 2 / t ^ 4)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) :=
    sdp_four_one_sub_cos_sq_div_fourth_tendsto_one
  have hF : Tendsto (fun t : ℝ => (integerCF f t).re)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp
      (sdp_integerCF_tendsto_one hf hfs hsymm)
    exact h.mono_left nhdsWithin_le_nhds
  have hq : Tendsto
      (fun t : ℝ => q * (4 * (1 - Real.cos t) ^ 2 / t ^ 4) *
        (integerCF f t).re ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 q) := by
    have h := (tendsto_const_nhds (x := q)).mul hcos |>.mul (hF.mul hF)
    convert h using 1
    · funext t
      ring
    · congr 1
      ring
  apply hq.congr'
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
  exact (hbalance t ht.1 ht.2).symm

/-- A nonnegative normalized defect with a convergent cube has the real
cube-root limit. -/
theorem sdp_tendsto_of_cube_tendsto {u : ℝ → ℝ} {c : ℝ}
    (hc : 0 < c) (hu : Tendsto (fun t => (u t) ^ 3) (𝓝[>] (0 : ℝ)) (𝓝 c))
    (hnonneg : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ u t) :
    Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 (c ^ (1 / 3 : ℝ))) := by
  have hroot : Tendsto (fun t : ℝ => (u t ^ 3) ^ (1 / 3 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (c ^ (1 / 3 : ℝ))) := by
    exact (Real.continuousAt_rpow_const c (1 / 3 : ℝ) (Or.inl hc.ne')).tendsto.comp hu
  apply hroot.congr'
  filter_upwards [hnonneg] with t ht
  calc
    (u t ^ 3) ^ (1 / 3 : ℝ) = (u t ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by
      exact congrArg (fun x : ℝ => x ^ (1 / 3 : ℝ))
        (Real.rpow_natCast (u t) 3).symm
    _ = u t ^ ((3 : ℝ) * (1 / 3 : ℝ)) := (Real.rpow_mul ht _ _).symm
    _ = u t ^ (1 : ℝ) := by congr 1; norm_num
    _ = u t := by rw [Real.rpow_one]

/-- A normalized defect limit gives the corresponding complex little-o
expansion via `Asymptotics.isLittleO_iff_tendsto'`. -/
theorem sdp_expansion_of_normalized_limit
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x)
    (α a : ℝ)
    (hu : Tendsto
      (fun t : ℝ => (1 - (integerCF f t).re) / t ^ α)
      (𝓝[>] (0 : ℝ)) (𝓝 a)) :
    (fun t : ℝ => integerCF f t -
      ((1 : ℂ) - (a : ℂ) * ((t ^ α : ℝ) : ℂ)))
      =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => ((t ^ α : ℝ) : ℂ)) := by
  have hzero : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      ((t ^ α : ℝ) : ℂ) = 0 →
        integerCF f t - ((1 : ℂ) - (a : ℂ) * ((t ^ α : ℝ) : ℂ)) = 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht hden
    have hden' : ((t ^ α : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ht α).ne'
    exact (hden' hden).elim
  apply (isLittleO_iff_tendsto' hzero).2
  have hreal : Tendsto (fun t : ℝ => a -
      (1 - (integerCF f t).re) / t ^ α)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := a)).sub hu
  have hcoe := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  apply hcoe.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hFcast : integerCF f t = ((integerCF f t).re : ℂ) := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simpa only [Complex.ofReal_im] using
        (sdp_integerCF_im hf hfs.summable hsymm t)
  have hp : t ^ α ≠ 0 := (Real.rpow_pos_of_pos ht α).ne'
  have hnumR :
      (a - (1 - (integerCF f t).re) / t ^ α) * t ^ α =
        (integerCF f t).re - (1 - a * t ^ α) := by
    field_simp [hp]
    ring
  rw [hFcast]
  field_simp [Complex.ofReal_ne_zero.mpr hp]
  change ((a - (1 - (integerCF f t).re) / t ^ α : ℝ) : ℂ) *
      ((t ^ α : ℝ) : ℂ) = _
  calc
    _ = (((a - (1 - (integerCF f t).re) / t ^ α) * t ^ α : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
    _ = (((integerCF f t).re - (1 - a * t ^ α) : ℝ) : ℂ) :=
      congrArg Complex.ofReal hnumR
    _ = ((integerCF f t).re : ℂ) -
          ((1 : ℂ) - (a : ℂ) * ((t ^ α : ℝ) : ℂ)) := by
      simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul]

/-- The real characteristic-transform dichotomy in Proposition 6.8,
the balance and is not an assumption. -/
theorem sdp_real_transform_dichotomy
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x)
    (hgsupp : ∀ y, y < -1 → g y = 0)
    (hrec : ∀ x y : ℤ, -1 ≤ y →
      3 * f x * g y =
        f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j)) +
        (if y = -1 then
          (∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
            (g (-1)) ^ 2 * f (x + 1) + g (x - 1)
         else 0))
    (hSdpQuad : ∀ t : ℝ,
      (integerCF f t) ^ 2 * (sdpHat f g t) ^ 2 +
        (3 * integerCF f t - 1) * sdpHat f g t + integerCF f t = 0)
    (hSdpReal : ∀ t : ℝ,
      (sdpHat f g t).re = ((integerCF f t).re - sdpK f g t) / 2) :
    let κ : ℝ := 3 - 6 * (g (-1)) ^ 2 - f 0
    let a : ℝ := (κ / 2) ^ (1 / 3 : ℝ)
    let b : ℝ := (g (-1)) ^ (2 / 3 : ℝ)
    0 < g (-1) ∧
      ((κ = 0 ∧
        (fun t : ℝ => integerCF f t -
          ((1 : ℂ) - (b : ℂ) * ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ)))
          =o[𝓝[>] (0 : ℝ)]
            (fun t : ℝ => ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ))) ∨
       (0 < κ ∧
        (fun t : ℝ => integerCF f t -
          ((1 : ℂ) - (a : ℂ) * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)))
          =o[𝓝[>] (0 : ℝ)]
            (fun t : ℝ => ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)))) := by
  dsimp only
  obtain ⟨_, _, hgneg⟩ := sdp_real_transform_nondegenerate
    hf hfs hg hgs hsymm hgsupp hrec
  let κ : ℝ := 3 - 6 * (g (-1)) ^ 2 - f 0
  have hκnonneg : 0 ≤ κ := by
    have hcube := sdp_normalized_cubic_tendsto
      hf hfs hg hgs hsymm hgsupp hrec hSdpQuad hSdpReal
    have hnonneg : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        0 ≤ ((1 - (integerCF f t).re) / t ^ (2 / 3 : ℝ)) ^ 3 := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      apply pow_nonneg
      apply div_nonneg
      · linarith [sdp_integerCF_re_le_one hf hfs t]
      · exact (Real.rpow_pos_of_pos ht _).le
    have hlimnonneg : 0 ≤ κ / 2 := by
      by_contra hnot
      have hlt : κ / 2 < 0 := lt_of_not_ge hnot
      have hnegative := (tendsto_order.1 hcube).2 0 hlt
      obtain ⟨t, hneg, hpos⟩ := (hnegative.and hnonneg).exists
      linarith
    dsimp [κ]
    linarith
  refine ⟨hgneg, ?_⟩
  by_cases hκzero : κ = 0
  · left
    refine ⟨hκzero, ?_⟩
    let q : ℝ := (g (-1)) ^ 2
    let u : ℝ → ℝ := fun t => (1 - (integerCF f t).re) / t ^ (4 / 3 : ℝ)
    have hcube := sdp_zero_kappa_normalized_cubic_tendsto
      hf hfs hg hgs hsymm hgsupp hrec hSdpQuad hSdpReal (by simpa [κ] using hκzero)
    have hcubeq : Tendsto (fun t : ℝ => u t ^ 3)
        (𝓝[>] (0 : ℝ)) (𝓝 q) := by
      simpa only [u, q] using hcube
    have hnonneg : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ u t := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      dsimp [u]
      apply div_nonneg
      · linarith [sdp_integerCF_re_le_one hf hfs t]
      · exact (Real.rpow_pos_of_pos ht _).le
    have hu := sdp_tendsto_of_cube_tendsto
      (sq_pos_of_pos hgneg) hcubeq hnonneg
    have hb : q ^ (1 / 3 : ℝ) =
        (g (-1)) ^ (2 / 3 : ℝ) := by
      calc
        q ^ (1 / 3 : ℝ) = ((g (-1)) ^ 2) ^ (1 / 3 : ℝ) := rfl
        _ =
            ((g (-1)) ^ (2 : ℝ)) ^ (1 / 3 : ℝ) := by
              exact congrArg (fun x : ℝ => x ^ (1 / 3 : ℝ))
                (Real.rpow_natCast (g (-1)) 2).symm
        _ =
            (g (-1)) ^ ((2 : ℝ) * (1 / 3 : ℝ)) :=
              (Real.rpow_mul (le_of_lt hgneg) 2 (1 / 3 : ℝ)).symm
        _ = (g (-1)) ^ (2 / 3 : ℝ) := by congr 1; norm_num
    have hu' : Tendsto u (𝓝[>] (0 : ℝ))
        (𝓝 ((g (-1)) ^ (2 / 3 : ℝ))) := by
      simpa only [u, q, hb] using hu
    have hfinal := sdp_expansion_of_normalized_limit
      hf hfs hsymm
      (4 / 3 : ℝ) ((g (-1)) ^ (2 / 3 : ℝ)) (by simpa only [u] using hu')
    exact hfinal
  · right
    have hκpos : 0 < κ := lt_of_le_of_ne hκnonneg (Ne.symm hκzero)
    refine ⟨hκpos, ?_⟩
    let a : ℝ := (κ / 2) ^ (1 / 3 : ℝ)
    let u : ℝ → ℝ := fun t => (1 - (integerCF f t).re) / t ^ (2 / 3 : ℝ)
    have hcube := sdp_normalized_cubic_tendsto
      hf hfs hg hgs hsymm hgsupp hrec hSdpQuad hSdpReal
    have hnonneg : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ u t := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      dsimp [u]
      apply div_nonneg
      · linarith [sdp_integerCF_re_le_one hf hfs t]
      · exact (Real.rpow_pos_of_pos ht _).le
    have hu := sdp_tendsto_of_cube_tendsto
      (div_pos hκpos (by norm_num)) hcube hnonneg
    have hu' : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 a) := by
      simpa only [a] using hu
    exact sdp_expansion_of_normalized_limit
      hf hfs hsymm
      (2 / 3 : ℝ) a (by simpa only [u] using hu')

end SDP
end DirectedDistances.Recursive.SDPExpansion
