/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import DirectedDistances.Recursive.SDPNondegenerate
import DirectedDistances.Recursive.CharacteristicCubic
import DirectedDistances.PaperProofs.Section6.Next.CharacteristicDiscriminant
import Mathlib.Tactic.Ring







public section
namespace DirectedDistances.Recursive.SDPExpansion

open Filter
open scoped Topology

/-- The integer characteristic series `F` from `eq:FGdefs`, -/
@[expose] noncomputable def integerCF (p : ℤ → ℝ) (t : ℝ) : ℂ :=
  ∑' k : ℤ, (p k : ℂ) *
    Complex.exp ((((t * (k : ℝ) : ℝ) : ℂ) * Complex.I))

/-- The negative-index part `F⁻` from `eq:FGdefs`, -/
@[expose] noncomputable def negativeCF (p : ℤ → ℝ) (t : ℝ) : ℂ :=
  ∑' k : {k : ℤ // k ≤ -1}, (p k : ℂ) *
    Complex.exp ((((t * (k : ℝ) : ℝ) : ℂ) * Complex.I))

/-- The SDP offset `c(t)` from `eq:fhatmin` and `eq:defn-ct`, -/
@[expose] noncomputable def sdpOffset (f g : ℤ → ℝ) (t : ℝ) : ℂ :=
  (((2 * (g (-1)) ^ 2 : ℝ) : ℂ) +
    Complex.exp ((t : ℂ) * Complex.I) *
      ((-3 - 2 * (g (-1)) ^ 2 + f 0 : ℝ) : ℂ)) /
    (2 * Complex.exp ((((2 * t : ℝ) : ℂ) * Complex.I)))

/-- The shifted negative transform `\widehat F⁻` from `eq:fhatmin`, -/
@[expose] noncomputable def sdpHat (f g : ℤ → ℝ) (t : ℝ) : ℂ :=
  negativeCF f t + sdpOffset f g t

/-- The real function `K(t)` from `eq:real-part-fhat2`, -/
@[expose] noncomputable def sdpK (f g : ℤ → ℝ) (t : ℝ) : ℝ :=
  f 0 + (3 + 2 * (g (-1)) ^ 2 - f 0) * Real.cos t
      - 2 * (g (-1)) ^ 2 * Real.cos (2 * t)




theorem sdpK_gap_factorization (f g : ℤ → ℝ) (t : ℝ) :
    3 - sdpK f g t =
      (1 - Real.cos t) *
        ((3 - 6 * (g (-1)) ^ 2 - f 0) +
          4 * (g (-1)) ^ 2 * (1 - Real.cos t)) := by
  unfold sdpK
  rw [Real.cos_two_mul]
  ring

section SDP

variable {f g : ℤ → ℝ}



theorem sdp_real_transform_nondegenerate
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
         else 0)) :
    (∀ c : ℤ, f c < 1) ∧ 0 < f 0 ∧ 0 < g (-1) :=
  sdp_pmf_nondegenerate_of_master hf hfs hg hgs hsymm hgsupp hrec

/-- On a positive interval, the source quadratic and real-part identity yield
The nonzero imaginary part needed to divide out the quadratic's imaginary
part comes from the checked characteristic-discriminant helper. -/
theorem sdp_cubic_identity_near_zero
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
      (sdpHat f g t).re =
        ((integerCF f t).re - sdpK f g t) / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      (integerCF f t).im = 0 ∧
        (3 * (integerCF f t).re - 1) ^ 2 -
          4 * (integerCF f t).re ^ 3 < 0 ∧
        (sdpHat f g t).im ≠ 0 ∧
        (integerCF f t).re ^ 3 - sdpK f g t * (integerCF f t).re ^ 2 +
          3 * (integerCF f t).re - 1 = 0 := by
  have hnondeg := sdp_pmf_nondegenerate_of_master hf hfs hg hgs hsymm hgsupp hrec
  have hzero : f 0 < 1 := hnondeg.1 0
  obtain ⟨δ, hδ, hdisc⟩ :=
    DirectedDistances.PaperProofs.Section6.exists_integer_characteristic_discriminant_neg
      hf hfs hsymm hzero
  refine ⟨δ, hδ, ?_⟩
  intro t ht htd
  obtain ⟨him, hdiscneg, hroot⟩ := hdisc t ht htd
  change (integerCF f t).im = 0 at him
  change (3 * (integerCF f t).re - 1) ^ 2 -
    4 * (integerCF f t).re ^ 3 < 0 at hdiscneg
  have hrootHat := hroot (sdpHat f g t) (hSdpQuad t)
  have hcast : ((integerCF f t).re : ℂ) = integerCF f t := by
    apply Complex.ext
    · simp
    · simp [him]
  have hquad :
      ((integerCF f t).re : ℂ) ^ 2 * (sdpHat f g t) ^ 2 +
        (3 * ((integerCF f t).re : ℂ) - 1) * sdpHat f g t +
          ((integerCF f t).re : ℂ) = 0 := by
    rw [hcast]
    exact hSdpQuad t
  have hcubic :=
    characteristic_cubic_identity_of_quadratic
      (integerCF f t).re (sdpK f g t) (sdpHat f g t)
      (hSdpReal t) hrootHat hquad
  exact ⟨him, hdiscneg, hrootHat, hcubic⟩

/-- The cubic balance on the same positive interval, rewritten with the exact
factorization of `3 - K(t)`. -/
theorem sdp_cubic_gap_identity_near_zero
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
      (sdpHat f g t).re =
        ((integerCF f t).re - sdpK f g t) / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ((integerCF f t).re - 1) ^ 3 +
        (1 - Real.cos t) *
          ((3 - 6 * (g (-1)) ^ 2 - f 0) +
            4 * (g (-1)) ^ 2 * (1 - Real.cos t)) *
          (integerCF f t).re ^ 2 = 0 := by
  obtain ⟨δ, hδ, hcubic⟩ := sdp_cubic_identity_near_zero
    hf hfs hg hgs hsymm hgsupp hrec hSdpQuad hSdpReal
  refine ⟨δ, hδ, ?_⟩
  intro t ht htd
  obtain ⟨_, _, _, hcubic⟩ := hcubic t ht htd
  calc
    _ = (integerCF f t).re ^ 3 - sdpK f g t * (integerCF f t).re ^ 2 +
          3 * (integerCF f t).re - 1 := by
            rw [← sdpK_gap_factorization f g t]
            ring
    _ = 0 := hcubic

end SDP
end DirectedDistances.Recursive.SDPExpansion
