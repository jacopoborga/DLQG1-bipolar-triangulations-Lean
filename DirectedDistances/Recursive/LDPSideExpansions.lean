/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Recursive.LDPExpansionF
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Candidate LDP side-transform branches

The quadratic roots underlying Proposition 6.2,
expanded here from the checked real-transform expansion. Selecting the
source branch still requires Proposition 6.1 applied to the reflected law. -/

public section
namespace DirectedDistances.Recursive

open Filter Asymptotics
open scoped Topology

/-- The characteristic transform of the reflected positive part of a law
supported on negative integers, `eq:Ghat` in -/
@[expose] noncomputable def reflectedPositiveCF (p : ℤ → ℝ) (t : ℝ) : ℂ :=
  ∑' k : {k : ℤ // 1 ≤ k}, (p (-k) : ℂ) *
    Complex.exp ((((t * (k : ℝ) : ℝ) : ℂ) * Complex.I))

/-- The negative-imaginary quadratic root for the LDP transform, written
using the real characteristic value. It is defined on the whole real carrier;
the square-root formula is used asymptotically where its radicand is positive. -/
@[expose] noncomputable def ldpQuadraticRootMinus (f : ℤ → ℝ) (t : ℝ) : ℂ :=
  let F := (integerCF f t).re
  (-1 : ℂ) + (((1 - F) * (1 - 2 * F) / (2 * F ^ 2) : ℝ) : ℂ) -
    (((1 - F) * Real.sqrt (4 * F - 1) / (2 * F ^ 2) : ℝ) : ℂ) * Complex.I

/-- The positive-imaginary quadratic root for the LDP transform, written
using the real characteristic value. Proposition 6.2, -/
@[expose] noncomputable def ldpQuadraticRootPlus (f : ℤ → ℝ) (t : ℝ) : ℂ :=
  let F := (integerCF f t).re
  (-1 : ℂ) + (((1 - F) * (1 - 2 * F) / (2 * F ^ 2) : ℝ) : ℂ) +
    (((1 - F) * Real.sqrt (4 * F - 1) / (2 * F ^ 2) : ℝ) : ℂ) * Complex.I

/-- Factorization of the discriminant of the LDP quadratic. Proposition 6.2, -/
theorem ldp_quadratic_discriminant_factorization (F : ℝ) :
    (3 * F - 1) ^ 2 - 4 * F ^ 3 = -(F - 1) ^ 2 * (4 * F - 1) := by
  ring


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
variable (_hLdpGhat : ∀ t : ℝ,
  reflectedPositiveCF g t = -integerCF f t * ldpHat f t)

/-- Both quadratic branches have the two candidate coefficients in the LDP
side-transform expansion. The hypotheses are exactly those of
`ldp_real_transform_expansion` plus the source identity `eq:Ghat`; the
identity is retained here because the selected branch is intended to feed the
reflected-law argument. Proposition 6.2,

The remaining branch choice is to prove that the reflected characteristic
transform has the positive-imaginary coefficient, by constructing its genuine
nonnegative integer law and applying Proposition 6.1 at `ν = 2/3`.
In terms of these branches, the exact selector still needed is
`∃ δ > 0, ∀ t, 0 < t → t < δ → ldpHat f t = ldpQuadraticRootMinus f t`. -/
theorem ldp_side_candidate_root_expansions
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
      (ldpHat f t).re = ((integerCF f t).re - ldpK f t) / 2)
    (_hLdpGhat : ∀ t : ℝ,
      reflectedPositiveCF g t = -integerCF f t * ldpHat f t) :
    let κ : ℝ := 3 + f 0
    let a : ℝ := (κ / 2) ^ (1 / 3 : ℝ)
    let dMinus : ℂ := ((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2
    let dPlus : ℂ := ((-1 : ℂ) + (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2
    0 < κ ∧
      Tendsto (fun t : ℝ => (ldpQuadraticRootMinus f t + 1) /
        ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (dMinus * (a : ℂ))) ∧
      Tendsto (fun t : ℝ => (ldpQuadraticRootPlus f t + 1) /
        ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (dPlus * (a : ℂ))) := by
  dsimp only
  obtain ⟨hκ, _hPacket1Expansion⟩ := ldp_real_transform_expansion
    hf hfs hg hgs hsymm hgsupp hrec hLdpQuad hLdpReal
  refine ⟨hκ, ?_, ?_⟩
  · -- Negative-imaginary candidate.
    let F : ℝ → ℝ := fun t => (integerCF f t).re
    let ε : ℝ → ℝ := fun t => t ^ (2 / 3 : ℝ)
    let u : ℝ → ℝ := fun t => (1 - F t) / ε t
    let A : ℝ → ℝ := fun t => (1 - 2 * F t) / (2 * F t ^ 2)
    let B : ℝ → ℝ := fun t => Real.sqrt (4 * F t - 1) / (2 * F t ^ 2)
    let a : ℝ := ((3 + f 0) / 2) ^ (1 / 3 : ℝ)
    have hcub := ldp_normalized_cubic_tendsto
      hf hfs hg hgs hsymm hgsupp hrec hLdpQuad hLdpReal
    have hF : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have h := Complex.continuous_re.continuousAt.tendsto.comp
        (integerCF_tendsto_one hf hfs hsymm)
      exact h.mono_left nhdsWithin_le_nhds
    have hbase : 0 < (3 + f 0) / 2 := by linarith
    have hroot : Tendsto (fun t : ℝ => (u t ^ 3) ^ (1 / 3 : ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 a) := by
      have h := (Real.continuousAt_rpow_const ((3 + f 0) / 2)
        (1 / 3 : ℝ) (Or.inl hbase.ne')).tendsto.comp hcub
      simpa only [Function.comp_def, u, a] using h
    have hu : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 a) := by
      apply hroot.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      have hu_nonneg : 0 ≤ u t := by
        dsimp [u, ε, F]
        apply div_nonneg
        · linarith [integerCF_re_le_one hf hfs t]
        · exact (Real.rpow_pos_of_pos ht _).le
      have heq : u t = (u t ^ 3) ^ (1 / 3 : ℝ) := by
        calc
          u t = u t ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = u t ^ ((3 : ℝ) * (1 / 3 : ℝ)) := by congr 1 ; norm_num
          _ = (u t ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := Real.rpow_mul hu_nonneg _ _
          _ = (u t ^ 3) ^ (1 / 3 : ℝ) :=
            congrArg (fun x : ℝ => x ^ (1 / 3 : ℝ)) (Real.rpow_natCast (u t) 3)
      exact heq.symm
    have hA : Tendsto A (𝓝[>] (0 : ℝ)) (𝓝 (-1 / 2 : ℝ)) := by
      have hnum : Tendsto (fun t => 1 - 2 * F t)
          (𝓝[>] (0 : ℝ)) (𝓝 (-1 : ℝ)) := by
        have hmul := hF.const_mul (2 : ℝ)
        have hconst : Tendsto (fun _ : ℝ => (1 : ℝ))
            (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
        convert hconst.sub hmul using 1 ; norm_num
      have hden : Tendsto (fun t => 2 * F t ^ 2)
          (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ)) := by
        simpa using (hF.pow 2).const_mul (2 : ℝ)
      have h := hnum.div hden (by norm_num : (2 : ℝ) ≠ 0)
      change Tendsto (fun t => (1 - 2 * F t) / (2 * F t ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 (-1 / 2 : ℝ))
      exact h
    have hB : Tendsto B (𝓝[>] (0 : ℝ))
        (𝓝 (Real.sqrt 3 / 2 : ℝ)) := by
      have hrad : Tendsto (fun t => 4 * F t - 1)
          (𝓝[>] (0 : ℝ)) (𝓝 (3 : ℝ)) := by
        have hmul := hF.const_mul (4 : ℝ)
        convert hmul.sub_const 1 using 1 ; norm_num
      have hsqrt : Tendsto (fun t => Real.sqrt (4 * F t - 1))
          (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 3)) := by
        exact Real.continuous_sqrt.continuousAt.tendsto.comp hrad
      have hden : Tendsto (fun t => 2 * F t ^ 2)
          (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ)) := by
        simpa using (hF.pow 2).const_mul (2 : ℝ)
      have h := hsqrt.div hden (by norm_num : (2 : ℝ) ≠ 0)
      change Tendsto (fun t => Real.sqrt (4 * F t - 1) / (2 * F t ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 3 / 2 : ℝ))
      exact h
    have hrealA : Tendsto (fun t => ((u t * A t : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 ((a * (-1 / 2 : ℝ) : ℝ) : ℂ)) := by
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp (hu.mul hA)
    have hrealBI : Tendsto (fun t => ((u t * B t : ℝ) : ℂ) * Complex.I)
        (𝓝[>] (0 : ℝ))
        (𝓝 (((a * (Real.sqrt 3 / 2 : ℝ) : ℝ) : ℂ) * Complex.I)) := by
      exact (Complex.continuous_ofReal.continuousAt.tendsto.comp (hu.mul hB)).mul
        tendsto_const_nhds
    have hFne : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), F t ≠ 0 :=
      hF.eventually_ne (by norm_num)
    have hratio : Tendsto
        (fun t => (ldpQuadraticRootMinus f t + 1) / (ε t : ℂ))
        (𝓝[>] (0 : ℝ))
        (𝓝 (((a * (-1 / 2 : ℝ) : ℝ) : ℂ) -
          (((a * (Real.sqrt 3 / 2 : ℝ) : ℝ) : ℂ) * Complex.I))) := by
      apply (hrealA.sub hrealBI).congr'
      filter_upwards [self_mem_nhdsWithin, hFne] with t ht hFt
      have hε : ε t ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
      dsimp [ldpQuadraticRootMinus, ε, F, u, A, B]
      field_simp [hFt, hε]
      ; push_cast
      ; ring
    have hratio' : Tendsto
        (fun t => (ldpQuadraticRootMinus f t + 1) / (ε t : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (((((-1 : ℂ) - (Real.sqrt 3 : ℂ) * Complex.I) / 2) *
          (a : ℂ)))) := by
      convert hratio using 1 ; congr 1 ; push_cast ; ring
    exact hratio'
  · -- Positive-imaginary candidate; the real estimates are shared, while
    -- the sign of the square-root term is reversed.
    let F : ℝ → ℝ := fun t => (integerCF f t).re
    let ε : ℝ → ℝ := fun t => t ^ (2 / 3 : ℝ)
    let u : ℝ → ℝ := fun t => (1 - F t) / ε t
    let A : ℝ → ℝ := fun t => (1 - 2 * F t) / (2 * F t ^ 2)
    let B : ℝ → ℝ := fun t => Real.sqrt (4 * F t - 1) / (2 * F t ^ 2)
    let a : ℝ := ((3 + f 0) / 2) ^ (1 / 3 : ℝ)
    have hcub := ldp_normalized_cubic_tendsto
      hf hfs hg hgs hsymm hgsupp hrec hLdpQuad hLdpReal
    have hF : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have h := Complex.continuous_re.continuousAt.tendsto.comp
        (integerCF_tendsto_one hf hfs hsymm)
      exact h.mono_left nhdsWithin_le_nhds
    have hbase : 0 < (3 + f 0) / 2 := by linarith
    have hroot : Tendsto (fun t : ℝ => (u t ^ 3) ^ (1 / 3 : ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 a) := by
      have h := (Real.continuousAt_rpow_const ((3 + f 0) / 2)
        (1 / 3 : ℝ) (Or.inl hbase.ne')).tendsto.comp hcub
      simpa only [Function.comp_def, u, a] using h
    have hu : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 a) := by
      apply hroot.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      have hu_nonneg : 0 ≤ u t := by
        dsimp [u, ε, F]
        apply div_nonneg
        · linarith [integerCF_re_le_one hf hfs t]
        · exact (Real.rpow_pos_of_pos ht _).le
      have heq : u t = (u t ^ 3) ^ (1 / 3 : ℝ) := by
        calc
          u t = u t ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = u t ^ ((3 : ℝ) * (1 / 3 : ℝ)) := by congr 1 ; norm_num
          _ = (u t ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := Real.rpow_mul hu_nonneg _ _
          _ = (u t ^ 3) ^ (1 / 3 : ℝ) :=
            congrArg (fun x : ℝ => x ^ (1 / 3 : ℝ)) (Real.rpow_natCast (u t) 3)
      exact heq.symm
    have hA : Tendsto A (𝓝[>] (0 : ℝ)) (𝓝 (-1 / 2 : ℝ)) := by
      have hnum : Tendsto (fun t => 1 - 2 * F t)
          (𝓝[>] (0 : ℝ)) (𝓝 (-1 : ℝ)) := by
        have hmul := hF.const_mul (2 : ℝ)
        have hconst : Tendsto (fun _ : ℝ => (1 : ℝ))
            (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
        convert hconst.sub hmul using 1 ; norm_num
      have hden : Tendsto (fun t => 2 * F t ^ 2)
          (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ)) := by
        simpa using (hF.pow 2).const_mul (2 : ℝ)
      have h := hnum.div hden (by norm_num : (2 : ℝ) ≠ 0)
      change Tendsto (fun t => (1 - 2 * F t) / (2 * F t ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 (-1 / 2 : ℝ))
      exact h
    have hB : Tendsto B (𝓝[>] (0 : ℝ))
        (𝓝 (Real.sqrt 3 / 2 : ℝ)) := by
      have hrad : Tendsto (fun t => 4 * F t - 1)
          (𝓝[>] (0 : ℝ)) (𝓝 (3 : ℝ)) := by
        have hmul := hF.const_mul (4 : ℝ)
        convert hmul.sub_const 1 using 1 ; norm_num
      have hsqrt : Tendsto (fun t => Real.sqrt (4 * F t - 1))
          (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 3)) :=
        Real.continuous_sqrt.continuousAt.tendsto.comp hrad
      have hden : Tendsto (fun t => 2 * F t ^ 2)
          (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ)) := by
        simpa using (hF.pow 2).const_mul (2 : ℝ)
      have h := hsqrt.div hden (by norm_num : (2 : ℝ) ≠ 0)
      change Tendsto (fun t => Real.sqrt (4 * F t - 1) / (2 * F t ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 3 / 2 : ℝ))
      exact h
    have hrealA : Tendsto (fun t => ((u t * A t : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 ((a * (-1 / 2 : ℝ) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp (hu.mul hA)
    have hrealBI : Tendsto (fun t => ((u t * B t : ℝ) : ℂ) * Complex.I)
        (𝓝[>] (0 : ℝ))
        (𝓝 (((a * (Real.sqrt 3 / 2 : ℝ) : ℝ) : ℂ) * Complex.I)) :=
      (Complex.continuous_ofReal.continuousAt.tendsto.comp (hu.mul hB)).mul
        tendsto_const_nhds
    have hFne : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), F t ≠ 0 :=
      hF.eventually_ne (by norm_num)
    have hratio : Tendsto
        (fun t => (ldpQuadraticRootPlus f t + 1) / (ε t : ℂ))
        (𝓝[>] (0 : ℝ))
        (𝓝 (((a * (-1 / 2 : ℝ) : ℝ) : ℂ) +
          (((a * (Real.sqrt 3 / 2 : ℝ) : ℝ) : ℂ) * Complex.I))) := by
      apply (hrealA.add hrealBI).congr'
      filter_upwards [self_mem_nhdsWithin, hFne] with t ht hFt
      have hε : ε t ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
      dsimp [ldpQuadraticRootPlus, ε, F, u, A, B]
      field_simp [hFt, hε]
      ; push_cast
      ; ring
    have hratio' : Tendsto
        (fun t => (ldpQuadraticRootPlus f t + 1) / (ε t : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (((((-1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2) *
          (a : ℂ)))) := by
      convert hratio using 1 ; congr 1 ; push_cast ; ring
    exact hratio'

end LDP

end DirectedDistances.Recursive
