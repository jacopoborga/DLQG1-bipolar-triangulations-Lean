/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Recursive.SDPExpansionDichotomy
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import DirectedDistances.PaperProofs.Section6.Next.CharacteristicDiscriminant

/-! # Candidate roots for the SDP side transforms

This module expands both quadratic roots underlying the side-transform
767–842`. The exact remaining selector needed to finish data 4 is
`κ = 0 → ∃ δ > 0, ∀ t, 0 < t → t < δ → sdpHat f g t =
sdpQuadraticRootPlus f t`, and
`0 < κ → ∃ δ > 0, ∀ t, 0 < t → t < δ → sdpHat f g t =
sdpQuadraticRootMinus f t`. The continuity argument proving that one branch
is constant on a punctured interval is included below. The shifted-law bridge
to Proposition 6.1 and the second-order remainder estimate for `sdpOffset`
needed for the stated `negativeCF` expansions remain to be proved. -/

public section
namespace DirectedDistances.Recursive.SDPExpansion

open Filter Asymptotics
open scoped Topology

/-- The lower-imaginary quadratic root of the SDP transform equation, -/
@[expose] noncomputable def sdpQuadraticRootMinus (f : ℤ → ℝ) (t : ℝ) : ℂ :=
  let F := (integerCF f t).re
  (-1 : ℂ) + ((((1 - F) * (1 - 2 * F) / (2 * F ^ 2) : ℝ) : ℂ)) -
    ((((1 - F) * Real.sqrt (4 * F - 1) / (2 * F ^ 2) : ℝ) : ℂ)) * Complex.I

/-- The upper-imaginary quadratic root of the SDP transform equation, -/
@[expose] noncomputable def sdpQuadraticRootPlus (f : ℤ → ℝ) (t : ℝ) : ℂ :=
  let F := (integerCF f t).re
  (-1 : ℂ) + ((((1 - F) * (1 - 2 * F) / (2 * F ^ 2) : ℝ) : ℂ)) +
    ((((1 - F) * Real.sqrt (4 * F - 1) / (2 * F ^ 2) : ℝ) : ℂ)) * Complex.I

/-- The SDP characteristic series on the source support `k ≥ -1`, -/
@[expose] noncomputable def sdpCF (p : ℤ → ℝ) (t : ℝ) : ℂ :=
  ∑' k : {k : ℤ // -1 ≤ k}, (p k : ℂ) *
    Complex.exp ((((t * (k : ℝ) : ℝ) : ℂ) * Complex.I))




theorem sdpCF_scaled_limit_of_sdpHat_scaled_limit {f g : ℤ → ℝ}
    (hSdpG : ∀ t : ℝ,
      sdpCF g t = -integerCF f t * sdpHat f g t)
    {α c : ℝ} {d : ℂ} (hα : 0 < α)
    (hF : Tendsto
      (fun t : ℝ => ((1 : ℂ) - integerCF f t) /
        ((t ^ α : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (c : ℂ)))
    (hHat : Tendsto
      (fun t : ℝ => (sdpHat f g t + 1) /
        ((t ^ α : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (d * (c : ℂ)))) :
    Tendsto
      (fun t : ℝ => (sdpCF g t - 1) / ((t ^ α : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(c : ℂ) - d * (c : ℂ))) := by
  let ε : ℝ → ℂ := fun t => ((t ^ α : ℝ) : ℂ)
  let U : ℝ → ℂ := fun t => ((1 : ℂ) - integerCF f t) / ε t
  let V : ℝ → ℂ := fun t => (sdpHat f g t + 1) / ε t
  have hU : Tendsto U (𝓝[>] (0 : ℝ)) (𝓝 (c : ℂ)) := by
    simpa only [U, ε] using hF
  have hV : Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 (d * (c : ℂ))) := by
    simpa only [V, ε] using hHat
  have hpow : Tendsto (fun t : ℝ => t ^ α) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.comp
      (show Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) from
        tendsto_id.mono_left nhdsWithin_le_nhds)
    simpa only [Function.comp_def, Real.zero_rpow hα.ne'] using h
  have hε : Tendsto ε (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hpow
  have hlinear : Tendsto (fun t : ℝ => -U t - V t)
      (𝓝[>] (0 : ℝ)) (𝓝 (-(c : ℂ) - d * (c : ℂ))) := hU.neg.sub hV
  have hquad : Tendsto (fun t : ℝ => U t * V t * ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 ((c : ℂ) * (d * (c : ℂ)) * 0)) :=
    (hU.mul hV).mul hε
  have hsum : Tendsto (fun t : ℝ => -U t - V t + U t * V t * ε t)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-(c : ℂ) - d * (c : ℂ) + (c : ℂ) * (d * (c : ℂ)) * 0)) :=
    hlinear.add hquad
  have hsum' : Tendsto (fun t : ℝ => -U t - V t + U t * V t * ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 (-(c : ℂ) - d * (c : ℂ))) := by
    convert hsum using 1; congr 1; ring
  apply hsum'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hden : ε t ≠ 0 := by
    dsimp [ε]
    exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ht α).ne'
  dsimp [U, V, ε]
  rw [hSdpG]
  field_simp [hden]
  ring

/-- The quadratic discriminant factors through the same cubic defect used in -/
theorem sdp_quadratic_discriminant_factorization (F : ℝ) :
    (3 * F - 1) ^ 2 - 4 * F ^ 3 = -(F - 1) ^ 2 * (4 * F - 1) := by
  ring

private noncomputable def sdpRealRootMinus (F : ℝ) : ℂ :=
  (-1 : ℂ) + ((((1 - F) * (1 - 2 * F) / (2 * F ^ 2) : ℝ) : ℂ)) -
    ((((1 - F) * Real.sqrt (4 * F - 1) / (2 * F ^ 2) : ℝ) : ℂ)) * Complex.I

private noncomputable def sdpRealRootPlus (F : ℝ) : ℂ :=
  (-1 : ℂ) + ((((1 - F) * (1 - 2 * F) / (2 * F ^ 2) : ℝ) : ℂ)) +
    ((((1 - F) * Real.sqrt (4 * F - 1) / (2 * F ^ 2) : ℝ) : ℂ)) * Complex.I

private theorem sdpRealRootMinus_is_quadratic_root {F : ℝ} (hF : 1 / 4 < F) :
    (F : ℂ) ^ 2 * sdpRealRootMinus F ^ 2 +
      (3 * (F : ℂ) - 1) * sdpRealRootMinus F + (F : ℂ) = 0 := by
  have hFne : F ≠ 0 := by linarith
  have hsqrt : Real.sqrt (4 * F - 1) ^ 2 = 4 * F - 1 :=
    Real.sq_sqrt (by linarith)
  have hsqrtAlt : Real.sqrt (-1 + F * 4) ^ 2 = -1 + F * 4 := by
    rw [show -1 + F * 4 = 4 * F - 1 by ring]
    exact hsqrt
  have hsqrtC : ((Real.sqrt (-1 + F * 4) : ℝ) : ℂ) ^ 2 =
      ((-1 + F * 4 : ℝ) : ℂ) := by exact_mod_cast hsqrtAlt
  dsimp [sdpRealRootMinus]
  push_cast
  field_simp [hFne]
  ring_nf
  simp only [Complex.I_sq]
  rw [hsqrtC]
  push_cast
  ring

private theorem sdpRealRootPlus_is_quadratic_root {F : ℝ} (hF : 1 / 4 < F) :
    (F : ℂ) ^ 2 * sdpRealRootPlus F ^ 2 +
      (3 * (F : ℂ) - 1) * sdpRealRootPlus F + (F : ℂ) = 0 := by
  have hFne : F ≠ 0 := by linarith
  have hsqrt : Real.sqrt (4 * F - 1) ^ 2 = 4 * F - 1 :=
    Real.sq_sqrt (by linarith)
  have hsqrtAlt : Real.sqrt (-1 + F * 4) ^ 2 = -1 + F * 4 := by
    rw [show -1 + F * 4 = 4 * F - 1 by ring]
    exact hsqrt
  have hsqrtC : ((Real.sqrt (-1 + F * 4) : ℝ) : ℂ) ^ 2 =
      ((-1 + F * 4 : ℝ) : ℂ) := by exact_mod_cast hsqrtAlt
  dsimp [sdpRealRootPlus]
  push_cast
  field_simp [hFne]
  ring_nf
  simp only [Complex.I_sq]
  rw [hsqrtC]
  push_cast
  ring

/-- The two explicit SDP quadratic branches solve the source quadratic when
the radicand is positive, `eq:quadratic`, -/
theorem sdp_quadratic_candidate_roots_satisfy {f : ℤ → ℝ} (t : ℝ)
    (hF : 1 / 4 < (integerCF f t).re) :
    let F := (integerCF f t).re
    (F : ℂ) ^ 2 * sdpQuadraticRootMinus f t ^ 2 +
        (3 * (F : ℂ) - 1) * sdpQuadraticRootMinus f t + (F : ℂ) = 0 ∧
      (F : ℂ) ^ 2 * sdpQuadraticRootPlus f t ^ 2 +
        (3 * (F : ℂ) - 1) * sdpQuadraticRootPlus f t + (F : ℂ) = 0 := by
  dsimp only
  refine ⟨?_, ?_⟩
  · change ((integerCF f t).re : ℂ) ^ 2 *
      sdpRealRootMinus (integerCF f t).re ^ 2 +
      (3 * ((integerCF f t).re : ℂ) - 1) *
        sdpRealRootMinus (integerCF f t).re + ((integerCF f t).re : ℂ) = 0
    exact sdpRealRootMinus_is_quadratic_root hF
  · change ((integerCF f t).re : ℂ) ^ 2 *
      sdpRealRootPlus (integerCF f t).re ^ 2 +
      (3 * ((integerCF f t).re : ℂ) - 1) *
        sdpRealRootPlus (integerCF f t).re + ((integerCF f t).re : ℂ) = 0
    exact sdpRealRootPlus_is_quadratic_root hF

private theorem sdp_integerCF_continuous {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hs : Summable f) : Continuous (integerCF f) := by
  unfold integerCF
  apply continuous_tsum (fun k => continuous_const.mul
    (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).mul
        continuous_const))) hs
  intro k t
  change ‖(f k : ℂ) * Complex.exp
    ((((t * (k : ℝ) : ℝ) : ℂ) * Complex.I))‖ ≤ f k
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf k),
    Complex.norm_exp_ofReal_mul_I, mul_one]

private theorem sdp_negativeCF_continuous {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hs : Summable f) : Continuous (negativeCF f) := by
  unfold negativeCF
  apply continuous_tsum (fun k => continuous_const.mul
    (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).mul
        continuous_const))) (hs.subtype (fun k : ℤ => k ≤ -1))
  intro k t
  change ‖(f k : ℂ) * Complex.exp
    ((((t * (k : ℝ) : ℝ) : ℂ) * Complex.I))‖ ≤ f k
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf k),
    Complex.norm_exp_ofReal_mul_I, mul_one]

private theorem sdpOffset_continuous (f g : ℤ → ℝ) :
    Continuous (sdpOffset f g) := by
  have hphase : Continuous (fun t : ℝ => (t : ℂ) * Complex.I) :=
    Complex.continuous_ofReal.mul continuous_const
  have hphase2 : Continuous (fun t : ℝ => (((2 * t : ℝ) : ℂ) * Complex.I)) := by
    exact (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul
      continuous_const
  have hexp : Continuous (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp hphase
  have hexp2 : Continuous (fun t : ℝ =>
      Complex.exp (((2 * t : ℝ) : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp hphase2
  have hnum : Continuous (fun t : ℝ =>
      (((2 * (g (-1)) ^ 2 : ℝ) : ℂ) +
        Complex.exp ((t : ℂ) * Complex.I) *
          ((-3 - 2 * (g (-1)) ^ 2 + f 0 : ℝ) : ℂ))) :=
    continuous_const.add (hexp.mul continuous_const)
  have hden : Continuous (fun t : ℝ =>
      (2 : ℂ) * Complex.exp (((2 * t : ℝ) : ℂ) * Complex.I)) :=
    continuous_const.mul hexp2
  have hden_ne (t : ℝ) :
      (2 : ℂ) * Complex.exp (((2 * t : ℝ) : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)
  change Continuous (fun t : ℝ =>
    ((((2 * (g (-1)) ^ 2 : ℝ) : ℂ) +
      Complex.exp ((t : ℂ) * Complex.I) *
        ((-3 - 2 * (g (-1)) ^ 2 + f 0 : ℝ) : ℂ)) /
      ((2 : ℂ) * Complex.exp (((2 * t : ℝ) : ℂ) * Complex.I))))
  simpa only [Pi.div_def] using hnum.div hden hden_ne

private theorem sdpHat_continuous {f g : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hs : Summable f) : Continuous (sdpHat f g) := by
  change Continuous (fun t => negativeCF f t + sdpOffset f g t)
  exact (sdp_negativeCF_continuous hf hs).add (sdpOffset_continuous f g)

private theorem sdpOffset_exp_form (f g : ℤ → ℝ) (t : ℝ) :
    sdpOffset f g t =
      (((g (-1)) ^ 2 : ℝ) : ℂ) *
          Complex.exp (-(((2 * t : ℝ) : ℂ) * Complex.I)) +
        (((-3 - 2 * (g (-1)) ^ 2 + f 0) / 2 : ℝ) : ℂ) *
          Complex.exp (-((t : ℂ) * Complex.I)) := by
  let z : ℂ := (t : ℂ) * Complex.I
  have hphase : ((t : ℂ) * Complex.I) = z := rfl
  have hphase2 : (((2 * t : ℝ) : ℂ) * Complex.I) = 2 * z := by
    dsimp [z]
    push_cast
    ring
  have hexp2 : Complex.exp (2 * z) = Complex.exp z ^ 2 := by
    rw [show 2 * z = z + z by ring, Complex.exp_add]
    ring
  dsimp [sdpOffset]
  rw [hphase, hphase2, hexp2, Complex.exp_neg, Complex.exp_neg]
  field_simp [Complex.exp_ne_zero z]
  rw [hexp2]
  push_cast
  ring

/-- The offset has an explicit first-order Taylor polynomial and a remainder
bounded by a constant times `t^2`, `eq:defn-ct`, -/
theorem sdpOffset_second_order_remainder (f g : ℤ → ℝ) :
    (fun t : ℝ => sdpOffset f g t - (((f 0 - 3 : ℝ) / 2 : ℝ) : ℂ) -
      (((-(2 * (g (-1)) ^ 2 +
        (-3 - 2 * (g (-1)) ^ 2 + f 0) / 2) : ℝ) : ℂ) *
        ((t : ℝ) : ℂ) * Complex.I)) =O[𝓝 (0 : ℝ)]
      (fun t : ℝ => ((t ^ 2 : ℝ) : ℂ)) := by
  let q : ℝ := (g (-1)) ^ 2
  let c : ℝ := -3 - 2 * q + f 0
  let zOne : ℝ → ℂ := fun t => -((t : ℂ) * Complex.I)
  let zTwo : ℝ → ℂ := fun t => -(((2 * t : ℝ) : ℂ) * Complex.I)
  let R : ℂ → ℂ := fun z => Complex.exp z - 1 - z
  let C : ℝ := 4 * |q| + |c / 2|
  have hdecomp (t : ℝ) :
      sdpOffset f g t - (((f 0 - 3 : ℝ) / 2 : ℝ) : ℂ) -
        (((-(2 * q + c / 2) : ℝ) : ℂ) * ((t : ℝ) : ℂ) * Complex.I) =
      ((q : ℝ) : ℂ) * R (zTwo t) + ((c / 2 : ℝ) : ℂ) * R (zOne t) := by
    rw [sdpOffset_exp_form]
    dsimp [q, c, R, zOne, zTwo]
    push_cast
    ring
  have hRbound (z : ℂ) (hz : ‖z‖ ≤ 1) : ‖R z‖ ≤ ‖z‖ ^ 2 := by
    have h := Complex.exp_bound_sq 0 z hz
    simp only [zero_add, Complex.exp_zero, smul_eq_mul, mul_one, norm_one, one_mul] at h
    exact h
  have hnormOne (t : ℝ) : ‖zOne t‖ = |t| := by
    show ‖-((t : ℂ) * Complex.I)‖ = |t|
    rw [norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  have hnormTwo (t : ℝ) : ‖zTwo t‖ = 2 * |t| := by
    show ‖-(((2 * t : ℝ) : ℂ) * Complex.I)‖ = 2 * |t|
    rw [norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hbound (t : ℝ) (ht : |t| < 1 / 2) :
      ‖sdpOffset f g t - (((f 0 - 3 : ℝ) / 2 : ℝ) : ℂ) -
        (((-(2 * q + c / 2) : ℝ) : ℂ) * ((t : ℝ) : ℂ) * Complex.I)‖ ≤
        C * ‖((t ^ 2 : ℝ) : ℂ)‖ := by
    have hzOne : ‖zOne t‖ ≤ 1 := by
      rw [hnormOne]
      linarith
    have hzTwo : ‖zTwo t‖ ≤ 1 := by
      rw [hnormTwo]
      linarith
    have hR₁' : ‖R (zOne t)‖ ≤ t ^ 2 := by
      have h := hRbound _ hzOne
      rwa [hnormOne, sq_abs] at h
    have hR₂' : ‖R (zTwo t)‖ ≤ 4 * t ^ 2 := by
      have h := hRbound _ hzTwo
      rw [hnormTwo, mul_pow, sq_abs] at h
      linarith
    have ht2 : ‖((t ^ 2 : ℝ) : ℂ)‖ = t ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
    rw [hdecomp t, ht2]
    calc
      _ ≤ ‖((q : ℝ) : ℂ) * R (zTwo t)‖ +
          ‖((c / 2 : ℝ) : ℂ) * R (zOne t)‖ := norm_add_le _ _
      _ = |q| * ‖R (zTwo t)‖ + |c / 2| * ‖R (zOne t)‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |q| * (4 * t ^ 2) + |c / 2| * t ^ 2 := by
        gcongr
      _ = C * t ^ 2 := by
        simp only [C]
        ring
  rw [isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)]
    with t ht
  have ht' : |t| < 1 / 2 := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
  exact hbound t ht'

private theorem sdpHat_eq_candidate_root {f g : ℤ → ℝ} (t : ℝ)
    (hF : 1 / 4 < (integerCF f t).re)
    (hFcast : integerCF f t = ((integerCF f t).re : ℂ))
    (hSdpQuad :
      (integerCF f t) ^ 2 * (sdpHat f g t) ^ 2 +
        (3 * integerCF f t - 1) * sdpHat f g t + integerCF f t = 0) :
    sdpHat f g t = sdpQuadraticRootMinus f t ∨
      sdpHat f g t = sdpQuadraticRootPlus f t := by
  let F : ℝ := (integerCF f t).re
  let rMinus : ℂ := sdpQuadraticRootMinus f t
  let rPlus : ℂ := sdpQuadraticRootPlus f t
  have hFne : F ≠ 0 := by dsimp [F]; linarith
  have hFcast_ne : (F : ℂ) ≠ 0 := by exact_mod_cast hFne
  have hF2ne : (F : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hFcast_ne
  have hroots := sdp_quadratic_candidate_roots_satisfy (f := f) t hF
  have hrootMinus :
      (F : ℂ) ^ 2 * rMinus ^ 2 + (3 * (F : ℂ) - 1) * rMinus + (F : ℂ) = 0 := by
    simpa only [F, rMinus] using hroots.1
  let A : ℝ := (1 - F) * (1 - 2 * F) / (2 * F ^ 2)
  let B : ℝ := (1 - F) * Real.sqrt (4 * F - 1) / (2 * F ^ 2)
  have hrootMinusForm : rMinus = ((-1 + A : ℝ) : ℂ) - (B : ℂ) * Complex.I := by
    simp [rMinus, A, B, F, sdpQuadraticRootMinus]
  have hrootPlusForm : rPlus = ((-1 + A : ℝ) : ℂ) + (B : ℂ) * Complex.I := by
    simp [rPlus, A, B, F, sdpQuadraticRootPlus]
  have hsum : rMinus + rPlus = (((1 - 3 * F) / F ^ 2 : ℝ) : ℂ) := by
    rw [hrootMinusForm, hrootPlusForm]
    dsimp [A]
    push_cast
    field_simp [hFne]
    ring_nf
  have hsumzero :
      (F : ℂ) ^ 2 * (rMinus + rPlus) + (3 * (F : ℂ) - 1) = 0 := by
    rw [hsum]
    have hreal : F ^ 2 * ((1 - 3 * F) / F ^ 2) + (3 * F - 1) = 0 := by
      field_simp [hFne]
      ring
    exact_mod_cast hreal
  have hFcast' : (F : ℂ) = integerCF f t := by
    dsimp [F]
    exact hFcast.symm
  have hactual :
      (F : ℂ) ^ 2 * (sdpHat f g t) ^ 2 +
        (3 * (F : ℂ) - 1) * sdpHat f g t + (F : ℂ) = 0 := by
    rw [hFcast']
    exact hSdpQuad
  let Q : ℂ → ℂ := fun z =>
    (F : ℂ) ^ 2 * z ^ 2 + (3 * (F : ℂ) - 1) * z + (F : ℂ)
  have hfactor (z : ℂ) : Q z - Q rMinus =
      (z - rMinus) * ((F : ℂ) ^ 2 * (z + rMinus) + (3 * (F : ℂ) - 1)) := by
    dsimp [Q]
    ring
  have hprod : (sdpHat f g t - rMinus) *
      ((F : ℂ) ^ 2 * (sdpHat f g t + rMinus) + (3 * (F : ℂ) - 1)) = 0 := by
    calc
      _ = Q (sdpHat f g t) - Q rMinus := (hfactor _).symm
      _ = 0 := by simp only [Q, hactual, hrootMinus, sub_self]
  rcases mul_eq_zero.mp hprod with hminus | hfactorZero
  · exact Or.inl (sub_eq_zero.mp hminus)
  · have hplusFactor : (F : ℂ) ^ 2 * (sdpHat f g t - rPlus) = 0 := by
      calc
        _ = ((F : ℂ) ^ 2 * (sdpHat f g t + rMinus) +
              (3 * (F : ℂ) - 1)) -
            ((F : ℂ) ^ 2 * (rMinus + rPlus) + (3 * (F : ℂ) - 1)) := by ring
        _ = 0 := by rw [hfactorZero, hsumzero]; ring
    have hplus : sdpHat f g t - rPlus = 0 := by
      exact (mul_eq_zero.mp hplusFactor).resolve_left hF2ne
    exact Or.inr (sub_eq_zero.mp hplus)




theorem sdp_quadratic_branch_constancy {f g : ℤ → ℝ}
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
    (_hSdpReal : ∀ t : ℝ,
      (sdpHat f g t).re = ((integerCF f t).re - sdpK f g t) / 2) :
    ∃ δ : ℝ, 0 < δ ∧
      ((∀ t : ℝ, 0 < t → t < δ →
          sdpHat f g t = sdpQuadraticRootPlus f t) ∨
       (∀ t : ℝ, 0 < t → t < δ →
          sdpHat f g t = sdpQuadraticRootMinus f t)) := by
  obtain ⟨hzero, _, _⟩ := sdp_real_transform_nondegenerate
    hf hfs hg hgs hsymm hgsupp hrec
  obtain ⟨δ, hδ, hinterval⟩ :=
    DirectedDistances.PaperProofs.Section6.exists_integer_cosine_mass_interval
      hf hfs (hzero 0)
  let F : ℝ → ℝ := fun t => (integerCF f t).re
  have hFcont : Continuous F := by
    exact Complex.continuous_re.comp (sdp_integerCF_continuous hf hfs.summable)
  have hFbounds (t : ℝ) (ht : 0 < t) (htd : t < δ) :
      1 / 4 < F t ∧ F t < 1 := by
    have hcos := hinterval t ht htd
    have hFcos : F t = ∑' k : ℤ, f k * Real.cos (t * (k : ℝ)) := by
      exact sdp_integerCF_re hf hfs.summable t
    rw [hFcos]
    exact hcos
  have hFcast (t : ℝ) : integerCF f t = ((F t : ℝ) : ℂ) := by
    apply Complex.ext
    · rfl
    · dsimp [F]
      simpa only [Complex.ofReal_im] using
        sdp_integerCF_im hf hfs.summable hsymm t
  let S : Set ℝ := Set.Ioo (0 : ℝ) δ
  let X := {t : ℝ // t ∈ S}
  let A : ℝ → ℝ := fun t => (1 - F t) * (1 - 2 * F t) / (2 * F t ^ 2)
  let B : ℝ → ℝ := fun t =>
    (1 - F t) * Real.sqrt (4 * F t - 1) / (2 * F t ^ 2)
  let den : ℝ → ℝ := fun t => 2 * F t ^ 2
  have hdenCont : Continuous den := by
    exact continuous_const.mul (hFcont.pow 2)
  have hdenNe (t : ℝ) (ht : t ∈ S) : den t ≠ 0 := by
    have hpos : 0 < F t := by
      have := hFbounds t ht.1 ht.2
      linarith
    dsimp [den]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hpos.ne')
  have hAnumCont : Continuous (fun t : ℝ => (1 - F t) * (1 - 2 * F t)) := by
    exact (continuous_const.sub hFcont).mul
      (continuous_const.sub (continuous_const.mul hFcont))
  have hAcont : ContinuousOn A S := by
    change ContinuousOn
      (fun t : ℝ => (1 - F t) * (1 - 2 * F t) / (2 * F t ^ 2)) S
    exact hAnumCont.continuousOn.div hdenCont.continuousOn hdenNe
  have hsqrtCont : Continuous (fun t : ℝ => Real.sqrt (4 * F t - 1)) := by
    exact Real.continuous_sqrt.comp
      ((continuous_const.mul hFcont).sub continuous_const)
  have hBnumCont : Continuous
      (fun t : ℝ => (1 - F t) * Real.sqrt (4 * F t - 1)) :=
    (continuous_const.sub hFcont).mul hsqrtCont
  have hBcont : ContinuousOn B S := by
    change ContinuousOn
      (fun t : ℝ => (1 - F t) * Real.sqrt (4 * F t - 1) /
        (2 * F t ^ 2)) S
    exact hBnumCont.continuousOn.div hdenCont.continuousOn hdenNe
  have hAcast : ContinuousOn (fun t : ℝ => (A t : ℂ)) S := by
    exact Complex.continuous_ofReal.comp_continuousOn' hAcont
  have hBcast : ContinuousOn (fun t : ℝ => (B t : ℂ)) S := by
    exact Complex.continuous_ofReal.comp_continuousOn' hBcont
  have hrealPartCont : ContinuousOn
      (fun t : ℝ => ((-1 + A t : ℝ) : ℂ)) S := by
    exact Complex.continuous_ofReal.comp_continuousOn'
      (continuousOn_const.add hAcont)
  have hIcont : ContinuousOn (fun _ : ℝ => Complex.I) S := continuousOn_const
  have hBimagCont : ContinuousOn (fun t : ℝ => (B t : ℂ) * Complex.I) S :=
    hBcast.mul hIcont
  have hminusFormula :
      (fun t : ℝ => sdpQuadraticRootMinus f t) =
        (fun t => ((-1 + A t : ℝ) : ℂ) - (B t : ℂ) * Complex.I) := by
    funext t
    simp [sdpQuadraticRootMinus, A, B, F]
  have hplusFormula :
      (fun t : ℝ => sdpQuadraticRootPlus f t) =
        (fun t => ((-1 + A t : ℝ) : ℂ) + (B t : ℂ) * Complex.I) := by
    funext t
    simp [sdpQuadraticRootPlus, A, B, F]
  have hminusCont : ContinuousOn (fun t : ℝ => sdpQuadraticRootMinus f t) S := by
    rw [hminusFormula]
    exact hrealPartCont.sub hBimagCont
  have hplusCont : ContinuousOn (fun t : ℝ => sdpQuadraticRootPlus f t) S := by
    rw [hplusFormula]
    exact hrealPartCont.add hBimagCont
  have hBpos (t : ℝ) (ht : t ∈ S) : 0 < B t := by
    obtain ⟨hlo, hhi⟩ := hFbounds t ht.1 ht.2
    have hFpos : 0 < F t := by linarith
    have hrad : 0 < 4 * F t - 1 := by linarith
    have hsqrt : 0 < Real.sqrt (4 * F t - 1) := Real.sqrt_pos.2 hrad
    have hnum : 0 < (1 - F t) * Real.sqrt (4 * F t - 1) :=
      mul_pos (by linarith) hsqrt
    have hden : 0 < 2 * F t ^ 2 :=
      mul_pos (by norm_num) (sq_pos_of_pos hFpos)
    dsimp [B]
    exact div_pos hnum hden
  let minusBranch : Set X := {x | sdpHat f g x.val = sdpQuadraticRootMinus f x.val}
  let plusBranch : Set X := {x | sdpHat f g x.val = sdpQuadraticRootPlus f x.val}
  have hhatCont : Continuous (fun x : X => sdpHat f g x.val) :=
    (sdpHat_continuous hf hfs.summable).comp continuous_subtype_val
  have hminusX : Continuous (fun x : X => sdpQuadraticRootMinus f x.val) :=
    hminusCont.domRestrict
  have hplusX : Continuous (fun x : X => sdpQuadraticRootPlus f x.val) :=
    hplusCont.domRestrict
  have hminusClosed : IsClosed minusBranch := by
    exact isClosed_eq hhatCont hminusX
  have hplusClosed : IsClosed plusBranch := by
    exact isClosed_eq hhatCont hplusX
  have hchoose (x : X) : x ∈ minusBranch ∨ x ∈ plusBranch := by
    have ht := x.property
    obtain ⟨hlo, _⟩ := hFbounds x.val ht.1 ht.2
    have hroots := sdpHat_eq_candidate_root x.val hlo (hFcast x.val) (hSdpQuad x.val)
    exact hroots
  have hnoBoth (x : X) (hminus : x ∈ minusBranch) (hplus : x ∈ plusBranch) : False := by
    have hrootEq : sdpQuadraticRootPlus f x.val = sdpQuadraticRootMinus f x.val :=
      hplus.symm.trans hminus
    have him := congrArg Complex.im hrootEq
    rw [congrFun hplusFormula x.val, congrFun hminusFormula x.val] at him
    simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, zero_add, add_zero] at him
    have := hBpos x.val x.property
    linarith
  have hbranchComplement : minusBranchᶜ = plusBranch := by
    ext x
    constructor
    · intro hnot
      rcases hchoose x with hminus | hplus
      · exact (hnot hminus).elim
      · exact hplus
    · intro hplus hminus
      exact (hnoBoth x hminus hplus).elim
  have hminusOpen : IsOpen minusBranch := by
    have hEq : minusBranch = plusBranchᶜ := by
      simpa only [compl_compl] using congrArg (fun C : Set X => Cᶜ) hbranchComplement
    rw [hEq]
    exact hplusClosed.isOpen_compl
  have hplusOpen : IsOpen plusBranch := by
    have hEq : plusBranch = minusBranchᶜ := hbranchComplement.symm
    rw [hEq]
    exact hminusClosed.isOpen_compl
  have hpre : PreconnectedSpace X := by
    apply isPreconnected_iff_preconnectedSpace.mp
    simpa [S] using (isPreconnected_Ioo (a := (0 : ℝ)) (b := δ))
  rcases (@isClopen_iff X _ hpre minusBranch).mp ⟨hminusClosed, hminusOpen⟩
      with hEmpty | hUniv
  · refine ⟨δ, hδ, Or.inl ?_⟩
    intro t ht htd
    let x : X := ⟨t, by simp [S, ht, htd]⟩
    have hnot : x ∉ minusBranch := by rw [hEmpty]; simp
    rcases hchoose x with hm | hp
    · exact (hnot hm).elim
    · exact hp
  · refine ⟨δ, hδ, Or.inr ?_⟩
    intro t ht htd
    let x : X := ⟨t, by simp [S, ht, htd]⟩
    have hx : x ∈ minusBranch := by rw [hUniv]; simp
    exact hx

private theorem sdp_root_candidates_scaled {F u : ℝ → ℝ} {α c : ℝ}
    (hF : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 1))
    (hu : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 c))
    (hfactor : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      1 - F t = u t * t ^ α) :
    Tendsto
        (fun t : ℝ => (sdpRealRootMinus (F t) + 1) / ((t ^ α : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ))
        (𝓝 (((((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2) *
          (c : ℂ)))) ∧
      Tendsto
        (fun t : ℝ => (sdpRealRootPlus (F t) + 1) / ((t ^ α : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ))
        (𝓝 (((((-1 : ℂ) + (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2) *
          (c : ℂ)))) := by
  let A : ℝ → ℝ := fun t => (1 - 2 * F t) / (2 * F t ^ 2)
  let B : ℝ → ℝ := fun t => Real.sqrt (4 * F t - 1) / (2 * F t ^ 2)
  have hA : Tendsto A (𝓝[>] (0 : ℝ)) (𝓝 (-1 / 2 : ℝ)) := by
    have hnum : Tendsto (fun t => 1 - 2 * F t)
        (𝓝[>] (0 : ℝ)) (𝓝 (-1 : ℝ)) := by
      have hmul := hF.const_mul (2 : ℝ)
      convert (tendsto_const_nhds (x := (1 : ℝ))).sub hmul using 1
      norm_num
    have hden : Tendsto (fun t => 2 * F t ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ)) := by
      simpa using (hF.pow 2).const_mul (2 : ℝ)
    change Tendsto (fun t => (1 - 2 * F t) / (2 * F t ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (-1 / 2 : ℝ))
    exact hnum.div hden (by norm_num)
  have hrad : Tendsto (fun t => 4 * F t - 1)
      (𝓝[>] (0 : ℝ)) (𝓝 (3 : ℝ)) := by
    have hmul := hF.const_mul (4 : ℝ)
    convert hmul.sub_const 1 using 1
    norm_num
  have hsqrt : Tendsto (fun t => Real.sqrt (4 * F t - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 3)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hrad
  have hden : Tendsto (fun t => 2 * F t ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ)) := by
    simpa using (hF.pow 2).const_mul (2 : ℝ)
  have hB : Tendsto B (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 3 / 2 : ℝ)) := by
    change Tendsto (fun t => Real.sqrt (4 * F t - 1) / (2 * F t ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 3 / 2 : ℝ))
    exact hsqrt.div hden (by norm_num)
  have hreal : Tendsto (fun t => ((u t * A t : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((c * (-1 / 2 : ℝ) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp (hu.mul hA)
  have himag : Tendsto (fun t => ((u t * B t : ℝ) : ℂ) * Complex.I)
      (𝓝[>] (0 : ℝ))
      (𝓝 (((c * (Real.sqrt 3 / 2 : ℝ) : ℝ) : ℂ) * Complex.I)) :=
    (Complex.continuous_ofReal.continuousAt.tendsto.comp (hu.mul hB)).mul
      tendsto_const_nhds
  have hFne : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), F t ≠ 0 :=
    hF.eventually_ne (by norm_num)
  constructor
  · have hlim := hreal.sub himag
    have hlim' : Tendsto
        (fun t => ((u t * A t : ℝ) : ℂ) - ((u t * B t : ℝ) : ℂ) * Complex.I)
        (𝓝[>] (0 : ℝ))
        (𝓝 (((((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2) *
          (c : ℂ)))) := by
      convert hlim using 1; congr 1; push_cast; ring
    apply hlim'.congr'
    filter_upwards [hfactor, hFne, self_mem_nhdsWithin] with t hfac hFt ht
    have hε : t ^ α ≠ 0 := (Real.rpow_pos_of_pos ht α).ne'
    dsimp [sdpRealRootMinus, A, B]
    rw [hfac]
    field_simp [hFt, hε]
    push_cast
    ring
  · have hlim := hreal.add himag
    have hlim' : Tendsto
        (fun t => ((u t * A t : ℝ) : ℂ) + ((u t * B t : ℝ) : ℂ) * Complex.I)
        (𝓝[>] (0 : ℝ))
        (𝓝 (((((-1 : ℂ) + (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2) *
          (c : ℂ)))) := by
      convert hlim using 1; congr 1; push_cast; ring
    apply hlim'.congr'
    filter_upwards [hfactor, hFne, self_mem_nhdsWithin] with t hfac hFt ht
    have hε : t ^ α ≠ 0 := (Real.rpow_pos_of_pos ht α).ne'
    dsimp [sdpRealRootPlus, A, B]
    rw [hfac]
    field_simp [hFt, hε]
    push_cast
    ring

section SDP

variable {f g : ℤ → ℝ}

/-- Both candidate quadratic roots have the predicted scaled limits in each
SDP scaling regime. This does not choose which root is the source transform, -/
theorem sdp_transform_candidate_root_expansions
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
    (_hSdpG : ∀ t : ℝ,
      sdpCF g t = -integerCF f t * sdpHat f g t) :
    let κ : ℝ := 3 - 6 * (g (-1)) ^ 2 - f 0
    let a : ℝ := (κ / 2) ^ (1 / 3 : ℝ)
    let b : ℝ := (g (-1)) ^ (2 / 3 : ℝ)
    let dMinus : ℂ := ((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2
    let dPlus : ℂ := ((-1 : ℂ) + (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2
    0 < g (-1) ∧
      ((κ = 0 ∧
        Tendsto (fun t : ℝ => (sdpQuadraticRootMinus f t + 1) /
          ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (dMinus * (b : ℂ))) ∧
        Tendsto (fun t : ℝ => (sdpQuadraticRootPlus f t + 1) /
          ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (dPlus * (b : ℂ)))) ∨
       (0 < κ ∧
        Tendsto (fun t : ℝ => (sdpQuadraticRootMinus f t + 1) /
          ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (dMinus * (a : ℂ))) ∧
        Tendsto (fun t : ℝ => (sdpQuadraticRootPlus f t + 1) /
          ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (dPlus * (a : ℂ))))) := by
  dsimp only
  obtain ⟨hgneg, hpacket⟩ := sdp_real_transform_dichotomy
    hf hfs hg hgs hsymm hgsupp hrec hSdpQuad hSdpReal
  let κ : ℝ := 3 - 6 * (g (-1)) ^ 2 - f 0
  let F : ℝ → ℝ := fun t => (integerCF f t).re
  have hF : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp
      (sdp_integerCF_tendsto_one hf hfs hsymm)
    exact h.mono_left nhdsWithin_le_nhds
  refine ⟨hgneg, ?_⟩
  rcases hpacket with ⟨hκzero, _hFexp⟩ | ⟨hκpos, _hFexp⟩
  · left
    let q : ℝ := (g (-1)) ^ 2
    let u : ℝ → ℝ := fun t => (1 - F t) / t ^ (4 / 3 : ℝ)
    have hcube := sdp_zero_kappa_normalized_cubic_tendsto
      hf hfs hg hgs hsymm hgsupp hrec hSdpQuad hSdpReal hκzero
    have hnonneg : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ u t := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      dsimp [u, F]
      apply div_nonneg
      · linarith [sdp_integerCF_re_le_one hf hfs t]
      · exact (Real.rpow_pos_of_pos ht _).le
    have hu := sdp_tendsto_of_cube_tendsto
      (sq_pos_of_pos hgneg) (by simpa only [u, q, F] using hcube) hnonneg
    have hb : q ^ (1 / 3 : ℝ) = (g (-1)) ^ (2 / 3 : ℝ) := by
      calc
        q ^ (1 / 3 : ℝ) = ((g (-1)) ^ 2) ^ (1 / 3 : ℝ) := rfl
        _ = ((g (-1)) ^ (2 : ℝ)) ^ (1 / 3 : ℝ) := by
          exact congrArg (fun x : ℝ => x ^ (1 / 3 : ℝ))
            (Real.rpow_natCast (g (-1)) 2).symm
        _ = (g (-1)) ^ ((2 : ℝ) * (1 / 3 : ℝ)) :=
          (Real.rpow_mul (le_of_lt hgneg) 2 (1 / 3 : ℝ)).symm
        _ = (g (-1)) ^ (2 / 3 : ℝ) := by congr 1; norm_num
    have hb' : ((g (-1)) ^ 2) ^ (1 / 3 : ℝ) =
        (g (-1)) ^ (2 / 3 : ℝ) := by simpa only [q] using hb
    have hu' : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 ((g (-1)) ^ (2 / 3 : ℝ))) := by
      simpa only [hb'] using hu
    have hfactor : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        1 - F t = u t * t ^ (4 / 3 : ℝ) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have hp : t ^ (4 / 3 : ℝ) ≠ 0 :=
        (Real.rpow_pos_of_pos ht (4 / 3 : ℝ)).ne'
      dsimp [u]
      field_simp [hp]
    have hroots := sdp_root_candidates_scaled hF hu' hfactor
    refine ⟨hκzero, ?_, ?_⟩
    · simpa only [sdpQuadraticRootMinus, sdpRealRootMinus, F] using hroots.1
    · simpa only [sdpQuadraticRootPlus, sdpRealRootPlus, F] using hroots.2
  · right
    let u : ℝ → ℝ := fun t => (1 - F t) / t ^ (2 / 3 : ℝ)
    have hcube := sdp_normalized_cubic_tendsto
      hf hfs hg hgs hsymm hgsupp hrec hSdpQuad hSdpReal
    have hnonneg : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ u t := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      dsimp [u, F]
      apply div_nonneg
      · linarith [sdp_integerCF_re_le_one hf hfs t]
      · exact (Real.rpow_pos_of_pos ht _).le
    have hκpositive : 0 < κ := by simpa only [κ] using hκpos
    have hcube' : Tendsto (fun t : ℝ => u t ^ 3)
        (𝓝[>] (0 : ℝ)) (𝓝 (κ / 2)) := by
      simpa only [u, F, κ] using hcube
    have hu := sdp_tendsto_of_cube_tendsto (c := κ / 2)
      (div_pos hκpositive (by norm_num)) hcube' hnonneg
    let a : ℝ := (κ / 2) ^ (1 / 3 : ℝ)
    have hu' : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 a) := by simpa only [a] using hu
    have hfactor : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        1 - F t = u t * t ^ (2 / 3 : ℝ) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have hp : t ^ (2 / 3 : ℝ) ≠ 0 :=
        (Real.rpow_pos_of_pos ht (2 / 3 : ℝ)).ne'
      dsimp [u]
      field_simp [hp]
    have hroots := sdp_root_candidates_scaled hF hu' hfactor
    refine ⟨hκpos, ?_, ?_⟩
    · simpa only [sdpQuadraticRootMinus, sdpRealRootMinus, F] using hroots.1
    · simpa only [sdpQuadraticRootPlus, sdpRealRootPlus, F] using hroots.2

end SDP
end DirectedDistances.Recursive.SDPExpansion
