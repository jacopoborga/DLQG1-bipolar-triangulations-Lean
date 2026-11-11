/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Recursive.SDPSideExpansions
import DirectedDistances.Recursive.SDPQuadraticFromMaster
import DirectedDistances.Paper.Section6.Tauberian
import DirectedDistances.Tauberian.NormalizedBoundary
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # SDP side-transform branch selection

The source selector and side expansions in Proposition 6.8 use -/

public section
namespace DirectedDistances.Recursive.SDPExpansion

open Filter Asymptotics
open MeasureTheory
open scoped Topology

variable {f g : ℤ → ℝ}

private theorem sdp_negative_nat_mass
    (hfs : HasSum f (1 : ℝ)) (hsymm : ∀ x, f (-x) = f x) :
    HasSum (fun n : ℕ => f (-((n : ℤ) + 1))) ((1 - f 0) / 2) := by
  have hpos : Summable (fun n : ℕ => f n) :=
    hfs.summable.comp_injective Nat.cast_injective
  have hneg : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) := by
    apply hfs.summable.comp_injective
    intro a b hab
    simp only [neg_inj, add_left_inj, Nat.cast_inj] at hab
    exact hab
  have hwhole : (∑' k : ℤ, f k) =
      (∑' n : ℕ, f n) + ∑' n : ℕ, f (-((n : ℤ) + 1)) :=
    tsum_of_nat_of_neg_add_one hpos hneg
  have hsplit := hpos.tsum_eq_zero_add
  have hreflect : (fun n : ℕ => f (-((n : ℤ) + 1))) =
      fun n : ℕ => f ((n + 1 : ℕ) : ℤ) := by
    funext n
    have hcast : -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hcast, hsymm]
  have htotal := hfs.tsum_eq
  rw [hwhole, hsplit, ← hreflect] at htotal
  have hmass : ∑' n : ℕ, f (-((n : ℤ) + 1)) = (1 - f 0) / 2 := by
    have htotal' : f 0 + (∑' n : ℕ, f (-((n : ℤ) + 1))) +
        ∑' n : ℕ, f (-((n : ℤ) + 1)) = 1 := by
      simpa using htotal
    
    linarith
  exact hmass ▸ hneg.hasSum

private def sdpNegativeIndexEquiv :
    ℕ ≃ {k : ℤ // k ≤ -1} where
  toFun n := ⟨-((n : ℤ) + 1), by omega⟩
  invFun k := (-k.val - 1).toNat
  left_inv n := by simp
  right_inv k := by
    apply Subtype.ext
    have hk : 0 ≤ -k.val - 1 := by omega
    have hcast : (((-k.val - 1).toNat : ℕ) : ℤ) = -k.val - 1 :=
      Int.toNat_of_nonneg hk
    change -((((-k.val - 1).toNat : ℕ) : ℤ) + 1) = k.val
    rw [hcast]
    omega

private theorem sdp_negative_subtype_mass
    (hfs : HasSum f (1 : ℝ)) (hsymm : ∀ x, f (-x) = f x) :
    HasSum (fun k : {k : ℤ // k ≤ -1} => f k.val) ((1 - f 0) / 2) := by
  have hnat := sdp_negative_nat_mass hfs hsymm
  have hnat' : HasSum
      (fun n : ℕ => (fun k : {k : ℤ // k ≤ -1} => f k.val)
        (sdpNegativeIndexEquiv n)) ((1 - f 0) / 2) := by
    convert hnat using 1
    funext n
    rfl
  exact sdpNegativeIndexEquiv.hasSum_iff.mp hnat'

private noncomputable def sdpNegativeSideLaw (f : ℤ → ℝ) :
    Measure {k : ℤ // k ≤ -1} :=
  Measure.sum fun k : {k : ℤ // k ≤ -1} =>
    ENNReal.ofReal (2 * f k.val / (1 - f 0)) • Measure.dirac k

private theorem sdpNegativeSideLaw_isProbability
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x) (hf0 : f 0 < 1) :
    IsProbabilityMeasure (sdpNegativeSideLaw f) := by
  have hmass := sdp_negative_subtype_mass hfs hsymm
  have hden : 0 < 1 - f 0 := by linarith
  have hs : HasSum (fun k : {k : ℤ // k ≤ -1} => 2 * f k.val / (1 - f 0)) 1 := by
    have hscaled := hmass.mul_left (2 / (1 - f 0))
    have hvalue : (2 / (1 - f 0)) * ((1 - f 0) / 2) = 1 := by
      field_simp
    convert hscaled using 1
    · funext k
      simp only [div_eq_mul_inv]
      ring
    · exact hvalue.symm
  exact HasSum.isProbabilityMeasure_sum_dirac (fun k => div_nonneg (mul_nonneg (by norm_num) (hf k.val)) hden.le) hs

private theorem sdpNegativeCF_neg (f : ℤ → ℝ) (t : ℝ) :
    negativeCF f (-t) = star (negativeCF f t) := by
  unfold negativeCF
  rw [Complex.star_def, Complex.conj_tsum]
  apply tsum_congr
  intro k
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  rw [Complex.conj_I]
  congr 1
  apply congrArg Complex.exp
  push_cast
  ring

private theorem sdpNegativeSideLaw_characteristic
    (f : ℤ → ℝ) (hf : ∀ x, 0 ≤ f x) (hf0 : f 0 < 1) (t : ℝ) :
    (∫ k : {k : ℤ // k ≤ -1},
      Complex.exp ((((t * (((-k.val).toNat : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)
      ∂sdpNegativeSideLaw f) =
      (((2 / (1 - f 0) : ℝ) : ℂ) * negativeCF f (-t)) := by
  let X : {k : ℤ // k ≤ -1} → ℕ := fun k => (-k.val).toNat
  have hXcast (k : {k : ℤ // k ≤ -1}) : (X k : ℝ) = (-k.val : ℝ) := by
    have hk : (X k : ℤ) = -k.val := Int.toNat_of_nonneg (by omega)
    exact_mod_cast hk
  have hc (k : {k : ℤ // k ≤ -1}) :
      ENNReal.ofReal (2 * f k.val / (1 - f 0)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hden : 0 < 1 - f 0 := by linarith
  change (∫ k : {k : ℤ // k ≤ -1},
      (Complex.exp ((((t * (X k : ℝ) : ℝ) : ℂ) * Complex.I)))
      ∂Measure.sum (fun k : {k : ℤ // k ≤ -1} =>
        ENNReal.ofReal (2 * f k.val / (1 - f 0)) • Measure.dirac k)) = _
  rw [integral_sum_dirac hc]
  unfold negativeCF
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  have hcast : (X k : ℝ) = (-k.val : ℝ) := hXcast k
  have hweight : 0 ≤ 2 * f k.val / (1 - f 0) :=
    div_nonneg (mul_nonneg (by norm_num) (hf k.val)) hden.le
  simp only [ENNReal.toReal_ofReal hweight]
  rw [hcast]
  simp only [Complex.real_smul]
  have hexp : Complex.exp ((((t * (-k.val : ℝ) : ℝ) : ℂ) * Complex.I)) =
      Complex.exp ((((-t * (k.val : ℝ) : ℝ) : ℂ) * Complex.I)) := by
    congr 1
    push_cast
    ring
  rw [hexp]
  push_cast
  field_simp [ne_of_gt hden]

private noncomputable def sdpSelectionRootMinus (F : ℝ) : ℂ :=
  (-1 : ℂ) + ((((1 - F) * (1 - 2 * F) / (2 * F ^ 2) : ℝ) : ℂ)) -
    ((((1 - F) * Real.sqrt (4 * F - 1) / (2 * F ^ 2) : ℝ) : ℂ)) * Complex.I

private noncomputable def sdpSelectionRootPlus (F : ℝ) : ℂ :=
  (-1 : ℂ) + ((((1 - F) * (1 - 2 * F) / (2 * F ^ 2) : ℝ) : ℂ)) +
    ((((1 - F) * Real.sqrt (4 * F - 1) / (2 * F ^ 2) : ℝ) : ℂ)) * Complex.I

private theorem sdp_selection_root_candidates_scaled {F u : ℝ → ℝ} {α c : ℝ}
    (hF : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 1))
    (hu : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 c))
    (hfactor : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 1 - F t = u t * t ^ α) :
    Tendsto (fun t : ℝ => (sdpSelectionRootMinus (F t) + 1) /
      ((t ^ α : ℝ) : ℂ)) (𝓝[>] (0 : ℝ))
        (𝓝 (((((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2) * (c : ℂ)))) ∧
    Tendsto (fun t : ℝ => (sdpSelectionRootPlus (F t) + 1) /
      ((t ^ α : ℝ) : ℂ)) (𝓝[>] (0 : ℝ))
        (𝓝 (((((-1 : ℂ) + (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2) * (c : ℂ)))) := by
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
        (𝓝 (((((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2) * (c : ℂ)))) := by
      convert hlim using 1; congr 1; push_cast; ring
    apply hlim'.congr'
    filter_upwards [hfactor, hFne, self_mem_nhdsWithin] with t hfac hFt ht
    have hε : t ^ α ≠ 0 := (Real.rpow_pos_of_pos ht α).ne'
    dsimp [sdpSelectionRootMinus, A, B]
    rw [hfac]
    field_simp [hFt, hε]
    push_cast
    ring
  · have hlim := hreal.add himag
    have hlim' : Tendsto
        (fun t => ((u t * A t : ℝ) : ℂ) + ((u t * B t : ℝ) : ℂ) * Complex.I)
        (𝓝[>] (0 : ℝ))
        (𝓝 (((((-1 : ℂ) + (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2) * (c : ℂ)))) := by
      convert hlim using 1; congr 1; push_cast; ring
    apply hlim'.congr'
    filter_upwards [hfactor, hFne, self_mem_nhdsWithin] with t hfac hFt ht
    have hε : t ^ α ≠ 0 := (Real.rpow_pos_of_pos ht α).ne'
    dsimp [sdpSelectionRootPlus, A, B]
    rw [hfac]
    field_simp [hFt, hε]
    push_cast
    ring

private theorem sdp_zero_kappa_root_limits
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
    (hκ : 3 - 6 * (g (-1)) ^ 2 - f 0 = 0) :
    Tendsto (fun t : ℝ => (sdpQuadraticRootMinus f t + 1) /
      ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ)) (𝓝[>] (0 : ℝ))
        (𝓝 (((((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2) *
          (((g (-1)) ^ (2 / 3 : ℝ) : ℝ) : ℂ)))) ∧
    Tendsto (fun t : ℝ => (sdpQuadraticRootPlus f t + 1) /
      ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ)) (𝓝[>] (0 : ℝ))
        (𝓝 (((((-1 : ℂ) + (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2) *
          (((g (-1)) ^ (2 / 3 : ℝ) : ℝ) : ℂ)))) := by
  have hquad := sdp_quadratic_of_master hf hfs hg hgs hsymm hgsupp hrec
  have hreal := sdp_real_part_of_symm (g := g) hf hfs hsymm
  obtain ⟨_, _, hgneg⟩ := sdp_real_transform_nondegenerate
    hf hfs hg hgs hsymm hgsupp hrec
  let F : ℝ → ℝ := fun t => (integerCF f t).re
  have hF : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp
      (sdp_integerCF_tendsto_one hf hfs hsymm)
    exact h.mono_left nhdsWithin_le_nhds
  let q : ℝ := (g (-1)) ^ 2
  let u : ℝ → ℝ := fun t => (1 - F t) / t ^ (4 / 3 : ℝ)
  have hcube := sdp_zero_kappa_normalized_cubic_tendsto
    hf hfs hg hgs hsymm hgsupp hrec hquad hreal hκ
  have hcube' : Tendsto (fun t : ℝ => u t ^ 3)
      (𝓝[>] (0 : ℝ)) (𝓝 q) := by
    simpa only [u, q, F] using hcube
  have hnonneg : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ u t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    dsimp [u, F]
    apply div_nonneg
    · linarith [sdp_integerCF_re_le_one hf hfs t]
    · exact (Real.rpow_pos_of_pos (Set.mem_Ioi.mp ht) _).le
  have hu := sdp_tendsto_of_cube_tendsto (sq_pos_of_pos hgneg) hcube' hnonneg
  have hb : q ^ (1 / 3 : ℝ) = (g (-1)) ^ (2 / 3 : ℝ) := by
    calc
      q ^ (1 / 3 : ℝ) = ((g (-1)) ^ 2) ^ (1 / 3 : ℝ) := rfl
      _ = ((g (-1)) ^ (2 : ℝ)) ^ (1 / 3 : ℝ) := by
        exact congrArg (fun x : ℝ => x ^ (1 / 3 : ℝ))
          (Real.rpow_natCast (g (-1)) 2).symm
      _ = (g (-1)) ^ ((2 : ℝ) * (1 / 3 : ℝ)) :=
        (Real.rpow_mul (le_of_lt hgneg) 2 (1 / 3 : ℝ)).symm
      _ = (g (-1)) ^ (2 / 3 : ℝ) := by congr 1; norm_num
  have hu' : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 ((g (-1)) ^ (2 / 3 : ℝ))) := by
    have hb' : ((g (-1)) ^ 2) ^ (1 / 3 : ℝ) =
        (g (-1)) ^ (2 / 3 : ℝ) := by
      simpa only [q] using hb
    simpa only [← hb'] using hu
  have hfactor : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      1 - F t = u t * t ^ (4 / 3 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hp : t ^ (4 / 3 : ℝ) ≠ 0 :=
      (Real.rpow_pos_of_pos (Set.mem_Ioi.mp ht) _).ne'
    dsimp [u]
    field_simp [hp]
  have hroots := sdp_selection_root_candidates_scaled hF hu' hfactor
  constructor
  · simpa only [sdpQuadraticRootMinus, sdpSelectionRootMinus, F] using hroots.1
  · simpa only [sdpQuadraticRootPlus, sdpSelectionRootPlus, F] using hroots.2

theorem sdp_side_nondegenerate_of_master
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
    f 0 < 1 ∧ 0 < g (-1) := by
  obtain ⟨hf_lt, _, hg_pos⟩ := sdp_real_transform_nondegenerate
    hf hfs hg hgs hsymm hgsupp hrec
  exact ⟨hf_lt 0, hg_pos⟩

theorem sdp_side_branch_constancy_of_master
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
    ∃ δ : ℝ, 0 < δ ∧
      ((∀ t : ℝ, 0 < t → t < δ →
          sdpHat f g t = sdpQuadraticRootPlus f t) ∨
       (∀ t : ℝ, 0 < t → t < δ →
          sdpHat f g t = sdpQuadraticRootMinus f t)) := by
  exact sdp_quadratic_branch_constancy hf hfs hg hgs hsymm hgsupp hrec
    (sdp_quadratic_of_master hf hfs hg hgs hsymm hgsupp hrec)
    (sdp_real_part_of_symm hf hfs hsymm)

private theorem sdp_tsq_isLittleO_tpow_four_thirds :
    (fun t : ℝ => ((t ^ 2 : ℝ) : ℂ)) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ)) := by
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono 0 (by
      intro t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt ht)
  have habs := (DirectedDistances.Tauberian.abs_sq_isLittleO_abs_rpow_one_add
    (ν := (1 / 3 : ℝ)) (by norm_num)).mono hle
  have hreal : (fun t : ℝ => t ^ 2) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (4 / 3 : ℝ)) := by
    apply habs.congr'
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [abs_of_pos ht]
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [abs_of_pos ht]
      congr 1
      norm_num
  apply Complex.isLittleO_ofReal_left.mpr
  apply Complex.isLittleO_ofReal_right.mpr
  exact hreal

private theorem sdp_offset_remainder_littleO_zero_kappa
    (hκ : 3 - 6 * (g (-1)) ^ 2 - f 0 = 0) :
    (fun t : ℝ => sdpOffset f g t -
      (((f 0 - 3 : ℝ) / 2 : ℝ) : ℂ) -
      ((((2 * (g (-1)) ^ 2 : ℝ) : ℂ) * Complex.I) * (t : ℂ)))
      =o[𝓝[>] (0 : ℝ)]
        (fun t : ℝ => ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ)) := by
  have hcoef : -(2 * (g (-1)) ^ 2 +
      (-3 - 2 * (g (-1)) ^ 2 + f 0) / 2) = 2 * (g (-1)) ^ 2 := by
    linarith [hκ]
  have hO := sdpOffset_second_order_remainder f g
  have hO' : (fun t : ℝ => sdpOffset f g t -
      (((f 0 - 3 : ℝ) / 2 : ℝ) : ℂ) -
      ((((2 * (g (-1)) ^ 2 : ℝ) : ℂ) * Complex.I) * (t : ℂ)))
      =O[𝓝 (0 : ℝ)] (fun t : ℝ => ((t ^ 2 : ℝ) : ℂ)) := by
    have heq : (fun t : ℝ => sdpOffset f g t -
        (((f 0 - 3 : ℝ) / 2 : ℝ) : ℂ) -
        ((((2 * (g (-1)) ^ 2 : ℝ) : ℂ) * Complex.I) * (t : ℂ))) =
      (fun t : ℝ => sdpOffset f g t -
        (((f 0 - 3 : ℝ) / 2 : ℝ) : ℂ) -
        (((-(2 * (g (-1)) ^ 2 +
          (-3 - 2 * (g (-1)) ^ 2 + f 0) / 2) : ℝ) : ℂ) *
          (t : ℂ) * Complex.I)) := by
      funext t
      rw [hcoef]
      push_cast
      ring
    simpa only [heq] using hO
  exact (hO'.mono nhdsWithin_le_nhds).trans_isLittleO
    sdp_tsq_isLittleO_tpow_four_thirds

private theorem sdpQuadraticRootMinus_star (t : ℝ) :
    star (sdpQuadraticRootMinus f t) = sdpQuadraticRootPlus f t := by
  simp [sdpQuadraticRootMinus, sdpQuadraticRootPlus]

private theorem sdp_bad_branch_positive_characteristic_limit
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
    (hf0 : f 0 < 1)
    (hκ : 3 - 6 * (g (-1)) ^ 2 - f 0 = 0)
    (δ : ℝ) (hδ : 0 < δ)
    (hminus : ∀ t : ℝ, 0 < t → t < δ →
      sdpHat f g t = sdpQuadraticRootMinus f t) :
    let X : {k : ℤ // k ≤ -1} → ℕ := fun k => (-k.val).toNat
    let C : ℝ := 2 / (1 - f 0)
    let c₁ : ℝ := C * (2 * (g (-1)) ^ 2)
    let dPlus : ℂ := ((-1 : ℂ) + (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2
    let c₂ : ℂ := (C : ℂ) * dPlus *
      (((g (-1)) ^ (2 / 3 : ℝ) : ℝ) : ℂ)
    Tendsto (fun t : ℝ =>
      ((∫ k : {k : ℤ // k ≤ -1},
          Complex.exp ((((t * (X k : ℝ) : ℝ) : ℂ) * Complex.I))
            ∂sdpNegativeSideLaw f) - 1 -
        ((c₁ : ℂ) * Complex.I) * (t : ℂ)) /
        ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 c₂) := by
  dsimp only
  let α : ℝ := 4 / 3
  let ε : ℝ → ℂ := fun t => ((t ^ α : ℝ) : ℂ)
  let q : ℝ := (g (-1)) ^ 2
  let b : ℝ := (g (-1)) ^ (2 / 3 : ℝ)
  let C : ℝ := 2 / (1 - f 0)
  let c₁ : ℝ := C * (2 * q)
  let dPlus : ℂ := ((-1 : ℂ) + (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2
  let c₂ : ℂ := (C : ℂ) * dPlus * (b : ℂ)
  let X : {k : ℤ // k ≤ -1} → ℕ := fun k => (-k.val).toNat
  let Roff : ℝ → ℂ := fun t => sdpOffset f g t -
    (((f 0 - 3 : ℝ) / 2 : ℝ) : ℂ) -
    ((((2 * q : ℝ) : ℂ) * Complex.I) * (t : ℂ))
  have hroots := sdp_zero_kappa_root_limits
    hf hfs hg hgs hsymm hgsupp hrec hκ
  have hhat : Tendsto (fun t : ℝ => (star (sdpHat f g t) + 1) / ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 (dPlus * (b : ℂ))) := by
    apply hroots.2.congr'
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
    rw [hminus t ht.1 ht.2, sdpQuadraticRootMinus_star]
  have hrem : Tendsto (fun t : ℝ => Roff t / ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hLittle := sdp_offset_remainder_littleO_zero_kappa (g := g) hκ
    have h := hLittle.tendsto_div_nhds_zero
    simpa only [Roff, ε, α, q] using h
  have hremStar : Tendsto (fun t : ℝ => star (Roff t / ε t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (continuous_star.continuousAt (x := (0 : ℂ))).tendsto.comp hrem
    simpa [Function.comp_def] using h
  have hlim : Tendsto (fun t : ℝ => (C : ℂ) *
      ((star (sdpHat f g t) + 1) / ε t - star (Roff t / ε t)))
      (𝓝[>] (0 : ℝ)) (𝓝 c₂) := by
    have h := hhat.sub hremStar
    have hmul := h.const_mul (C : ℂ)
    convert hmul using 1; simp only [c₂, C, dPlus, b, sub_zero]; ring_nf
  have hden : 0 < 1 - f 0 := by linarith
  have hC0 : (C : ℂ) * ((((1 - f 0) / 2 : ℝ) : ℂ)) = 1 := by
    dsimp [C]
    push_cast
    have hdenC : (1 - (f 0 : ℂ)) ≠ 0 := by
      exact_mod_cast (ne_of_gt hden)
    field_simp [hdenC]
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := Set.mem_Ioi.mp ht
  have hε : ε t ≠ 0 := by
    dsimp [ε, α]
    exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos htpos _).ne'
  have hchar := sdpNegativeSideLaw_characteristic f hf hf0 t
  have hchar' : (∫ k : {k : ℤ // k ≤ -1},
      Complex.exp ((((t * (X k : ℝ) : ℝ) : ℂ) * Complex.I))
        ∂sdpNegativeSideLaw f) = (C : ℂ) * negativeCF f (-t) := by
    simpa only [C, X] using hchar
  have hnegative : negativeCF f t = sdpHat f g t - sdpOffset f g t := by
    rw [sdpHat]
    ring
  have hroff : sdpOffset f g t =
      (((f 0 - 3 : ℝ) / 2 : ℝ) : ℂ) +
        ((((2 * q : ℝ) : ℂ) * Complex.I) * (t : ℂ)) + Roff t := by
    dsimp [Roff]
    ring
  have hstarOffset : star (sdpOffset f g t) =
      (((f 0 - 3 : ℝ) / 2 : ℝ) : ℂ) -
        ((((2 * q : ℝ) : ℂ) * Complex.I) * (t : ℂ)) + star (Roff t) := by
    rw [hroff, star_add, star_add, star_mul, star_mul]
    simp only [Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hstarRoffQ : star (Roff t / ε t) = star (Roff t) / ε t := by
    rw [star_div₀]
    simp [ε, α]
  rw [hchar', sdpNegativeCF_neg, hnegative, star_sub,
    hstarOffset, hstarRoffQ]
  have hconst : -(C : ℂ) * (((f 0 - 3 : ℝ) / 2 : ℝ) : ℂ) - 1 = (C : ℂ) := by
    have hsum : (((f 0 - 3 : ℝ) / 2 : ℝ) : ℂ) =
        -1 - (((1 - f 0 : ℝ) / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hsum]
    calc
      -(C : ℂ) * (-1 - (((1 - f 0 : ℝ) / 2 : ℝ) : ℂ)) - 1 =
          (C : ℂ) + (C : ℂ) * (((1 - f 0 : ℝ) / 2 : ℝ) : ℂ) - 1 := by ring
      _ = (C : ℂ) := by rw [hC0]; ring
  field_simp [hε]
  dsimp [ε, α] at *
  have hε' : ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    simpa only [ε, α] using hε
  field_simp [hε']
  dsimp [C, c₁, q] at *
  have hdenC : (1 - (f 0 : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt hden)
  field_simp [hdenC] at hconst ⊢
  push_cast at hconst ⊢
  linear_combination (-1 : ℂ) * hconst


private theorem sdp_selection_littleO_star {F : ℝ → ℂ} {G : ℝ → ℝ} {l : Filter ℝ}
    (h : F =o[l] G) : (fun t => star (F t)) =o[l] G := by
  rw [isLittleO_iff] at h ⊢
  intro ε hε
  filter_upwards [h (c := ε) hε] with t ht
  simpa only [norm_star] using ht

private theorem sdp_selection_extend_conjugate {φ : ℝ → ℂ} {c : ℂ} {ν : ℝ}
    (hpos : (fun t : ℝ => φ t - 1 - c * (((t ^ ν : ℝ) : ℂ))) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ ν))
    (hconj : ∀ t : ℝ, φ (-t) = star (φ t)) :
    (fun t : ℝ => φ t - 1 -
      (if 0 < t then c else star c) * (((|t| ^ ν : ℝ) : ℂ))
      ) =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν) := by
  have hpos' : (fun t : ℝ => φ t - 1 -
      (if 0 < t then c else star c) * (((|t| ^ ν : ℝ) : ℂ)) ) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => (|t| : ℝ) ^ ν) := by
    apply hpos.congr'
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have htp : 0 < t := Set.mem_Ioi.mp ht
      simp [htp, abs_of_pos htp]
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact congrArg (fun r : ℝ => r ^ ν) (abs_of_pos (Set.mem_Ioi.mp ht)).symm
  have hnegMap : Tendsto (fun t : ℝ => -t) (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    have hcont : Tendsto (fun t : ℝ => -t) (𝓝[<] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa only [neg_zero] using
        ((continuous_neg.continuousAt (x := (0 : ℝ))).tendsto.mono_left
          nhdsWithin_le_nhds)
    refine ⟨hcont, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact neg_pos.mpr (Set.mem_Iio.mp ht)
  have hnegComp := hpos.comp_tendsto hnegMap
  have hnegStar : (fun t : ℝ => star
      ((φ (-t) - 1 - c * ((((-t) ^ ν : ℝ) : ℂ)))) ) =o[𝓝[<] (0 : ℝ)]
      (fun t : ℝ => ((-t) ^ ν)) := sdp_selection_littleO_star hnegComp
  have hneg : (fun t : ℝ => φ t - 1 -
      (if 0 < t then c else star c) * (((|t| ^ ν : ℝ) : ℂ))) =o[𝓝[<] (0 : ℝ)]
      (fun t : ℝ => (|t| : ℝ) ^ ν) := by
    apply hnegStar.congr'
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have htn : t < 0 := Set.mem_Iio.mp ht
      have hsym' : φ t = star (φ (-t)) := by
        simpa only [neg_neg] using hconj (-t)
      calc
        star (φ (-t) - 1 - c * ((((-t) ^ ν : ℝ) : ℂ))) =
            star (φ (-t)) - 1 - (star c) * (((|t| ^ ν : ℝ) : ℂ)) := by
              simp [abs_of_neg htn]
        _ = φ t - 1 - (star c) * (((|t| ^ ν : ℝ) : ℂ)) := by rw [← hsym']
        _ = φ t - 1 - (if 0 < t then c else star c) *
              (((|t| ^ ν : ℝ) : ℂ)) := by simp [not_lt.mpr htn.le]
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [abs_of_neg (Set.mem_Iio.mp ht)]
  have hfilter : 𝓝[<] (0 : ℝ) ⊔ 𝓝[>] (0 : ℝ) = 𝓝[≠] (0 : ℝ) := by
    rw [← nhdsWithin_union]
    congr 1
    ext t
    simp
  rw [← hfilter]
  exact hneg.sup hpos'

private theorem sdp_selection_extend_conjugate_linear {φ : ℝ → ℂ} {c : ℂ}
    {c₁ ν : ℝ}
    (hpos : (fun t : ℝ => φ t - 1 - ((c₁ : ℂ) * Complex.I) * (t : ℂ) -
      c * (((t ^ ν : ℝ) : ℂ))) =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ ν))
    (hconj : ∀ t : ℝ, φ (-t) = star (φ t)) :
    (fun t : ℝ => φ t - 1 - ((c₁ : ℂ) * Complex.I) * (t : ℂ) -
      (if 0 < t then c else star c) * (((|t| ^ ν : ℝ) : ℂ))) =o[𝓝[≠] (0 : ℝ)]
      (fun t : ℝ => (|t| : ℝ) ^ ν) := by
  let ψ : ℝ → ℂ := fun t => φ t - ((c₁ : ℂ) * Complex.I) * (t : ℂ)
  have hposψ : (fun t : ℝ => ψ t - 1 - c * (((t ^ ν : ℝ) : ℂ))) =o[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ ν) := by
    convert hpos using 1
    funext t
    dsimp [ψ]
    ring
  have hconjψ (t : ℝ) : ψ (-t) = star (ψ t) := by
    dsimp [ψ]
    rw [hconj t]
    simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
    simp only [Complex.star_def]
    ring
  have hout := sdp_selection_extend_conjugate hposψ hconjψ
  convert hout using 1
  funext t
  dsimp [ψ]
  ring


private theorem sdp_selection_remainder_of_limit
    (F : ℝ → ℂ) (c₀ c : ℂ) (α : ℝ)
    (h : Tendsto (fun t : ℝ => (F t - c₀) /
      ((t ^ α : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 c)) :
    (fun t : ℝ => F t - c₀ - c * ((t ^ α : ℝ) : ℂ))
      =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ α) := by
  let ε : ℝ → ℂ := fun t => ((t ^ α : ℝ) : ℂ)
  have hεne : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ε t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (Set.mem_Ioi.mp ht) _).ne'
  have hratio : Tendsto (fun t : ℝ =>
      (F t - c₀ - c * ε t) / ε t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h' := h.sub_const c
    have h'' : Tendsto (fun t : ℝ => (F t - c₀) / ε t - c)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa [ε] using h'
    apply h''.congr'
    filter_upwards [hεne] with t ht
    field_simp [ε, ht]
  have hden : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      ((t ^ α : ℝ) : ℂ) = 0 →
        F t - c₀ - c * ((t ^ α : ℝ) : ℂ) = 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht hz
    have hpos : 0 < t := Set.mem_Ioi.mp ht
    have hne : ((t ^ α : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hpos α).ne'
    exact False.elim (hne hz)
  have hlittle := (isLittleO_iff_tendsto' hden).2 hratio
  rw [isLittleO_iff] at hlittle ⊢
  intro C hC
  filter_upwards [self_mem_nhdsWithin, hlittle hC] with t ht hbound
  have htpos : 0 < t := Set.mem_Ioi.mp ht
  simpa [ε, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt htpos) _)] using hbound


/-- The upper-imaginary SDP root is selected when κ vanishes, by the
Tauberian sign clause for the normalized conjugate of `F⁻`. -/
theorem sdp_kappa_zero_select_plus_of_master
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
    (hκ : 3 - 6 * (g (-1)) ^ 2 - f 0 = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      sdpHat f g t = sdpQuadraticRootPlus f t := by
  obtain ⟨hf0, hgpos⟩ := sdp_side_nondegenerate_of_master
    hf hfs hg hgs hsymm hgsupp hrec
  obtain ⟨δ, hδ, hplus | hminus⟩ := sdp_side_branch_constancy_of_master
    hf hfs hg hgs hsymm hgsupp hrec
  · exact ⟨δ, hδ, hplus⟩
  · exfalso
    let X : {k : ℤ // k ≤ -1} → ℕ := fun k => (-k.val).toNat
    let μ := sdpNegativeSideLaw f
    have : IsProbabilityMeasure μ := sdpNegativeSideLaw_isProbability hf hfs hsymm hf0
    let C : ℝ := 2 / (1 - f 0)
    let c₁ : ℝ := C * (2 * (g (-1)) ^ 2)
    let b : ℝ := (g (-1)) ^ (2 / 3 : ℝ)
    let c₂ : ℂ := (C : ℂ) *
      (((-1 : ℂ) + (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2) * (b : ℂ)
    let φ : ℝ → ℂ := fun t => ∫ k, Complex.exp
      ((((t * (X k : ℝ) : ℝ) : ℂ) * Complex.I)) ∂μ
    have hC : 0 < C := div_pos (by norm_num) (sub_pos.mpr hf0)
    have hc₁ : 0 < c₁ := mul_pos hC (mul_pos (by norm_num) (sq_pos_of_pos hgpos))
    have hb : 0 < b := Real.rpow_pos_of_pos hgpos _
    have hc₂ : 0 < c₂.im := by
      have him : c₂.im = C * (Real.sqrt 3 / 2) * b := by
        dsimp [c₂]
        simp [Complex.mul_im, Complex.mul_re]
      rw [him]
      exact mul_pos (mul_pos hC (div_pos (Real.sqrt_pos.mpr (by norm_num))
        (by norm_num))) hb
    have hlim : Tendsto (fun t : ℝ =>
        (φ t - 1 - ((c₁ : ℂ) * Complex.I) * (t : ℂ)) /
          ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 c₂) :=
      sdp_bad_branch_positive_characteristic_limit
        hf hfs hg hgs hsymm hgsupp hrec hf0 hκ δ hδ hminus
    have hpos := sdp_selection_remainder_of_limit
      (fun t => φ t - ((c₁ : ℂ) * Complex.I) * (t : ℂ)) 1 c₂ (4 / 3) (by
        convert hlim using 1
        funext t
        congr 1
        ring)
    have hconj (t : ℝ) : φ (-t) = star (φ t) := by
      have hchar (u : ℝ) : φ u = (C : ℂ) * negativeCF f (-u) :=
        sdpNegativeSideLaw_characteristic f hf hf0 u
      rw [hchar, hchar, neg_neg, sdpNegativeCF_neg, star_mul, star_star]
      simp [mul_comm]
    have hpos' : (fun t : ℝ => φ t - 1 - ((c₁ : ℂ) * Complex.I) * (t : ℂ) -
        c₂ * ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ)) =o[𝓝[>] (0 : ℝ)]
        (fun t : ℝ => t ^ (4 / 3 : ℝ)) := by
      convert hpos using 1
      funext t
      ring
    have hexp := sdp_selection_extend_conjugate_linear hpos' hconj
    have hexp' : (fun t : ℝ => φ t - 1 - (c₁ : ℂ) * Complex.I * (t : ℂ) -
        (if 0 < t then c₂ else starRingEnd ℂ c₂) *
          (((|t| : ℝ) ^ (1 + (1 / 3 : ℝ)) : ℝ) : ℂ))
        =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ (1 + (1 / 3 : ℝ))) := by
      norm_num at *
      exact hexp
    have hsign := (DirectedDistances.Paper.Section6.tauberian_characteristic
      ({k : ℤ // k ≤ -1}) μ X (measurable_of_countable X)).2
        c₁ hc₁ c₂ hc₂.ne' (1 / 3) (by norm_num) (by norm_num) hexp'
    exact (not_lt_of_gt hc₂) hsign.1


namespace SelectionSummation

private noncomputable def cfPhase (t : ℝ) (k : ℤ) : ℂ :=
  Complex.exp (((t * (k : ℝ) : ℝ) : ℂ) * Complex.I)

private theorem cfPhase_add (t : ℝ) (a b : ℤ) :
    cfPhase t (a + b) = cfPhase t a * cfPhase t b := by
  unfold cfPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem cfPhase_norm (t : ℝ) (k : ℤ) : ‖cfPhase t k‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem cfPhase_zero_left (k : ℤ) : cfPhase 0 k = 1 := by
  simp [cfPhase]

private theorem cfPhase_zero_right (t : ℝ) : cfPhase t 0 = 1 := by
  simp [cfPhase]

private theorem cfPhase_neg (t : ℝ) (k : ℤ) : cfPhase t (-k) = cfPhase (-t) k := by
  unfold cfPhase
  congr 1
  push_cast
  ring

private theorem cfPhase_neg_neg (t : ℝ) (k : ℤ) : cfPhase (-t) (-k) = cfPhase t k := by
  rw [cfPhase_neg, neg_neg]

/-- `HasSum` form of the characteristic series `integerCF` -/
private theorem hasSum_cf {p : ℤ → ℝ} (hp : ∀ k, 0 ≤ p k) (hs : Summable p) (t : ℝ) :
    HasSum (fun k : ℤ => (p k : ℂ) * cfPhase t k) (integerCF p t) := by
  have h : Summable (fun k : ℤ => (p k : ℂ) * cfPhase t k) := by
    refine Summable.of_norm_bounded hs fun k => ?_
    rw [norm_mul, cfPhase_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg (hp k)]
  exact h.hasSum

/-- `HasSum` form of the negative-index series `negativeCF`, indexed by `n ↦ -(n+1)` -/
private theorem hasSum_negativeCF {p : ℤ → ℝ} (hp : ∀ k, 0 ≤ p k) (hs : Summable p) (t : ℝ) :
    HasSum (fun n : ℕ => (p (-((n : ℤ) + 1)) : ℂ) * cfPhase t (-((n : ℤ) + 1)))
      (negativeCF p t) := by
  have hsum := hasSum_cf hp hs t
  set h : ℤ → ℂ := fun k => (p k : ℂ) * cfPhase t k with hh
  have hinj : Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) := by
    intro a b hab
    simp only [neg_inj, add_left_inj, Nat.cast_inj] at hab
    exact hab
  have hzero : ∀ k, k ∉ Set.range (fun n : ℕ => -((n : ℤ) + 1)) →
      ({k : ℤ | k ≤ -1}.indicator h) k = 0 := by
    intro k hk
    rw [Set.indicator_apply]
    split_ifs with hk'
    · exfalso
      apply hk
      refine ⟨(-k - 1).toNat, ?_⟩
      have hk'' : k ≤ -1 := hk'
      dsimp only
      omega
    · rfl
  have hind : HasSum ({k : ℤ | k ≤ -1}.indicator h) (negativeCF p t) := by
    have hsub : negativeCF p t = ∑' k : ℤ, {k : ℤ | k ≤ -1}.indicator h k :=
      tsum_subtype ({k : ℤ | k ≤ -1}) h
    rw [hsub]
    exact (hsum.summable.indicator _).hasSum
  have key := (hinj.hasSum_iff hzero).2 hind
  convert key using 1
  funext n
  have hm : (-((n : ℤ) + 1)) ∈ {k : ℤ | k ≤ -1} := by
    show -((n : ℤ) + 1) ≤ -1
    omega
  simp only [Function.comp_apply, Set.indicator_apply, hh]
  simp only [hm, ↓reduceIte]

/-- Symmetric splitting `F = f(0) + F⁻(t) + F⁻(-t)` used for -/
private theorem integerCF_eq_split {p : ℤ → ℝ} (hp : ∀ k, 0 ≤ p k) (hs : Summable p)
    (hsymm : ∀ k, p (-k) = p k) (t : ℝ) :
    integerCF p t = (p 0 : ℂ) + negativeCF p t + negativeCF p (-t) := by
  have hc := hasSum_cf hp hs t
  have h1 : Summable (fun n : ℕ => (p n : ℂ) * cfPhase t n) :=
    hc.summable.comp_injective Nat.cast_injective
  have hneg := hasSum_negativeCF hp hs t
  have h2 := hneg.summable
  have e1 : integerCF p t =
      (∑' n : ℕ, (p n : ℂ) * cfPhase t n) +
        ∑' n : ℕ, (p (-((n : ℤ) + 1)) : ℂ) * cfPhase t (-((n : ℤ) + 1)) :=
    tsum_of_nat_of_neg_add_one (f := fun k : ℤ => (p k : ℂ) * cfPhase t k) h1 h2
  have e2 := h1.tsum_eq_zero_add
  have e3 := (hasSum_negativeCF hp hs (-t)).tsum_eq
  have e4 : ∀ n : ℕ, (p (-((n : ℤ) + 1)) : ℂ) * cfPhase (-t) (-((n : ℤ) + 1)) =
      (p ((n + 1 : ℕ) : ℤ) : ℂ) * cfPhase t ((n + 1 : ℕ) : ℤ) := by
    intro n
    rw [cfPhase_neg_neg]
    have : (-((n : ℤ) + 1)) = -(((n + 1 : ℕ)) : ℤ) := by push_cast; ring
    rw [this, hsymm]
    push_cast
    ring_nf
  simp only [e4] at e3
  rw [e1, e2, e3, hneg.tsum_eq]
  simp [cfPhase_zero_right]
  ring

/-- `F(0) = 1`. -/
private theorem integerCF_zero {p : ℤ → ℝ} (hp : ∀ k, 0 ≤ p k) (hps : HasSum p 1) :
    integerCF p 0 = 1 := by
  have h1 := hasSum_cf hp hps.summable 0
  have h2 : HasSum (fun k : ℤ => (p k : ℂ)) 1 := by
    have := Complex.hasSum_ofReal.2 hps
    simpa using this
  simp only [cfPhase_zero_left, mul_one] at h1
  exact h1.unique h2

/-- `F⁻(0) = (1 - f(0))/2`, used in `eq:first-sub`, -/
private theorem negativeCF_zero {p : ℤ → ℝ} (hp : ∀ k, 0 ≤ p k) (hps : HasSum p 1)
    (hsymm : ∀ k, p (-k) = p k) :
    negativeCF p 0 = (((1 - p 0) / 2 : ℝ) : ℂ) := by
  have h := integerCF_eq_split hp hps.summable hsymm 0
  rw [integerCF_zero hp hps, neg_zero] at h
  push_cast
  linear_combination (-1 / 2 : ℂ) * h

private theorem hasSum_negative_indicator {p : ℤ → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hs : Summable p) (t : ℝ) :
    HasSum (fun k : ℤ => if k ≤ -1 then (p k : ℂ) * cfPhase t k else 0)
      (negativeCF p t) := by
  have hc := hasSum_cf hp hs t
  have ht : negativeCF p t = ∑' k : ℤ,
      {k : ℤ | k ≤ -1}.indicator (fun k => (p k : ℂ) * cfPhase t k) k :=
    by
      change (∑' k : {k : ℤ // k ≤ -1}, (p k : ℂ) * cfPhase t k) = _
      exact tsum_subtype {k : ℤ | k ≤ -1} (fun k : ℤ => (p k : ℂ) * cfPhase t k)
  rw [ht]
  convert (hc.summable.indicator {k : ℤ | k ≤ -1}).hasSum using 1
  funext k
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]

private theorem norm_summable_cf {p : ℤ → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hs : Summable p) (t : ℝ) :
    Summable (fun k : ℤ => ‖(p k : ℂ) * cfPhase t k‖) := by
  convert hs using 1
  funext k
  rw [norm_mul, cfPhase_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg (hp k)]

private theorem hasSum_phase_conv {a b : ℤ → ℝ}
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (has : Summable a) (hbs : Summable b) (t : ℝ) (d : ℤ) :
    HasSum (fun y : ℤ => cfPhase t y *
      ((∑' j : ℤ, a j * b (y - j - d) : ℝ) : ℂ))
      (cfPhase t d * integerCF a t * integerCF b t) := by
  let u : ℤ → ℂ := fun k => (a k : ℂ) * cfPhase t k
  let v : ℤ → ℂ := fun k => (b k : ℂ) * cfPhase t k
  have hu := norm_summable_cf ha has t
  have hv := norm_summable_cf hb hbs t
  have hp : HasSum (fun q : ℤ × ℤ => u q.1 * v q.2)
      (integerCF a t * integerCF b t) := by
    have hsm := summable_mul_of_summable_norm hu hv
    have heq := tsum_mul_tsum_of_summable_norm hu hv
    exact heq ▸ hsm.hasSum
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    ⟨fun q => (q.2, q.1 - q.2 - d), fun q => (q.1 + q.2 + d, q.1),
      fun q => by dsimp; ext <;> ring,
      fun q => by dsimp; ext <;> ring⟩
  have hp' := (e.hasSum_iff.2 hp).mul_left (cfPhase t d)
  have hsum := hp'.prod_fiberwise (fun y => (hp'.summable.prod_factor y).hasSum)
  have hvv : cfPhase t d * (integerCF a t * integerCF b t) =
      cfPhase t d * integerCF a t * integerCF b t := (mul_assoc _ _ _).symm
  rw [hvv] at hsum
  convert hsum using 1
  funext y
  rw [Complex.ofReal_tsum, ← tsum_mul_left]
  apply tsum_congr
  intro j
  change cfPhase t y * ((a j * b (y - j - d) : ℝ) : ℂ) =
    cfPhase t d * (u j * v (y - j - d))
  have he : cfPhase t y = cfPhase t d * cfPhase t j * cfPhase t (y - j - d) := by
    rw [← cfPhase_add, ← cfPhase_add]
    congr 1
    ring
  rw [he]
  dsimp [u, v]
  push_cast
  ring

private theorem hasSum_phase_shift {p : ℤ → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hs : Summable p) (t : ℝ) (d : ℤ) :
    HasSum (fun x : ℤ => cfPhase t x * (p (x - d) : ℂ))
      (cfPhase t d * integerCF p t) := by
  have h := (Equiv.addRight (-d)).hasSum_iff.2 (hasSum_cf hp hs t)
  convert h.mul_left (cfPhase t d) using 1
  funext x
  simp only [Function.comp_apply, Equiv.coe_addRight]
  have he : cfPhase t x = cfPhase t d * cfPhase t (x - d) := by
    rw [← cfPhase_add]
    congr 1
    ring
  rw [he]
  simp only [sub_eq_add_neg]
  ring

private theorem hasSum_tail_pairs {f : ℤ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hfs : HasSum f 1) (t : ℝ) :
    HasSum (fun x : ℤ => cfPhase t x *
      ((∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1) : ℝ) : ℂ))
      (integerCF f t * (cfPhase t 1 * negativeCF f t - (f (-1) : ℂ))) := by
  let a : ℤ → ℝ := {j : ℤ | j ≤ -2}.indicator f
  have ha : ∀ j, 0 ≤ a j := by
    intro j
    dsimp [a, Set.indicator]
    split_ifs
    · exact hf j
    · exact le_rfl
  have has : Summable a := hfs.summable.indicator _
  have hA : integerCF a t = negativeCF f t - (f (-1) : ℂ) * cfPhase t (-1) := by
    have hn := hasSum_negative_indicator hf hfs.summable t
    have hi := hasSum_ite_eq (-1 : ℤ) ((f (-1) : ℂ) * cfPhase t (-1))
    have hh := hn.sub hi
    have he : (fun j : ℤ =>
        (if j ≤ -1 then (f j : ℂ) * cfPhase t j else 0) -
        (if j = -1 then (f (-1) : ℂ) * cfPhase t (-1) else 0)) =
        (fun j => (a j : ℂ) * cfPhase t j) := by
      funext j
      by_cases hj : j ≤ -2
      · have hj' : j ≤ -1 := by omega
        have hjn : j ≠ -1 := by omega
        simp [a, hj, hj', hjn]
      · by_cases hj1 : j = -1
        · subst j; simp [a]
        · have hj' : ¬ j ≤ -1 := by omega
          simp [a, hj, hj', hj1]
    rw [he] at hh
    exact (hasSum_cf ha has t).unique hh
  have hc := hasSum_phase_conv ha hf has hfs.summable t 1
  have hphase : cfPhase t 1 * cfPhase t (-1) = 1 := by
    rw [← cfPhase_add]; norm_num [cfPhase_zero_right]
  have hval : cfPhase t 1 * integerCF a t * integerCF f t =
      integerCF f t * (cfPhase t 1 * negativeCF f t - (f (-1) : ℂ)) := by
    rw [hA]
    linear_combination -(integerCF f t) * (f (-1) : ℂ) * hphase
  rw [hval] at hc
  convert hc using 1
  funext x
  congr 2
  refine (tsum_subtype {j : ℤ | j ≤ -2} (fun j : ℤ => f j * f (x - j - 1))).trans ?_
  apply tsum_congr
  intro j
  by_cases hj : j ≤ -2 <;> simp [a, Set.indicator, hj]

private theorem sdp_fiber_identity {f g : ℤ → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f 1)
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g 1)
    (hrec : ∀ x y : ℤ, -1 ≤ y →
      3 * f x * g y =
        f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j)) +
        (if y = -1 then
          (∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
            (g (-1)) ^ 2 * f (x + 1) + g (x - 1)
         else 0))
    (t : ℝ) (y : ℤ) (hy : -1 ≤ y) :
    3 * integerCF f t * (g y : ℂ) =
      integerCF f t * ((f y : ℂ) +
        ((∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j) : ℝ) : ℂ)) +
      (if y = -1 then
        integerCF f t * (cfPhase t 1 * negativeCF f t - (f (-1) : ℂ)) +
        (g (-1) : ℂ) ^ 2 * cfPhase t (-1) * integerCF f t +
        cfPhase t 1 * integerCF g t else 0) := by
  let V : ℂ := integerCF f t * (cfPhase t 1 * negativeCF f t - (f (-1) : ℂ)) +
        (g (-1) : ℂ) ^ 2 * cfPhase t (-1) * integerCF f t +
        cfPhase t 1 * integerCF g t
  have htail := hasSum_tail_pairs hf hfs t
  have hshift := (hasSum_phase_shift hf hfs.summable t (-1)).mul_left ((g (-1) : ℂ) ^ 2)
  have hgshift := hasSum_phase_shift hg hgs.summable t 1
  have hV : HasSum (fun x : ℤ => cfPhase t x *
      (((∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
        (g (-1)) ^ 2 * f (x + 1) + g (x - 1) : ℝ) : ℂ)) V := by
    convert (htail.add hshift).add hgshift using 1
    · funext x
      simp only [sub_neg_eq_add]
      push_cast
      ring
    · dsimp [V]; ring
  have hExtra : HasSum (fun x : ℤ => cfPhase t x *
      ((if y = -1 then
        (∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
        (g (-1)) ^ 2 * f (x + 1) + g (x - 1) else 0 : ℝ) : ℂ))
      (if y = -1 then V else 0) := by
    by_cases hy1 : y = -1
    · simpa only [hy1, ↓reduceIte] using hV
    · simp [hy1]
  have hF := hasSum_cf hf hfs.summable t
  have hL := hF.mul_left (3 * (g y : ℂ))
  have hR := (hF.mul_right
    (((f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j) : ℝ) : ℂ))).add hExtra
  have he : (fun x : ℤ => 3 * (g y : ℂ) * ((f x : ℂ) * cfPhase t x)) =
      (fun x : ℤ => (f x : ℂ) * cfPhase t x *
        ((f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j) : ℝ) : ℂ) +
      cfPhase t x * ((if y = -1 then
        (∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
        (g (-1)) ^ 2 * f (x + 1) + g (x - 1) else 0 : ℝ) : ℂ)) := by
    funext x
    have hr := congrArg (fun r : ℝ => (r : ℂ)) (hrec x y hy)
    push_cast at hr ⊢
    linear_combination cfPhase t x * hr
  rw [he] at hL
  have hh := hL.unique hR
  dsimp [V] at hh
  push_cast at hh ⊢
  linear_combination hh

private theorem cfPhase_one (t : ℝ) : cfPhase t 1 = Complex.exp ((t : ℂ) * Complex.I) := by
  simp [cfPhase]

private theorem sdpOffset_phase (f g : ℤ → ℝ) (t : ℝ) :
    sdpOffset f g t = (g (-1) : ℂ) ^ 2 * cfPhase t (-2) +
      (((-3 - 2 * (g (-1)) ^ 2 + f 0) / 2 : ℝ) : ℂ) * cfPhase t (-1) := by
  have h2 : Complex.exp (((2 * t : ℝ) : ℂ) * Complex.I) = cfPhase t 2 := by
    unfold cfPhase
    congr 1
    push_cast
    ring
  have hm2 : cfPhase t (-2) * cfPhase t 2 = 1 := by
    rw [← cfPhase_add]; norm_num [cfPhase_zero_right]
  have hm1 : cfPhase t (-1) * cfPhase t 2 = cfPhase t 1 := by
    rw [← cfPhase_add]; norm_num
  unfold sdpOffset
  rw [h2, ← cfPhase_one]
  have hne : cfPhase t 2 ≠ 0 := Complex.exp_ne_zero _
  apply (div_eq_iff (mul_ne_zero (by norm_num) hne)).2
  symm
  rw [add_mul]
  push_cast
  calc
    _ = 2 * (g (-1) : ℂ) ^ 2 * (cfPhase t (-2) * cfPhase t 2) +
      ((-3 - 2 * (g (-1) : ℂ) ^ 2 + (f 0 : ℂ))) *
        (cfPhase t (-1) * cfPhase t 2) := by ring
    _ = _ := by rw [hm2, hm1]; ring


private theorem G_identity
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x)
    (hrec : ∀ x y : ℤ, -1 ≤ y →
      3 * f x * g y =
        f x * (f y + ∑ j ∈ Finset.Icc (-1 : ℤ) (y + 1), g j * g (y - j)) +
        (if y = -1 then
          (∑' j : {j : ℤ // j ≤ -2}, f j * f (x - (j : ℤ) - 1)) +
            (g (-1)) ^ 2 * f (x + 1) + g (x - 1)
         else 0))
    (t : ℝ) : integerCF g t = -integerCF f t * sdpHat f g t := by
  have ht := sdp_fiber_identity hf hfs hg hgs hrec t (-1) (by omega)
  have hz := sdp_fiber_identity hf hfs hg hgs hrec 0 (-1) (by omega)
  rw [integerCF_zero hf hfs, integerCF_zero hg hgs,
    negativeCF_zero hf hfs hsymm] at hz
  simp only [cfPhase_zero_left, one_mul, mul_one, ↓reduceIte] at hz
  simp only [↓reduceIte] at ht
  have hp1 : cfPhase t (-1) * cfPhase t 1 = 1 := by
    rw [← cfPhase_add]
    norm_num [cfPhase_zero_right]
  have hp2 : cfPhase t (-1) * cfPhase t (-1) = cfPhase t (-2) := by
    rw [← cfPhase_add]
    norm_num
  rw [sdpHat, sdpOffset_phase]
  push_cast at hz ht ⊢
  linear_combination -cfPhase t (-1) * ht +
    (cfPhase t (-1) * integerCF f t) * hz -
    (integerCF f t * negativeCF f t + integerCF g t) * hp1 -
    (g (-1) : ℂ) ^ 2 * integerCF f t * hp2

end SelectionSummation

/-- The selected SDP side expansions when κ vanishes: the linear term of
`F⁻` is `-2 i g(-1)^2 t`, its fractional coefficient has positive imaginary
part, and the coefficient of `G` has negative imaginary part. -/
theorem sdp_kappa_zero_side_expansions_of_master
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
    (hκ : 3 - 6 * (g (-1)) ^ 2 - f 0 = 0) :
    let b : ℝ := (g (-1)) ^ (2 / 3 : ℝ)
    let dPlus : ℂ := ((-1 : ℂ) + (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2
    let dMinus : ℂ := ((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2
    (fun t : ℝ => negativeCF f t - (((1 - f 0) / 2 : ℝ) : ℂ) +
      (((2 * (g (-1)) ^ 2 : ℝ) : ℂ) * Complex.I) * (t : ℂ) -
      (dPlus * (b : ℂ)) * ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (4 / 3 : ℝ)) ∧
    (fun t : ℝ => sdpCF g t - 1 -
      (dMinus * (b : ℂ)) * ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (4 / 3 : ℝ)) := by
  dsimp only
  let b : ℝ := (g (-1)) ^ (2 / 3 : ℝ)
  let dPlus : ℂ := ((-1 : ℂ) + (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2
  let dMinus : ℂ := ((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2
  let ε : ℝ → ℂ := fun t => ((t ^ (4 / 3 : ℝ) : ℝ) : ℂ)
  obtain ⟨δ, hδ, hselect⟩ := sdp_kappa_zero_select_plus_of_master
    hf hfs hg hgs hsymm hgsupp hrec hκ
  have hhat : Tendsto (fun t : ℝ => (sdpHat f g t + 1) / ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 (dPlus * (b : ℂ))) := by
    apply (sdp_zero_kappa_root_limits hf hfs hg hgs hsymm hgsupp hrec hκ).2.congr'
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
    rw [hselect t ht.1 ht.2]
  have hhatLittle := sdp_selection_remainder_of_limit
    (sdpHat f g) (-1) (dPlus * (b : ℂ)) (4 / 3) (by simpa only [sub_neg_eq_add] using hhat)
  have hoff := Complex.isLittleO_ofReal_right.mp
    (sdp_offset_remainder_littleO_zero_kappa (g := g) hκ)
  constructor
  · apply (hhatLittle.sub hoff).congr'
    · filter_upwards with t
      rw [sdpHat]
      push_cast
      ring
    · filter_upwards with t
      rfl
  · have hFsmall : (fun t : ℝ => integerCF f t -
        ((1 : ℂ) - (b : ℂ) * ε t)) =o[𝓝[>] (0 : ℝ)] ε := by
      obtain ⟨_, hzero | hpos⟩ := sdp_real_transform_dichotomy_of_master
        hf hfs hg hgs hsymm hgsupp hrec
      · exact hzero.2
      · exfalso
        rw [hκ] at hpos
        exact (lt_irrefl 0) hpos.1
    have hF : Tendsto (fun t : ℝ => (1 - integerCF f t) / ε t)
        (𝓝[>] (0 : ℝ)) (𝓝 (b : ℂ)) := by
      have hz := hFsmall.tendsto_div_nhds_zero
      have hl := (tendsto_const_nhds (x := (b : ℂ))).sub hz
      have hl' : Tendsto (fun t => (b : ℂ) -
          (integerCF f t - (1 - (b : ℂ) * ε t)) / ε t)
          (𝓝[>] (0 : ℝ)) (𝓝 (b : ℂ)) := by simpa only [sub_zero] using hl
      apply hl'.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      have he : ε t ≠ 0 := Complex.ofReal_ne_zero.mpr
        (Real.rpow_pos_of_pos (Set.mem_Ioi.mp ht) _).ne'
      field_simp [he]
      ring
    have hG (t : ℝ) : sdpCF g t = -integerCF f t * sdpHat f g t := by
      have he : sdpCF g t = integerCF g t := by
        unfold sdpCF
        have hind := tsum_subtype {k : ℤ | -1 ≤ k}
          (fun k : ℤ => (g k : ℂ) *
            Complex.exp ((((t * (k : ℝ) : ℝ) : ℂ) * Complex.I)))
        change (∑' k : {k : ℤ // -1 ≤ k}, (g k : ℂ) *
          Complex.exp ((((t * (k : ℝ) : ℝ) : ℂ) * Complex.I))) = _ at hind
        rw [hind]
        unfold integerCF
        apply tsum_congr
        intro k
        by_cases hk : -1 ≤ k
        · simp [hk]
        · simp [hk, hgsupp k (by omega)]
      rw [he]
      exact SelectionSummation.G_identity hf hfs hg hgs hsymm hrec t
    have hGlim := sdpCF_scaled_limit_of_sdpHat_scaled_limit hG
      (by norm_num : (0 : ℝ) < 4 / 3) hF hhat
    have hcoeff : -(b : ℂ) - dPlus * (b : ℂ) = dMinus * (b : ℂ) := by
      dsimp [dPlus, dMinus]
      ring
    rw [hcoeff] at hGlim
    exact sdp_selection_remainder_of_limit (sdpCF g) 1 (dMinus * (b : ℂ))
      (4 / 3) hGlim

end DirectedDistances.Recursive.SDPExpansion
