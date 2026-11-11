/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Recursive.LDPSideExpansions
import DirectedDistances.Paper.Section6.Tauberian
import DirectedDistances.Recursive.LDPNondegenerate
import DirectedDistances.Recursive.LDPQuadraticFromMaster
import DirectedDistances.PaperProofs.Section6.Next.CharacteristicDiscriminant
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # LDP side-transform branch selection

is selected by Proposition 6.1 applied to the reflected law in `eq:Ghat`. -/

public section
namespace DirectedDistances.Recursive

open Filter Asymptotics MeasureTheory
open scoped Topology

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

/-- On the interval where the characteristic discriminant is negative, both
closed-form candidates solve the source quadratic and the actual transform -/
theorem ldp_side_roots_and_actual
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
    :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ((integerCF f t) ^ 2 * (ldpQuadraticRootMinus f t) ^ 2 +
          (3 * integerCF f t - 1) * ldpQuadraticRootMinus f t + integerCF f t = 0) ∧
        ((integerCF f t) ^ 2 * (ldpQuadraticRootPlus f t) ^ 2 +
          (3 * integerCF f t - 1) * ldpQuadraticRootPlus f t + integerCF f t = 0) ∧
        (ldpHat f t = ldpQuadraticRootMinus f t ∨
          ldpHat f t = ldpQuadraticRootPlus f t) := by
  obtain ⟨hf_lt, _⟩ := ldp_pmf_nondegenerate_of_master
    hf hfs hg hgs hsymm hgsupp hrec
  obtain ⟨δ, hδ, hinterval⟩ :=
    DirectedDistances.PaperProofs.Section6.exists_integer_cosine_mass_interval
      hf hfs (hf_lt 0)
  refine ⟨δ, hδ, ?_⟩
  intro t ht htd
  obtain ⟨hcoslo, hcoshi⟩ := hinterval t ht htd
  let F : ℝ := (integerCF f t).re
  have hFcos : F = ∑' k : ℤ, f k * Real.cos (t * (k : ℝ)) := by
    exact integerCF_re hf hfs.summable t
  rw [← hFcos] at hcoslo hcoshi
  have hFim : (integerCF f t).im = 0 := integerCF_im hf hfs.summable hsymm t
  have hFcast : (F : ℂ) = integerCF f t := by
    apply Complex.ext
    · rfl
    · simpa [F, Complex.ofReal_im] using hFim.symm
  have hFreal : integerCF f t = (F : ℂ) := hFcast.symm
  have hFlower : (1 / 4 : ℝ) < F := hcoslo
  have hFupper : F < 1 := hcoshi
  have hFne : F ≠ 0 := ne_of_gt (by linarith)
  have hsqrt : Real.sqrt (4 * F - 1) ^ 2 = 4 * F - 1 := by
    rw [Real.sq_sqrt]
    linarith
  have hsqrt' : Real.sqrt (-1 + F * 4) ^ 2 = -1 + F * 4 := by
    rw [show -1 + F * 4 = 4 * F - 1 by ring]
    exact hsqrt
  have hsqrt'' : Real.sqrt (F * 4 - 1) ^ 2 = F * 4 - 1 := by
    rw [show F * 4 - 1 = 4 * F - 1 by ring]
    exact hsqrt
  let A : ℝ := (1 - F) * (1 - 2 * F) / (2 * F ^ 2)
  let B : ℝ := (1 - F) * Real.sqrt (4 * F - 1) / (2 * F ^ 2)
  have hrootMinusForm : ldpQuadraticRootMinus f t =
      ((-1 + A : ℝ) : ℂ) - (B : ℂ) * Complex.I := by
    simp [ldpQuadraticRootMinus, A, B, F]
  have hrootPlusForm : ldpQuadraticRootPlus f t =
      ((-1 + A : ℝ) : ℂ) + (B : ℂ) * Complex.I := by
    simp [ldpQuadraticRootPlus, A, B, F]
  have hrootSum : ldpQuadraticRootMinus f t + ldpQuadraticRootPlus f t =
      (((1 - 3 * F) / F ^ 2 : ℝ) : ℂ) := by
    rw [hrootMinusForm, hrootPlusForm]
    dsimp [A]
    push_cast
    field_simp [hFne]
    ring
  have hrootProd : ldpQuadraticRootMinus f t * ldpQuadraticRootPlus f t =
      ((1 / F : ℝ) : ℂ) := by
    rw [hrootMinusForm, hrootPlusForm]
    have hcross :
        (((-1 + A : ℝ) : ℂ) - (B : ℂ) * Complex.I) *
          (((-1 + A : ℝ) : ℂ) + (B : ℂ) * Complex.I) =
        (((-1 + A) ^ 2 + B ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring_nf
      simp only [Complex.I_sq]
      ring
    rw [hcross]
    have hrealprod : (-1 + A) ^ 2 + B ^ 2 = 1 / F := by
      dsimp [A, B]
      field_simp [hFne]
      rw [hsqrt'']
      ring
    exact congrArg Complex.ofReal hrealprod
  have hfactor (z : ℂ) :
      (F : ℂ) ^ 2 * z ^ 2 + (3 * (F : ℂ) - 1) * z + (F : ℂ) =
        (F : ℂ) ^ 2 * (z - ldpQuadraticRootMinus f t) *
          (z - ldpQuadraticRootPlus f t) := by
    calc
      (F : ℂ) ^ 2 * z ^ 2 + (3 * (F : ℂ) - 1) * z + (F : ℂ) =
          (F : ℂ) ^ 2 * (z ^ 2 -
            (ldpQuadraticRootMinus f t + ldpQuadraticRootPlus f t) * z +
            ldpQuadraticRootMinus f t * ldpQuadraticRootPlus f t) := by
        rw [hrootSum, hrootProd]
        push_cast
        field_simp [hFne]
        ring
      _ = (F : ℂ) ^ 2 * (z - ldpQuadraticRootMinus f t) *
            (z - ldpQuadraticRootPlus f t) := by ring
  have hrootMinus :
      (integerCF f t) ^ 2 * (ldpQuadraticRootMinus f t) ^ 2 +
        (3 * integerCF f t - 1) * ldpQuadraticRootMinus f t + integerCF f t = 0 := by
    rw [hFreal]
    rw [hfactor]
    simp
  have hrootPlus :
      (integerCF f t) ^ 2 * (ldpQuadraticRootPlus f t) ^ 2 +
        (3 * integerCF f t - 1) * ldpQuadraticRootPlus f t + integerCF f t = 0 := by
    rw [hFreal]
    rw [hfactor]
    simp
  have hactual :
      (integerCF f t) ^ 2 * (ldpHat f t) ^ 2 +
        (3 * integerCF f t - 1) * ldpHat f t + integerCF f t = 0 := hLdpQuad t
  have hactual' :
      (F : ℂ) ^ 2 * (ldpHat f t) ^ 2 +
        (3 * (F : ℂ) - 1) * ldpHat f t + (F : ℂ) = 0 := by
    simpa only [hFreal] using hactual
  have hpair :
      (F : ℂ) ^ 2 * (ldpHat f t - ldpQuadraticRootMinus f t) *
          (ldpHat f t - ldpQuadraticRootPlus f t) = 0 := by
    rw [← hfactor (ldpHat f t)]
    exact hactual'
  have hpair' : (F : ℂ) ^ 2 *
      ((ldpHat f t - ldpQuadraticRootMinus f t) *
        (ldpHat f t - ldpQuadraticRootPlus f t)) = 0 := by
    simpa only [mul_assoc] using hpair
  have hmul := mul_eq_zero.mp hpair'
  have hFcast_ne : (F : ℂ) ≠ 0 := by exact_mod_cast hFne
  have hF2ne : (F : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hFcast_ne
  have hcases :
      (ldpHat f t - ldpQuadraticRootMinus f t = 0) ∨
        (ldpHat f t - ldpQuadraticRootPlus f t = 0) := by
    rcases hmul with hmul | hmul
    · exact False.elim (hF2ne hmul)
    · exact mul_eq_zero.mp hmul
  refine ⟨hrootMinus, hrootPlus, ?_⟩
  rcases hcases with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

private noncomputable def reflectedPositiveLaw (g : ℤ → ℝ) :
    Measure {k : ℤ // 1 ≤ k} :=
  Measure.sum fun k : {k : ℤ // 1 ≤ k} =>
    ENNReal.ofReal (g (-k)) • Measure.dirac (k : {k : ℤ // 1 ≤ k})

private theorem reflectedPositiveCF_neg (g : ℤ → ℝ) (t : ℝ) :
    reflectedPositiveCF g (-t) = star (reflectedPositiveCF g t) := by
  unfold reflectedPositiveCF
  rw [Complex.star_def, Complex.conj_tsum]
  apply tsum_congr
  intro k
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 1
  simp only [Complex.conj_I, Complex.ofReal_neg, neg_mul]
  rw [mul_neg]

private theorem reflectedPositiveLaw_weights_hasSum
    (hgs : HasSum g (1 : ℝ))
    (hgsupp : ∀ y, 0 ≤ y → g y = 0) :
    HasSum (fun k : {k : ℤ // 1 ≤ k} => g (-k)) 1 := by
  have hneg : Summable (fun k : ℤ => g (-k)) :=
    hgs.summable.comp_injective (Equiv.neg ℤ).injective
  have htsum : (∑' k : ℤ, g (-k)) = 1 := by
    calc
      (∑' k : ℤ, g (-k)) = ∑' k : ℤ, g ((Equiv.neg ℤ) k) := rfl
      _ = ∑' k : ℤ, g k := (Equiv.neg ℤ).tsum_eq g
      _ = 1 := hgs.tsum_eq
  let S : Set ℤ := {k | 1 ≤ k}
  have hcompl : (∑' k : {k : ℤ // k ∈ Sᶜ}, g (-k)) = 0 := by
    have hz : (fun k : {k : ℤ // k ∈ Sᶜ} => g (-k)) = fun _ => 0 := by
      funext k
      have hknot : ¬ 1 ≤ k.val := by
        have hp : ¬ k.val ∈ S := by
          simpa only [Set.mem_compl_iff] using k.property
        simpa only [S, Set.mem_ofPred_eq] using hp
      have hk : k.val ≤ 0 := by
        omega
      exact hgsupp (-k.val) (by omega)
    rw [hz, tsum_zero]
  have hsubsum : (∑' k : {k : ℤ // 1 ≤ k}, g (-k)) = 1 := by
    have hdecomp := hneg.tsum_subtype_add_tsum_subtype_compl S
    rw [hcompl] at hdecomp
    change (∑' k : {k : ℤ // 1 ≤ k}, g (-k) + 0) = ∑' k : ℤ, g (-k) at hdecomp
    have hdecomp' :
        (∑' k : {k : ℤ // 1 ≤ k}, g (-k)) + 0 = ∑' k : ℤ, g (-k) := hdecomp
    calc
      (∑' k : {k : ℤ // 1 ≤ k}, g (-k)) =
          (∑' k : {k : ℤ // 1 ≤ k}, g (-k)) + 0 := by simp
      _ = ∑' k : ℤ, g (-k) := hdecomp'
      _ = 1 := htsum
  exact (hneg.subtype (fun k : ℤ => 1 ≤ k)).hasSum_iff.mpr hsubsum

private theorem reflectedPositiveLaw_isProbability
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hgsupp : ∀ y, 0 ≤ y → g y = 0) :
    IsProbabilityMeasure (reflectedPositiveLaw g) := by
  let hs := reflectedPositiveLaw_weights_hasSum hgs hgsupp
  exact HasSum.isProbabilityMeasure_sum_dirac (fun k => hg (-k)) hs

private theorem reflectedPositiveLaw_characteristic
    (hg : ∀ y, 0 ≤ g y) (t : ℝ) :
    (∫ k : {k : ℤ // 1 ≤ k},
      Complex.exp ((((t * ((k.val.toNat : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)
      ∂reflectedPositiveLaw g) = reflectedPositiveCF g t := by
  let X : {k : ℤ // 1 ≤ k} → ℕ := fun k => k.val.toNat
  have hXcast (k : {k : ℤ // 1 ≤ k}) : (X k : ℝ) = (k.val : ℝ) := by
    have hk : (k.val.toNat : ℤ) = k.val :=
      Int.toNat_of_nonneg (by omega)
    exact_mod_cast hk
  have hc (k : {k : ℤ // 1 ≤ k}) :
      ENNReal.ofReal (g (-k)) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  let χ : {k : ℤ // 1 ≤ k} → ℂ := fun k =>
    Complex.exp ((((t * (X k : ℝ) : ℝ) : ℂ) * Complex.I))
  change (∫ k : {k : ℤ // 1 ≤ k},
      χ k
      ∂Measure.sum (fun k : {k : ℤ // 1 ≤ k} =>
        ENNReal.ofReal (g (-k)) • Measure.dirac k)) = _
  rw [integral_sum_dirac hc]
  rw [reflectedPositiveCF]
  apply tsum_congr
  intro k
  simp only [ENNReal.toReal_ofReal (hg (-k)), χ, Complex.real_smul]
  rw [hXcast]

private theorem reflectedPositiveCF_eq_integerCF_neg
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hgsupp : ∀ y, 0 ≤ y → g y = 0) (t : ℝ) :
    reflectedPositiveCF g t = integerCF g (-t) := by
  let S : Set ℤ := {k | 1 ≤ k}
  let w : ℤ → ℂ := fun k => (g (-k) : ℂ) * cfPhase t k
  let v : ℤ → ℂ := fun k => (g k : ℂ) * cfPhase (-t) k
  have hwfun : w = fun k => v ((Equiv.neg ℤ) k) := by
    funext k
    simp [w, v, cfPhase_neg_neg]
  have hvsum := hasSum_cf hg hgs.summable (-t)
  have hw : Summable w := by
    rw [hwfun]
    exact hvsum.summable.comp_injective (Equiv.neg ℤ).injective
  have htsum : (∑' k : ℤ, w k) = integerCF g (-t) := by
    calc
      (∑' k : ℤ, w k) = ∑' k : ℤ, v ((Equiv.neg ℤ) k) := by rw [hwfun]
      _ = ∑' k : ℤ, v k := (Equiv.neg ℤ).tsum_eq v
      _ = integerCF g (-t) := hvsum.tsum_eq
  have hcompl : (∑' k : {k : ℤ // k ∈ Sᶜ}, w k) = 0 := by
    have hz : (fun k : {k : ℤ // k ∈ Sᶜ} => w k) = fun _ => 0 := by
      funext k
      have hknot : ¬ 1 ≤ k.val := by
        have hp : ¬ k.val ∈ S := by
          simpa only [Set.mem_compl_iff] using k.property
        simpa only [S, Set.mem_ofPred_eq] using hp
      have hk : k.val ≤ 0 := by omega
      simp [w, hgsupp (-k.val) (by omega)]
    rw [hz, tsum_zero]
  have hdecomp := hw.tsum_subtype_add_tsum_subtype_compl S
  rw [hcompl] at hdecomp
  have hsub : (∑' k : {k : ℤ // 1 ≤ k}, w k) = ∑' k : ℤ, w k := by
    have hdecomp' : (∑' k : {k : ℤ // k ∈ S}, w k) + 0 = ∑' k : ℤ, w k := hdecomp
    calc
      (∑' k : {k : ℤ // 1 ≤ k}, w k) =
          (∑' k : {k : ℤ // k ∈ S}, w k) := by rfl
      _ = (∑' k : {k : ℤ // k ∈ S}, w k) + 0 := by simp
      _ = ∑' k : ℤ, w k := hdecomp'
  calc
    reflectedPositiveCF g t = ∑' k : {k : ℤ // 1 ≤ k}, w k := by
      unfold reflectedPositiveCF w cfPhase
      rfl
    _ = ∑' k : ℤ, w k := hsub
    _ = integerCF g (-t) := htsum

private theorem ldp_Ghat_of_master
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
    (t : ℝ) :
    reflectedPositiveCF g t = -(integerCF f t * ldpHat f t) := by
  rw [reflectedPositiveCF_eq_integerCF_neg hg hgs hgsupp]
  have hb0 := ldp_big_rel_of_master hf hfs hg hgs hgsupp hrec 0 t
  have hN0 := negativeCF_zero hf hfs hsymm
  have hG0 := integerCF_zero hg hgs
  have hpE := cfPhase_neg_one_mul t
  simp only [neg_zero, hN0, hG0, cfPhase_zero_left] at hb0
  push_cast at hb0
  have hG : integerCF g (-t) = -(integerCF f t * ldpHat f t) := by
    unfold ldpHat ldpOffset
    push_cast
    linear_combination (-Complex.exp ((t : ℂ) * Complex.I)) * hb0 +
      (-(integerCF f t * ((f 0 : ℂ) + negativeCF f t) + integerCF g (-t))) * hpE
  exact hG

private theorem integerCF_continuous_of_symm
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ))
    (hsymm : ∀ x, f (-x) = f x) : Continuous (integerCF f) := by
  let C : ℝ → ℝ := fun t => ∑' k : ℤ, f k * Real.cos (t * (k : ℝ))
  have hC : Continuous C := by
    exact DirectedDistances.PaperProofs.Section6.continuous_integer_cosine_mass hf hfs.summable
  have hid : integerCF f = fun t => (C t : ℂ) := by
    funext t
    exact integerCF_eq_ofReal_cosine hf hfs.summable hsymm t
  rw [hid]
  exact Complex.continuous_ofReal.comp hC

private theorem negativeCF_continuous_of_summable
    (hp : ∀ k, 0 ≤ p k) (hps : Summable p) : Continuous (negativeCF p) := by
  let K := {k : ℤ // k ≤ -1}
  let u : K → ℝ := fun k => p k.val
  let φ : K → ℝ → ℂ := fun k t =>
    (p k.val : ℂ) * Complex.exp ((((t * (k.val : ℝ) : ℝ) : ℂ) * Complex.I))
  have hu : Summable u := hps.subtype (fun k : ℤ => k ≤ -1)
  have hφ : ∀ k, Continuous (φ k) := by
    intro k
    dsimp [φ]
    fun_prop
  have hbound : ∀ k t, ‖φ k t‖ ≤ u k := by
    intro k t
    dsimp [φ, u]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp k.val),
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hc := continuous_tsum hφ hu hbound
  change Continuous (fun t : ℝ => ∑' k : K,
    (p k.val : ℂ) * Complex.exp ((((t * (k.val : ℝ) : ℝ) : ℂ) * Complex.I)))
  exact hc

private theorem ldpHat_continuous_of_summable
    (hf : ∀ x, 0 ≤ f x) (hfs : HasSum f (1 : ℝ)) : Continuous (ldpHat f) := by
  have hneg := negativeCF_continuous_of_summable hf hfs.summable
  have hoff : Continuous (ldpOffset f) := by
    unfold ldpOffset
    fun_prop
  change Continuous (fun t : ℝ => negativeCF f t + ldpOffset f t)
  exact hneg.add hoff

private theorem ldp_side_branch_constancy
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
        (3 * integerCF f t - 1) * ldpHat f t + integerCF f t = 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ((∀ t : ℝ, 0 < t → t < δ → ldpHat f t = ldpQuadraticRootMinus f t) ∨
       (∀ t : ℝ, 0 < t → t < δ → ldpHat f t = ldpQuadraticRootPlus f t)) := by
  obtain ⟨δc, hδc, hcos⟩ :=
    DirectedDistances.PaperProofs.Section6.exists_integer_cosine_mass_interval
      hf hfs ((ldp_pmf_nondegenerate_of_master hf hfs hg hgs hsymm hgsupp hrec).1 0)
  obtain ⟨δr, hδr, hroots⟩ :=
    ldp_side_roots_and_actual hf hfs hg hgs hsymm hgsupp hrec hLdpQuad
  let δ : ℝ := min δc δr
  have hδ : 0 < δ := lt_min hδc hδr
  let S : Set ℝ := Set.Ioo 0 δ
  let F : ℝ → ℝ := fun t => (integerCF f t).re
  let A : ℝ → ℝ := fun t => (1 - F t) * (1 - 2 * F t) / (2 * F t ^ 2)
  let B : ℝ → ℝ := fun t => (1 - F t) * Real.sqrt (4 * F t - 1) / (2 * F t ^ 2)
  have hFcos (t : ℝ) : F t = ∑' k : ℤ, f k * Real.cos (t * (k : ℝ)) := by
    exact integerCF_re hf hfs.summable t
  have hbounds : ∀ t ∈ S, (1 / 4 : ℝ) < F t ∧ F t < 1 := by
    intro t ht
    have htcos : 0 < t ∧ t < δc := ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
    obtain ⟨hlo, hhi⟩ := hcos t htcos.1 htcos.2
    rw [← hFcos] at hlo hhi
    exact ⟨hlo, hhi⟩
  have hactual : ∀ t ∈ S,
      ((ldpHat f t = ldpQuadraticRootMinus f t) ∨
       (ldpHat f t = ldpQuadraticRootPlus f t)) := by
    intro t ht
    have htr : 0 < t ∧ t < δr := ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
    exact (hroots t htr.1 htr.2).2.2
  have hFcont : Continuous F := by
    dsimp [F]
    exact Complex.continuous_re.comp (integerCF_continuous_of_symm hf hfs hsymm)
  have hhatcont : Continuous (ldpHat f) := ldpHat_continuous_of_summable hf hfs
  have hdenF : ∀ t ∈ S, 2 * F t ^ 2 ≠ 0 := by
    intro t ht
    have hFpos : 0 < F t := lt_trans (by norm_num : (0 : ℝ) < 1 / 4) (hbounds t ht).1
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hFpos.ne')
  have hAcont : ContinuousOn A S := by
    dsimp [A]
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · exact hdenF
  have hBcont : ContinuousOn B S := by
    dsimp [B]
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · exact hdenF
  have hminusForm (t : ℝ) : ldpQuadraticRootMinus f t =
      (-1 : ℂ) + (A t : ℂ) - (B t : ℂ) * Complex.I := by
    simp [ldpQuadraticRootMinus, A, B, F]
  have hplusForm (t : ℝ) : ldpQuadraticRootPlus f t =
      (-1 : ℂ) + (A t : ℂ) + (B t : ℂ) * Complex.I := by
    simp [ldpQuadraticRootPlus, A, B, F]
  have hminusCont : ContinuousOn (ldpQuadraticRootMinus f) S := by
    apply (show ContinuousOn (fun t : ℝ =>
      (-1 : ℂ) + (A t : ℂ) - (B t : ℂ) * Complex.I) S from by fun_prop).congr
    intro t ht
    exact (hminusForm t).symm
  have hplusCont : ContinuousOn (ldpQuadraticRootPlus f) S := by
    apply (show ContinuousOn (fun t : ℝ =>
      (-1 : ℂ) + (A t : ℂ) + (B t : ℂ) * Complex.I) S from by fun_prop).congr
    intro t ht
    exact (hplusForm t).symm
  have hBpos : ∀ t ∈ S, 0 < B t := by
    intro t ht
    have ⟨hFlo, hFhi⟩ := hbounds t ht
    apply div_pos
    · apply mul_pos
      · linarith
      · apply Real.sqrt_pos.2
        linarith
    · positivity
  have hrootsNe : ∀ t ∈ S,
      ldpQuadraticRootMinus f t ≠ ldpQuadraticRootPlus f t := by
    intro t ht hEq
    have hIm := congrArg Complex.im hEq
    rw [hminusForm, hplusForm] at hIm
    simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, add_zero] at hIm
    have := hBpos t ht
    linarith
  let Q : ℝ → ℂ := fun t =>
    (ldpHat f t - ldpQuadraticRootPlus f t) /
      (ldpQuadraticRootMinus f t - ldpQuadraticRootPlus f t)
  have hQden : ∀ t ∈ S,
      ldpQuadraticRootMinus f t - ldpQuadraticRootPlus f t ≠ 0 := by
    intro t ht hz
    exact hrootsNe t ht (sub_eq_zero.mp hz)
  have hQcont : ContinuousOn Q S := by
    dsimp [Q]
    exact (hhatcont.continuousOn.sub hplusCont).div
      (hminusCont.sub hplusCont) hQden
  let T : Set ℂ := {0, 1}
  have hT : IsDiscrete T := by
    apply Set.Finite.isDiscrete
    simp [T]
  have hQmaps : Set.MapsTo Q S T := by
    intro t ht
    rcases hactual t ht with h | h
    · have hq : Q t = 1 := by
        dsimp [Q]
        rw [h]
        exact div_self (hQden t ht)
      rw [hq]
      simp [T]
    · have hq : Q t = 0 := by
        dsimp [Q]
        rw [h]
        simp
      rw [hq]
      simp [T]
  let t₀ : ℝ := δ / 2
  have ht₀ : t₀ ∈ S := by
    dsimp [t₀, S]
    constructor <;> linarith
  have hQconst (t : ℝ) (ht : t ∈ S) : Q t = Q t₀ :=
    isPreconnected_Ioo.constant_of_mapsTo hT hQcont hQmaps ht ht₀
  have hbranch₀ := hactual t₀ ht₀
  refine ⟨δ, hδ, ?_⟩
  rcases hbranch₀ with h₀ | h₀
  · left
    intro t ht htd
    have htS : t ∈ S := ⟨ht, htd⟩
    rcases hactual t htS with h | h
    · exact h
    · have hqt : Q t = 0 := by
        dsimp [Q]
        rw [h]
        simp
      have hq₀ : Q t₀ = 1 := by
        dsimp [Q]
        rw [h₀]
        exact div_self (hQden t₀ ht₀)
      rw [hQconst t htS] at hqt
      rw [hq₀] at hqt
      norm_num at hqt
  · right
    intro t ht htd
    have htS : t ∈ S := ⟨ht, htd⟩
    rcases hactual t htS with h | h
    · have hqt : Q t = 1 := by
        dsimp [Q]
        rw [h]
        exact div_self (hQden t htS)
      have hq₀ : Q t₀ = 0 := by
        dsimp [Q]
        rw [h₀]
        simp
      rw [hQconst t htS] at hqt
      rw [hq₀] at hqt
      norm_num at hqt
    · exact h

private theorem reflectedPositiveLaw_tauberian_positive_imag
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hgsupp : ∀ y, 0 ≤ y → g y = 0)
    (c : ℂ) (hc : c.re ≠ 0) (ν : ℝ) (hν₀ : 0 < ν) (hν₁ : ν < 1)
    (hcf : (fun t : ℝ => reflectedPositiveCF g t - 1 -
        (if 0 < t then c else starRingEnd ℂ c) *
          (((|t| : ℝ) ^ ν : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)]
        (fun t : ℝ => (|t| : ℝ) ^ ν)) :
    0 < c.im := by
  let X : {k : ℤ // 1 ≤ k} → ℕ := fun k => k.val.toNat
  have hX : Measurable X := measurable_of_countable X
  let μ := reflectedPositiveLaw g
  letI : IsProbabilityMeasure μ := by
    exact reflectedPositiveLaw_isProbability hg hgs hgsupp
  have hfun :
      (fun t : ℝ =>
        (∫ k : {k : ℤ // 1 ≤ k},
          Complex.exp ((((t * (X k : ℝ) : ℝ) : ℂ) * Complex.I) : ℂ) ∂μ) - 1 -
          (if 0 < t then c else starRingEnd ℂ c) *
            (((|t| : ℝ) ^ ν : ℝ) : ℂ)) =
      (fun t : ℝ => reflectedPositiveCF g t - 1 -
        (if 0 < t then c else starRingEnd ℂ c) *
          (((|t| : ℝ) ^ ν : ℝ) : ℂ)) := by
    funext t
    rw [reflectedPositiveLaw_characteristic hg t]
  have hExp :
      (fun t : ℝ =>
        (∫ k : {k : ℤ // 1 ≤ k},
          Complex.exp ((((t * (X k : ℝ) : ℝ) : ℂ) * Complex.I) : ℂ) ∂μ) - 1 -
          (if 0 < t then c else starRingEnd ℂ c) *
            (((|t| : ℝ) ^ ν : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)]
        (fun t : ℝ => (|t| : ℝ) ^ ν) := by
    rw [hfun]
    exact hcf
  have htaub :=
    DirectedDistances.Paper.Section6.tauberian_characteristic
      ({k : ℤ // 1 ≤ k}) μ X hX
  have hfirst := htaub.1 c hc ν hν₀ hν₁ hExp
  exact hfirst.2.1

private theorem reflectedPositiveCF_littleO_of_positive_limit
    (g : ℤ → ℝ) (c : ℂ) (ν : ℝ) (_hν : 0 < ν)
    (hpos : Tendsto
      (fun t : ℝ => (reflectedPositiveCF g t - 1) / ((t ^ ν : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 c)) :
    (fun t : ℝ => reflectedPositiveCF g t - 1 -
      (if 0 < t then c else starRingEnd ℂ c) * (((|t| ^ ν : ℝ) : ℝ) : ℂ))
      =o[𝓝[≠] (0 : ℝ)] (fun t : ℝ => (|t| : ℝ) ^ ν) := by
  let E : ℝ → ℂ := fun t => (((|t| : ℝ) ^ ν : ℝ) : ℂ)
  let R : ℝ → ℂ := fun t => reflectedPositiveCF g t - 1 -
    (if 0 < t then c else starRingEnd ℂ c) * E t
  let Q : ℝ → ℂ := fun t => R t / E t
  have hposQ : Tendsto Q (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := hpos.sub_const c
    have h' : Tendsto (fun t : ℝ =>
        (reflectedPositiveCF g t - 1) / ((t ^ ν : ℝ) : ℂ) - c)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa using h
    apply h'.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := Set.mem_Ioi.mp ht
    have hε : t ^ ν ≠ 0 := (Real.rpow_pos_of_pos htpos ν).ne'
    have hεc : ((t ^ ν : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hε
    dsimp [Q, R, E]
    simp only [if_pos htpos, abs_of_pos htpos]
    field_simp [hεc]
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    have hcont : Tendsto (fun t : ℝ => -t) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using
      (continuous_neg.continuousAt (x := (0 : ℝ))).tendsto
    refine ⟨hcont.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htlt : t < 0 := Set.mem_Iio.mp ht
    exact neg_pos.mpr htlt
  have hnegQ : Tendsto Q (𝓝[<] (0 : ℝ)) (𝓝 0) := by
    have hstar : Tendsto (fun t : ℝ => star (Q (-t)))
        (𝓝[<] (0 : ℝ)) (𝓝 0) := by
      have h := (hposQ.comp hneg)
      have h' := (continuous_star.continuousAt (x := (0 : ℂ))).tendsto.comp h
      change Tendsto (fun t : ℝ => star (Q (-t))) (𝓝[<] (0 : ℝ))
        (𝓝 (star (0 : ℂ))) at h'
      simpa using h'
    apply hstar.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htlt : t < 0 := Set.mem_Iio.mp ht
    have htneg : ¬ 0 < t := not_lt.mpr (le_of_lt htlt)
    have htpos : 0 < -t := neg_pos.mpr htlt
    have hsymm : reflectedPositiveCF g t = star (reflectedPositiveCF g (-t)) := by
      have h := reflectedPositiveCF_neg g (-t)
      simpa only [neg_neg] using h
    dsimp [Q, R, E]
    rw [hsymm]
    simp [htneg, htpos, abs_neg]
  have hQ : Tendsto Q (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    rw [punctured_nhds_eq_nhdsWithin_sup_nhdsWithin]
    exact hnegQ.sup hposQ
  have hnonzero : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), E t = 0 → R t = 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht hEt
    have htne : t ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
    have hEtpos : 0 < |t| ^ ν := Real.rpow_pos_of_pos (abs_pos.mpr htne) ν
    have hEtne : E t ≠ 0 := Complex.ofReal_ne_zero.mpr hEtpos.ne'
    exact False.elim (hEtne hEt)
  have hlittle := (isLittleO_iff_tendsto' hnonzero).2 hQ
  rw [isLittleO_iff] at hlittle ⊢
  intro ε hε
  filter_upwards [hlittle hε] with t ht
  simpa [R, E, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg t) ν)] using ht

private theorem reflectedPositiveCF_coeff_of_products
    (hGhat : ∀ t : ℝ,
      reflectedPositiveCF g t = -(integerCF f t * ldpHat f t))
    (ε : ℝ → ℂ) (aF aHat : ℂ)
    (hF : Tendsto (fun t : ℝ => (integerCF f t - 1) / ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 aF))
    (hHat0 : Tendsto (ldpHat f) (𝓝[>] (0 : ℝ)) (𝓝 (-1)))
    (hHat : Tendsto (fun t : ℝ => (ldpHat f t + 1) / ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 aHat))
    (hε : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ε t ≠ 0) :
    Tendsto (fun t : ℝ => (reflectedPositiveCF g t - 1) / ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 (aF - aHat)) := by
  have hlim : Tendsto
      (fun t : ℝ => -(((integerCF f t - 1) / ε t) * ldpHat f t) -
        ((ldpHat f t + 1) / ε t))
      (𝓝[>] (0 : ℝ)) (𝓝 (aF - aHat)) := by
    convert (hF.mul hHat0).neg.sub hHat using 1 <;> simp
  apply hlim.congr'
  filter_upwards [hε] with t hεt
  rw [hGhat t]
  field_simp [hεt]
  ring

private theorem ldp_real_transform_coeff
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
    0 < κ ∧ Tendsto
      (fun t : ℝ => (integerCF f t - 1) / ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(a : ℂ))) := by
  dsimp only
  obtain ⟨hκ, hFsmall⟩ := ldp_real_transform_expansion
    hf hfs hg hgs hsymm hgsupp hrec hLdpQuad hLdpReal
  let a : ℝ := ((3 + f 0) / 2) ^ (1 / 3 : ℝ)
  let ε : ℝ → ℂ := fun t => ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)
  have ha : 0 < a := by
    apply Real.rpow_pos_of_pos
    positivity
  have hF : Tendsto (fun t : ℝ => (integerCF f t - 1) / ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 (-(a : ℂ))) := by
    have hsmall := hFsmall.tendsto_div_nhds_zero
    have hsub := hsmall.sub_const (a : ℂ)
    have hlim : Tendsto (fun t : ℝ =>
        ((integerCF f t - (1 - (a : ℂ) * ε t)) / ε t) - a)
        (𝓝[>] (0 : ℝ)) (𝓝 (-(a : ℂ))) := by
      convert hsub using 1 <;> simp
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := Set.mem_Ioi.mp ht
    have hε : ε t ≠ 0 := by
      apply Complex.ofReal_ne_zero.mpr
      exact (Real.rpow_pos_of_pos htpos _).ne'
    have hε' : ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := by
      simpa [ε] using hε
    dsimp [ε]
    field_simp [hε']
    ring
  exact ⟨hκ, hF⟩

/-- The Tauberian sign selects the negative-imaginary LDP quadratic root on a
The source branch is the minus root for `ldpHat`, equivalently the plus-sign
branch for the reflected law `eq:Ghat`. -/
theorem ldp_side_select_minus
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
      ldpHat f t = ldpQuadraticRootMinus f t := by
  obtain ⟨δ, hδ, hbranch⟩ := ldp_side_branch_constancy
    hf hfs hg hgs hsymm hgsupp hrec hLdpQuad
  have hGhat : ∀ t : ℝ,
      reflectedPositiveCF g t = -(integerCF f t * ldpHat f t) := by
    intro t
    exact ldp_Ghat_of_master hf hfs hg hgs hsymm hgsupp hrec t
  have hGhat' : ∀ t : ℝ,
      reflectedPositiveCF g t = -integerCF f t * ldpHat f t := by
    intro t
    rw [hGhat t]
    ring
  obtain ⟨hκ, hrootMinus, hrootPlus⟩ := ldp_side_candidate_root_expansions
    hf hfs hg hgs hsymm hgsupp hrec hLdpQuad hLdpReal hGhat'
  obtain ⟨_, hFsmall⟩ := ldp_real_transform_expansion
    hf hfs hg hgs hsymm hgsupp hrec hLdpQuad hLdpReal
  let a : ℝ := ((3 + f 0) / 2) ^ (1 / 3 : ℝ)
  let dMinus : ℂ := ((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2
  let dPlus : ℂ := ((-1 : ℂ) + (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2
  let ε : ℝ → ℂ := fun t => ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)
  let cBad : ℂ := (((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2) * (a : ℂ)
  have ha : 0 < a := by
    apply Real.rpow_pos_of_pos
    have hk : 0 < 3 + f 0 := by simpa using hκ
    positivity
  have hFcoeff : Tendsto (fun t : ℝ => (integerCF f t - 1) / ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 (-(a : ℂ))) := by
    have h := (ldp_real_transform_coeff hf hfs hg hgs hsymm hgsupp hrec hLdpQuad hLdpReal).2
    simpa [ε, a] using h
  have hHat0val : ldpHat f 0 = -1 := by
    rw [ldpHat, ldpOffset, negativeCF_zero hf hfs hsymm]
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    push_cast
    ring
  have hHat0 : Tendsto (ldpHat f) (𝓝[>] (0 : ℝ)) (𝓝 (-1)) := by
    have h := (ldpHat_continuous_of_summable hf hfs).continuousAt.tendsto
      (x := (0 : ℝ))
    rw [hHat0val] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hεne : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ε t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (Set.mem_Ioi.mp ht) _).ne'
  rcases hbranch with hminusBranch | hplusBranch
  · exact ⟨δ, hδ, hminusBranch⟩
  · have hHatPlus : Tendsto (fun t : ℝ => (ldpHat f t + 1) / ε t)
        (𝓝[>] (0 : ℝ)) (𝓝 (dPlus * (a : ℂ))) := by
      apply hrootPlus.congr'
      filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
      rw [hplusBranch t ht.1 ht.2]
    have hGcoeff := reflectedPositiveCF_coeff_of_products
      hGhat ε (-(a : ℂ)) (dPlus * (a : ℂ)) hFcoeff hHat0 hHatPlus hεne
    have hcEq : (-(a : ℂ)) - dPlus * (a : ℂ) = cBad := by
      dsimp [cBad, dPlus]
      ring
    rw [hcEq] at hGcoeff
    have hcf := reflectedPositiveCF_littleO_of_positive_limit
      g cBad (2 / 3 : ℝ) (by norm_num) hGcoeff
    have hcRe : cBad.re ≠ 0 := by
      have hre : cBad.re = -(a / 2) := by
        dsimp [cBad]
        simp only [Complex.div_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        norm_num [Complex.normSq]
        ring
      rw [hre]
      exact ne_of_lt (neg_lt_zero.mpr (div_pos ha (by norm_num)))
    have hcIm : cBad.im < 0 := by
      have him : cBad.im = -(Real.sqrt 3 / 2) * a := by
        dsimp [cBad]
        simp only [Complex.div_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        norm_num [Complex.normSq]
        ring
      rw [him]
      have hcoef : 0 < Real.sqrt 3 / 2 :=
        div_pos (Real.sqrt_pos.2 (by norm_num)) (by norm_num)
      exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hcoef) ha
    have hpos := reflectedPositiveLaw_tauberian_positive_imag
      hg hgs hgsupp cBad hcRe (2 / 3 : ℝ) (by norm_num) (by norm_num) hcf
    linarith

private theorem integerCF_eq_negativeCF_of_support
    (hg : ∀ y, 0 ≤ g y) (hgs : HasSum g (1 : ℝ))
    (hgsupp : ∀ y, 0 ≤ y → g y = 0) (t : ℝ) :
    integerCF g t = negativeCF g t := by
  have hcf := hasSum_cf hg hgs.summable t
  have hneg := hasSum_neg_half hcf (fun k hk => by
    simp [hgsupp k hk])
  exact hneg.unique (hasSum_negativeCF hg hgs.summable t)

private theorem ldp_exp_ratio_tendsto_zero :
    Tendsto (fun t : ℝ =>
      (Complex.exp ((t : ℂ) * Complex.I) - 1) / ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let φ : ℝ → ℂ := fun t => Complex.exp ((t : ℂ) * Complex.I)
  have hφ0 : φ 0 = 1 := by simp [φ]
  have hderiv : HasDerivAt φ Complex.I 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).mul_const (1 : ℝ)).ofReal_comp.mul_const
      Complex.I).cexp
    simpa [φ] using h
  have hslope : Tendsto (fun t : ℝ => t⁻¹ • (φ t - φ 0))
      (𝓝[>] (0 : ℝ)) (𝓝 Complex.I) := by
    simpa only [zero_add] using hderiv.tendsto_slope_zero_right
  have hratio : Tendsto (fun t : ℝ =>
      (Complex.exp ((t : ℂ) * Complex.I) - 1) / (t : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 Complex.I) := by
    apply hslope.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htne : t ≠ 0 := ne_of_gt (Set.mem_Ioi.mp ht)
    change t⁻¹ • (φ t - φ 0) = _
    rw [hφ0]
    simp only [Complex.real_smul, Complex.ofReal_inv]
    field_simp [Complex.ofReal_ne_zero.mpr htne]
    ring
  have hthird : Tendsto (fun t : ℝ => ((t ^ (1 / 3 : ℝ) : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 (1 / 3 : ℝ)
      (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 3))).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
    simpa only [Function.comp_def, Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0),
      Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp h
  have hproduct : Tendsto
      (fun t : ℝ => ((Complex.exp ((t : ℂ) * Complex.I) - 1) / (t : ℂ)) *
        ((t ^ (1 / 3 : ℝ) : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert hratio.mul hthird using 1 <;> simp
  apply hproduct.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := Set.mem_Ioi.mp ht
  have hpow : t ^ (2 / 3 : ℝ) * t ^ (1 / 3 : ℝ) = t := by
    rw [← Real.rpow_add htpos]
    norm_num
  have hpow' : t ^ (1 / 3 : ℝ) * t ^ (2 / 3 : ℝ) = t := by
    simpa [mul_comm] using hpow
  have hpowCast : ((t ^ (1 / 3 : ℝ) * t ^ (2 / 3 : ℝ) : ℝ) : ℂ) = (t : ℂ) := by
    exact_mod_cast hpow'
  have hpowne : ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos htpos _).ne'
  have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr htpos.ne'
  field_simp [hpowne, htne]
  calc
    _ = (Complex.exp ((t : ℂ) * Complex.I) - 1) *
        (((t ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)) := by
      ring
    _ = (Complex.exp ((t : ℂ) * Complex.I) - 1) *
        (((t ^ (1 / 3 : ℝ) * t ^ (2 / 3 : ℝ) : ℝ) : ℂ)) := by
      rw [← Complex.ofReal_mul]
    _ = (t : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) - 1) := by
      rw [hpowCast]
      ring

private theorem ldpOffset_ratio_tendsto_zero (f : ℤ → ℝ) :
    Tendsto (fun t : ℝ =>
      (ldpOffset f t - ldpOffset f 0) / ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let C : ℂ := (((3 + f 0) / 2 : ℝ) : ℂ)
  have hscaled : Tendsto (fun t : ℝ =>
      -C * (Complex.exp ((t : ℂ) * Complex.I) - 1) /
        ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℝ => -C) (𝓝[>] (0 : ℝ)) (𝓝 (-C)) :=
      tendsto_const_nhds
    have h := hconst.mul ldp_exp_ratio_tendsto_zero
    have h' : Tendsto (fun t : ℝ =>
        -C * ((Complex.exp ((t : ℂ) * Complex.I) - 1) /
          ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using h
    apply h'.congr'
    filter_upwards with t
    ring
  apply hscaled.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := Set.mem_Ioi.mp ht
  have hε : ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos htpos _).ne'
  have hidentity : ldpOffset f t - ldpOffset f 0 =
      -C * (Complex.exp ((t : ℂ) * Complex.I) - 1) := by
    dsimp [ldpOffset, C]
    simp only [zero_mul]
    rw [Complex.exp_zero]
    ring_nf
  rw [hidentity]

private theorem complex_remainder_littleO_of_normalized_limit
    (F : ℝ → ℂ) (c₀ c : ℂ)
    (h : Tendsto (fun t : ℝ => (F t - c₀) /
      ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 c)) :
    (fun t : ℝ => F t - c₀ - c * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ))
      =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (2 / 3 : ℝ)) := by
  let ε : ℝ → ℂ := fun t => ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)
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
      ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ) = 0 →
        F t - c₀ - c * ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ) = 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht hz
    have hpos : 0 < t := Set.mem_Ioi.mp ht
    have hne : ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hpos (2 / 3 : ℝ)).ne'
    exact False.elim (hne hz)
  have hlittle := (isLittleO_iff_tendsto' hden).2 hratio
  rw [isLittleO_iff] at hlittle ⊢
  intro C hC
  filter_upwards [self_mem_nhdsWithin, hlittle hC] with t ht hbound
  have htpos : 0 < t := Set.mem_Ioi.mp ht
  simpa [ε, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt htpos) _)] using hbound

/-! ## Proposition 6.2 side expansions -/

/-- The source expansions of `F⁻` and `G` in Proposition 6.2,
negative-index transform `G`; support of `g` also identifies it with
`integerCF g`. -/
theorem ldp_side_expansions
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
    let d : ℂ := ((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2
    (fun t : ℝ => negativeCF f t - (((1 - f 0) / 2 : ℝ) : ℂ) -
      (d * (a : ℂ)) * (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (2 / 3 : ℝ)) ∧
    (fun t : ℝ => negativeCF g t - 1 -
      (d * (a : ℂ)) * (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (2 / 3 : ℝ)) := by
  obtain ⟨δ, hδ, hselect⟩ := ldp_side_select_minus
    hf hfs hg hgs hsymm hgsupp hrec hLdpQuad hLdpReal
  have hGhat : ∀ t : ℝ,
      reflectedPositiveCF g t = -(integerCF f t * ldpHat f t) := by
    intro t
    exact ldp_Ghat_of_master hf hfs hg hgs hsymm hgsupp hrec t
  have hGhat' : ∀ t : ℝ,
      reflectedPositiveCF g t = -integerCF f t * ldpHat f t := by
    intro t
    rw [hGhat t]
    ring
  obtain ⟨_, hrootMinus, _⟩ := ldp_side_candidate_root_expansions
    hf hfs hg hgs hsymm hgsupp hrec hLdpQuad hLdpReal hGhat'
  let a : ℝ := ((3 + f 0) / 2) ^ (1 / 3 : ℝ)
  let d : ℂ := ((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2
  let cGood : ℂ := ((-1 : ℂ) + (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2 * (a : ℂ)
  let ε : ℝ → ℂ := fun t => ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)
  have ha : 0 < a := by
    apply Real.rpow_pos_of_pos
    have hk : 0 < 3 + f 0 := by
      obtain ⟨hκ, _⟩ := ldp_real_transform_coeff hf hfs hg hgs hsymm hgsupp hrec hLdpQuad hLdpReal
      simpa using hκ
    positivity
  have hFcoeff : Tendsto (fun t : ℝ => (integerCF f t - 1) / ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 (-(a : ℂ))) := by
    have h := (ldp_real_transform_coeff hf hfs hg hgs hsymm hgsupp hrec hLdpQuad hLdpReal).2
    simpa [ε, a] using h
  have hHat0val : ldpHat f 0 = -1 := by
    rw [ldpHat, ldpOffset, negativeCF_zero hf hfs hsymm]
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    push_cast
    ring
  have hHat0 : Tendsto (ldpHat f) (𝓝[>] (0 : ℝ)) (𝓝 (-1)) := by
    have h := (ldpHat_continuous_of_summable hf hfs).continuousAt.tendsto
      (x := (0 : ℝ))
    rw [hHat0val] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hεne : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ε t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (Set.mem_Ioi.mp ht) _).ne'
  have hHatMinus : Tendsto (fun t : ℝ => (ldpHat f t + 1) / ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 (d * (a : ℂ))) := by
    apply hrootMinus.congr'
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
    rw [hselect t ht.1 ht.2]
  have hGbarCoeff := reflectedPositiveCF_coeff_of_products
    hGhat ε (-(a : ℂ)) (d * (a : ℂ)) hFcoeff hHat0 hHatMinus hεne
  have hcGood : (-(a : ℂ)) - d * (a : ℂ) = cGood := by
    dsimp [d, cGood]
    ring
  rw [hcGood] at hGbarCoeff
  have hGSourceCoeff : Tendsto (fun t : ℝ => (negativeCF g t - 1) / ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 (star cGood)) := by
    have hstar : Tendsto (fun t : ℝ => star ((reflectedPositiveCF g t - 1) / ε t))
        (𝓝[>] (0 : ℝ)) (𝓝 (star cGood)) := by
      exact (continuous_star.continuousAt.tendsto.comp hGbarCoeff)
    apply hstar.congr'
    filter_upwards [self_mem_nhdsWithin] with t _
    have hnegative := integerCF_eq_negativeCF_of_support hg hgs hgsupp t
    have hreflect := reflectedPositiveCF_eq_integerCF_neg hg hgs hgsupp (-t)
    have hsymmCF := reflectedPositiveCF_neg g t
    have hreflect' : integerCF g t = reflectedPositiveCF g (-t) := by
      simpa only [neg_neg] using hreflect.symm
    have hsource : negativeCF g t = star (reflectedPositiveCF g t) := by
      calc
        negativeCF g t = integerCF g t := hnegative.symm
        _ = reflectedPositiveCF g (-t) := hreflect'
        _ = star (reflectedPositiveCF g t) := hsymmCF
    rw [hsource]
    simp [ε, Complex.star_def]
  have hFminusCoeff : Tendsto
      (fun t : ℝ => (negativeCF f t - (((1 - f 0) / 2 : ℝ) : ℂ)) / ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 (d * (a : ℂ))) := by
    have hOffset := ldpOffset_ratio_tendsto_zero f
    have hlim := hHatMinus.sub hOffset
    have hzero : (((1 - f 0) / 2 : ℝ) : ℂ) + ldpOffset f 0 = -1 := by
      simpa [ldpHat, negativeCF_zero hf hfs hsymm] using hHat0val
    have hlim' : Tendsto
        (fun x : ℝ => (ldpHat f x + 1) / ε x -
          (ldpOffset f x - ldpOffset f 0) / ((x ^ (2 / 3 : ℝ) : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (d * (a : ℂ))) := by simpa using hlim
    apply hlim'.congr'
    filter_upwards [hεne] with t hεt
    have hidentity : negativeCF f t - (((1 - f 0) / 2 : ℝ) : ℂ) =
        ldpHat f t + 1 - (ldpOffset f t - ldpOffset f 0) := by
      rw [ldpHat]
      linear_combination (-1 : ℂ) * hzero
    rw [hidentity]
    have hεc : ((t ^ (2 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := by
      simpa [ε] using hεt
    field_simp [hεc]
    ring
  have hFminus := complex_remainder_littleO_of_normalized_limit
    (negativeCF f) (((1 - f 0) / 2 : ℝ) : ℂ) (d * (a : ℂ)) hFminusCoeff
  have hGsource := complex_remainder_littleO_of_normalized_limit
    (negativeCF g) (1 : ℂ) (star cGood) hGSourceCoeff
  have hcoeffConj : star cGood = d * (a : ℂ) := by
    have hbase : star (((-1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2) = d := by
      apply Complex.ext
      · simp [d, Complex.star_def]
      · simp [d, Complex.star_def]
    change star (((-1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (a : ℂ)) =
      d * (a : ℂ)
    calc
      star (((-1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 * (a : ℂ)) =
          star (((-1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2) * star (a : ℂ) :=
            map_mul (starRingEnd ℂ) _ _
      _ = d * (a : ℂ) := by rw [hbase]; simp
  constructor
  · simpa only [hcoeffConj] using hFminus
  · simpa only [hcoeffConj] using hGsource

/-- The root identities and actual-root disjunction from the seven source premises,
using `eq:quadratic-new` proved from the master equation -/
theorem ldp_side_roots_and_actual_of_master
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
         else 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ((integerCF f t) ^ 2 * (ldpQuadraticRootMinus f t) ^ 2 +
          (3 * integerCF f t - 1) * ldpQuadraticRootMinus f t + integerCF f t = 0) ∧
        ((integerCF f t) ^ 2 * (ldpQuadraticRootPlus f t) ^ 2 +
          (3 * integerCF f t - 1) * ldpQuadraticRootPlus f t + integerCF f t = 0) ∧
        (ldpHat f t = ldpQuadraticRootMinus f t ∨
          ldpHat f t = ldpQuadraticRootPlus f t) :=
  ldp_side_roots_and_actual hf hfs hg hgs hsymm hgsupp hrec
    (ldp_quadratic_of_master hf hfs hg hgs hsymm hgsupp hrec)

/-- The selected `ldpQuadraticRootMinus` branch from the seven source premises,
using the quadratic and real-part identity proved from the master equation -/
theorem ldp_side_select_minus_of_master
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
         else 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ldpHat f t = ldpQuadraticRootMinus f t :=
  ldp_side_select_minus hf hfs hg hgs hsymm hgsupp hrec
    (ldp_quadratic_of_master hf hfs hg hgs hsymm hgsupp hrec)
    (ldp_real_part_of_symm hf hfs hsymm)

/-- The two Proposition 6.2 side expansions from the seven source premises,
using the quadratic and real-part identity proved from the master equation -/
theorem ldp_side_expansions_of_master
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
         else 0)) :
    let κ : ℝ := 3 + f 0
    let a : ℝ := (κ / 2) ^ (1 / 3 : ℝ)
    let d : ℂ := ((-1 : ℂ) - (Real.sqrt (3 : ℝ) : ℂ) * Complex.I) / 2
    (fun t : ℝ => negativeCF f t - (((1 - f 0) / 2 : ℝ) : ℂ) -
      (d * (a : ℂ)) * (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (2 / 3 : ℝ)) ∧
    (fun t : ℝ => negativeCF g t - 1 -
      (d * (a : ℂ)) * (((t ^ (2 / 3 : ℝ) : ℝ) : ℂ)))
        =o[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (2 / 3 : ℝ)) :=
  ldp_side_expansions hf hfs hg hgs hsymm hgsupp hrec
    (ldp_quadratic_of_master hf hfs hg hgs hsymm hgsupp hrec)
    (ldp_real_part_of_symm hf hfs hsymm)

end LDP

end DirectedDistances.Recursive
