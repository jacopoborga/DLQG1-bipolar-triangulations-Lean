/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section6.IncrementLawsIdentified
import DirectedDistances.Recursive.LDPQuadraticFromMaster
import DirectedDistances.Recursive.SDPQuadraticFromMaster
import DirectedDistances.PaperProofs.Section6.Next.CharacteristicDiscriminant

/-! Supporting lemmas for paper labels `lem:nonreal2` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section6

open DirectedDistances.RandomWalk DirectedDistances.Recursive



private theorem nonrealIdentified_negativeCF_continuous {p : ℤ → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hps : Summable p) : Continuous (negativeCF p) := by
  let K := {k : ℤ // k ≤ -1}
  let u : K → ℝ := fun k => p k.val
  let phase : K → ℝ → ℂ := fun k t =>
    (p k.val : ℂ) * Complex.exp ((((t * (k.val : ℝ) : ℝ) : ℂ) * Complex.I))
  have hu : Summable u := hps.subtype (fun k : ℤ => k ≤ -1)
  have hphase : ∀ k, Continuous (phase k) := by
    intro k
    dsimp [phase]
    fun_prop
  have hbound : ∀ k t, ‖phase k t‖ ≤ u k := by
    intro k t
    dsimp [phase, u]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp k.val),
      Complex.norm_exp_ofReal_mul_I, mul_one]
  exact continuous_tsum hphase hu hbound



theorem nonrealIdentified_ldpHat_continuous :
    Continuous (ldpHat incrementLawsIdentified_ldpF) := by
  rw [incrementLawsIdentified_ldpF_eq]
  have hneg := nonrealIdentified_negativeCF_continuous
    busemann_ldpF_nonneg busemann_ldpF_hasSum_one.summable
  have hoff : Continuous (ldpOffset (ldpF iidCodeMeasure busemannLDPMeasurableVersion)) := by
    unfold ldpOffset
    fun_prop
  exact hneg.add hoff



theorem nonrealIdentified_ldpHat_root (t : ℝ) :
    (integerCF incrementLawsIdentified_ldpF t) ^ 2 *
        (ldpHat incrementLawsIdentified_ldpF t) ^ 2 +
      (3 * integerCF incrementLawsIdentified_ldpF t - 1) *
        ldpHat incrementLawsIdentified_ldpF t +
      integerCF incrementLawsIdentified_ldpF t = 0 := by
  rw [incrementLawsIdentified_ldpF_eq]
  exact ldp_quadratic_of_master
    busemann_ldpF_nonneg busemann_ldpF_hasSum_one
    busemann_ldpG_nonneg busemann_ldpG_hasSum_one
    (busemann_ldpF_symm hsymLdp_ldpCode) busemann_ldpG_zero_of_nonneg
    ldp_master_equation_ldpCode t




theorem lem_nonreal2_identified :
    ∃ delta : ℝ, 0 < delta ∧
      (∀ t ∈ Set.Ioo 0 delta,
        (3 * (integerCF incrementLawsIdentified_ldpF t).re - 1) ^ 2 -
          4 * (integerCF incrementLawsIdentified_ldpF t).re ^ 3 < 0) ∧
      ContinuousOn (ldpHat incrementLawsIdentified_ldpF) (Set.Ioo 0 delta) ∧
      (∀ t ∈ Set.Ioo 0 delta,
        (integerCF incrementLawsIdentified_ldpF t) ^ 2 *
            (ldpHat incrementLawsIdentified_ldpF t) ^ 2 +
          (3 * integerCF incrementLawsIdentified_ldpF t - 1) *
            ldpHat incrementLawsIdentified_ldpF t +
          integerCF incrementLawsIdentified_ldpF t = 0) ∧
      (∀ t ∈ Set.Ioo 0 delta, (ldpHat incrementLawsIdentified_ldpF t).im ≠ 0) := by
  obtain ⟨delta, hdelta, hnonreal⟩ := incrementLawsIdentified_ldp_nonreal
  refine ⟨delta, hdelta, ?_, nonrealIdentified_ldpHat_continuous.continuousOn, ?_, ?_⟩
  · intro t ht
    exact (hnonreal t ht.1 ht.2).1
  · intro t _
    exact nonrealIdentified_ldpHat_root t
  · intro t ht
    exact (hnonreal t ht.1 ht.2).2



private theorem nonrealIdentified_root_im_ne_zero {F : ℝ}
    (hdisc : (3 * F - 1) ^ 2 - 4 * F ^ 3 < 0) {z : ℂ}
    (hq : (F : ℂ) ^ 2 * z ^ 2 + (3 * (F : ℂ) - 1) * z + (F : ℂ) = 0) :
    z.im ≠ 0 := by
  intro hz
  have hr := congrArg Complex.re hq
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.zero_re,
    pow_two, hz, mul_zero, zero_mul, sub_zero, add_zero] at hr
  have hreal : F ^ 2 * z.re ^ 2 + (3 * F - 1) * z.re + F = 0 := by
    nlinarith only [hr]
  have he : (3 * F - 1) ^ 2 - 4 * F ^ 3 =
      (2 * F ^ 2 * z.re + (3 * F - 1)) ^ 2 := by
    calc
      _ = (2 * F ^ 2 * z.re + (3 * F - 1)) ^ 2 -
          4 * F ^ 2 * (F ^ 2 * z.re ^ 2 + (3 * F - 1) * z.re + F) := by ring
      _ = _ := by rw [hreal, mul_zero, sub_zero]
  exact (not_lt_of_ge (he.symm ▸ sq_nonneg (2 * F ^ 2 * z.re + (3 * F - 1)))) hdisc




theorem lem_nonreal2_full_identified :
    ∃ delta : ℝ, 0 < delta ∧
      (∀ t ∈ Set.Ioo 0 delta,
        let F := (integerCF incrementLawsIdentified_ldpF t).re
        (integerCF incrementLawsIdentified_ldpF t).im = 0 ∧
        (3 * F - 1) ^ 2 - 4 * F ^ 3 < 0 ∧
          ∀ z : ℂ, (F : ℂ) ^ 2 * z ^ 2 + (3 * (F : ℂ) - 1) * z + F = 0 →
            z.im ≠ 0) ∧
      ContinuousOn (ldpHat incrementLawsIdentified_ldpF) (Set.Ioo 0 delta) ∧
      (∀ t ∈ Set.Ioo 0 delta,
        let F := (integerCF incrementLawsIdentified_ldpF t).re
        (F : ℂ) ^ 2 * (ldpHat incrementLawsIdentified_ldpF t) ^ 2 +
          (3 * (F : ℂ) - 1) * ldpHat incrementLawsIdentified_ldpF t + F = 0) ∧
      (∀ t ∈ Set.Ioo 0 delta, (ldpHat incrementLawsIdentified_ldpF t).im ≠ 0) ∧
      (∀ alpha beta : ℝ → ℝ,
        ContinuousOn alpha (Set.Ioo 0 delta) → ContinuousOn beta (Set.Ioo 0 delta) →
        (∀ s ∈ Set.Ioo 0 delta,
          let F := (integerCF incrementLawsIdentified_ldpF s).re
          (F : ℂ) ^ 2 * ((alpha s : ℂ) + (beta s : ℂ) * Complex.I) ^ 2 +
            (3 * (F : ℂ) - 1) * ((alpha s : ℂ) + (beta s : ℂ) * Complex.I) + F = 0) →
        ∀ s ∈ Set.Ioo 0 delta, beta s ≠ 0) := by
  obtain ⟨delta, hdelta, hdisc, hcont, _, him⟩ := lem_nonreal2_identified
  have hroots : ∀ t ∈ Set.Ioo 0 delta, ∀ z : ℂ,
      ((integerCF incrementLawsIdentified_ldpF t).re : ℂ) ^ 2 * z ^ 2 +
        (3 * ((integerCF incrementLawsIdentified_ldpF t).re : ℂ) - 1) * z +
        (integerCF incrementLawsIdentified_ldpF t).re = 0 → z.im ≠ 0 := by
    intro t ht z hz
    exact nonrealIdentified_root_im_ne_zero (hdisc t ht) hz
  refine ⟨delta, hdelta, ?_, hcont, ?_, him, ?_⟩
  · intro t ht
    refine ⟨?_, hdisc t ht, hroots t ht⟩
    rw [incrementLawsIdentified_ldpF_eq]
    exact integerCF_im busemann_ldpF_nonneg busemann_ldpF_hasSum_one.summable
      (busemann_ldpF_symm hsymLdp_ldpCode) t
  · intro t _
    have hreal : ((integerCF incrementLawsIdentified_ldpF t).re : ℂ) =
        integerCF incrementLawsIdentified_ldpF t := by
      apply Complex.ext
      · rfl
      · simp only [Complex.ofReal_im]
        rw [incrementLawsIdentified_ldpF_eq]
        exact (integerCF_im busemann_ldpF_nonneg busemann_ldpF_hasSum_one.summable
          (busemann_ldpF_symm hsymLdp_ldpCode) t).symm
    dsimp only
    rw [hreal]
    exact nonrealIdentified_ldpHat_root t
  · intro alpha beta _ _ hbranch s hs
    have hn := hroots s hs ((alpha s : ℂ) + (beta s : ℂ) * Complex.I) (hbranch s hs)
    simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] using hn



theorem nonrealIdentified_sdpHat_continuous :
    Continuous (SDPExpansion.sdpHat incrementLawsIdentified_sdpF
      incrementLawsIdentified_sdpG) := by
  rw [incrementLawsIdentified_sdpF_eq, incrementLawsIdentified_sdpG_eq]
  have hneg := nonrealIdentified_negativeCF_continuous
    busemann_sdpF_nonneg busemann_sdpF_hasSum_one.summable
  have hoff : Continuous (SDPExpansion.sdpOffset
      (SDPMasterFromLaw.sdpF iidCodeMeasure busemannSDPMeasurableVersion)
      (SDPMasterFromLaw.sdpG iidCodeMeasure busemannSDPMeasurableVersion)) := by
    unfold SDPExpansion.sdpOffset
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t
      exact mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)
  exact hneg.add hoff



theorem nonrealIdentified_sdpHat_root (t : ℝ) :
    (SDPExpansion.integerCF incrementLawsIdentified_sdpF t) ^ 2 *
        (SDPExpansion.sdpHat incrementLawsIdentified_sdpF
          incrementLawsIdentified_sdpG t) ^ 2 +
      (3 * SDPExpansion.integerCF incrementLawsIdentified_sdpF t - 1) *
        SDPExpansion.sdpHat incrementLawsIdentified_sdpF incrementLawsIdentified_sdpG t +
      SDPExpansion.integerCF incrementLawsIdentified_sdpF t = 0 := by
  rw [incrementLawsIdentified_sdpF_eq, incrementLawsIdentified_sdpG_eq]
  exact SDPExpansion.sdp_quadratic_of_master
    busemann_sdpF_nonneg busemann_sdpF_hasSum_one
    busemann_sdpG_nonneg busemann_sdpG_hasSum_one
    (busemann_sdpF_symm hsymSdp_sdpCode) busemann_sdpG_zero_below
    sdp_master_equation_sdpCode t

section SDP

local notation "f" => incrementLawsIdentified_sdpF
local notation "g" => incrementLawsIdentified_sdpG
local notation "hat" => SDPExpansion.sdpHat f g
local notation "cf" => SDPExpansion.integerCF f




theorem nonrealIdentified_sdp_full :
    ∃ delta : ℝ, 0 < delta ∧
      (∀ t ∈ Set.Ioo 0 delta,
        let F := (cf t).re
        (cf t).im = 0 ∧
        (3 * F - 1) ^ 2 - 4 * F ^ 3 < 0 ∧
          ∀ z : ℂ, (F : ℂ) ^ 2 * z ^ 2 + (3 * (F : ℂ) - 1) * z + F = 0 →
            z.im ≠ 0) ∧
      ContinuousOn hat (Set.Ioo 0 delta) ∧
      (∀ t ∈ Set.Ioo 0 delta,
        let F := (cf t).re
        (F : ℂ) ^ 2 * (hat t) ^ 2 + (3 * (F : ℂ) - 1) * hat t + F = 0) ∧
      (∀ t ∈ Set.Ioo 0 delta, (hat t).im ≠ 0) ∧
      (∀ alpha beta : ℝ → ℝ,
        ContinuousOn alpha (Set.Ioo 0 delta) → ContinuousOn beta (Set.Ioo 0 delta) →
        (∀ s ∈ Set.Ioo 0 delta,
          let F := (cf s).re
          (F : ℂ) ^ 2 * ((alpha s : ℂ) + (beta s : ℂ) * Complex.I) ^ 2 +
            (3 * (F : ℂ) - 1) * ((alpha s : ℂ) + (beta s : ℂ) * Complex.I) + F = 0) →
        ∀ s ∈ Set.Ioo 0 delta, beta s ≠ 0) := by
  have hf : ∀ k, 0 ≤ f k := by
    rw [incrementLawsIdentified_sdpF_eq]
    exact busemann_sdpF_nonneg
  have hfs : HasSum f 1 := by
    rw [incrementLawsIdentified_sdpF_eq]
    exact busemann_sdpF_hasSum_one
  have hsymm : ∀ k, f (-k) = f k := by
    rw [incrementLawsIdentified_sdpF_eq]
    exact busemann_sdpF_symm hsymSdp_sdpCode
  obtain ⟨delta, hdelta, hdisc⟩ := exists_integer_characteristic_discriminant_neg
    hf hfs hsymm (incrementLawsIdentified_sdp_nondegenerate.1 0)
  have hreal (t : ℝ) (ht : t ∈ Set.Ioo 0 delta) : ((cf t).re : ℂ) = cf t := by
    have him : (cf t).im = 0 := (hdisc t ht.1 ht.2).1
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using him.symm
  have hroot (t : ℝ) (ht : t ∈ Set.Ioo 0 delta) :
      ((cf t).re : ℂ) ^ 2 * (hat t) ^ 2 +
        (3 * ((cf t).re : ℂ) - 1) * hat t + (cf t).re = 0 := by
    rw [hreal t ht]
    exact nonrealIdentified_sdpHat_root t
  have hroots : ∀ t ∈ Set.Ioo 0 delta, ∀ z : ℂ,
      ((cf t).re : ℂ) ^ 2 * z ^ 2 + (3 * ((cf t).re : ℂ) - 1) * z +
        (cf t).re = 0 → z.im ≠ 0 := by
    intro t ht z hz
    exact nonrealIdentified_root_im_ne_zero (hdisc t ht.1 ht.2).2.1 hz
  refine ⟨delta, hdelta, ?_, nonrealIdentified_sdpHat_continuous.continuousOn,
    hroot, ?_, ?_⟩
  · intro t ht
    exact ⟨(hdisc t ht.1 ht.2).1, (hdisc t ht.1 ht.2).2.1, hroots t ht⟩
  · intro t ht
    exact hroots t ht (hat t) (hroot t ht)
  · intro alpha beta _ _ hbranch s hs
    have hn := hroots s hs ((alpha s : ℂ) + (beta s : ℂ) * Complex.I) (hbranch s hs)
    simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] using hn

end SDP

end DirectedDistances.PaperProofs.Section6
