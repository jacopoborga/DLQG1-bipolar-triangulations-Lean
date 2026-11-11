/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55Assembly6
public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusDecodedReader4

import all DirectedDistances.PaperProofs.Section5.GeoInftyLemma55ClassValued

/-! Replace the L-plus reader in Assembly 6 by the corrected decoder-4 reader.
This conditional assembly does not close the remaining geometric or
measurability obligations and makes no paper-completion claim. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical



















theorem lemma55_classValued_of_correctedLPlusReader
    (default : GeometricSideClass)
    (hLplusMeas4 : ∀ (x : XDP) (k : ℤ) (_hk : 0 ≤ k),
      AEMeasurable (LPlusSidePresentation.classOptionAt4 x k)
        (wholePlaneIIDCodeMeasure.map (fun W =>
          decodeLPlus x k (leftSideObsNonneg x k W))))
    (hLplusEq4 : ∀ (x : XDP) (k : ℤ) (_hk : 0 ≤ k),
      lemma55LeftSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
        (LPlusSidePresentation.classOptionAt4 x k) ∘ (fun W =>
          decodeLPlus x k (leftSideObsNonneg x k W)))
    (hLminusMeas : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
      AEMeasurable (LMinusSidePresentation.classOption4 (x := x))
        (wholePlaneIIDCodeMeasure.map (fun W =>
          decodeLMinus x k (leftSideObsNonpos x k W))))
    (hRminusMeas : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
      AEMeasurable (RMinusSidePresentation.classOption (x := x))
        (wholePlaneIIDCodeMeasure.map (fun W =>
          decodeRMinus x k (rightSideObsNonpos x k W)))) :
    ∀ (x : XDP) (k : ℤ),
      (lemma55LeftSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => some (lemma55OptionClassValue default
          (lemma55LeftSideClassOption x k W))) ∧
      (lemma55RightSideClassOption2 x k =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => some (lemma55OptionClassValue default
          (lemma55RightSideClassOption2 x k W))) ∧
      IndepFun (fun W => lemma55OptionClassValue default
          (lemma55LeftSideClassOption x k W))
        (fun W => lemma55OptionClassValue default
          (lemma55RightSideClassOption2 x k W)) wholePlaneIIDCodeMeasure ∧
      (0 ≤ k → wholePlaneIIDCodeMeasure.map
        (fun W => lemma55OptionClassValue default
          (lemma55RightSideClassOption2 x k W)) =
        wholePlaneIIDCodeMeasure.map
          (fun W => lemma55OptionClassValue default
            (lemma55RightSideClassOption2 x 0 W))) ∧
      (k ≤ 0 → wholePlaneIIDCodeMeasure.map
        (fun W => lemma55OptionClassValue default
          (lemma55LeftSideClassOption x k W)) =
        wholePlaneIIDCodeMeasure.map
          (fun W => lemma55OptionClassValue default
            (lemma55LeftSideClassOption x 0 W))) := by
  intro x k
  have hIndep : IndepFun (lemma55LeftSideClassOption x k)
      (lemma55RightSideClassOption2 x k) wholePlaneIIDCodeMeasure := by
    by_cases hk : 0 ≤ k
    · let hFL := hLplusMeas4 x k hk
      let FL := hFL.mk (LPlusSidePresentation.classOptionAt4 x k)
      let hPsi := aemeasurable_Psi_rightSideObsNonneg_law x k
      let PsiM := hPsi.mk (Psi x)
      have hLpull :
          (LPlusSidePresentation.classOptionAt4 x k) ∘ (fun W =>
            decodeLPlus x k (leftSideObsNonneg x k W)) =ᵐ[
              wholePlaneIIDCodeMeasure]
          FL ∘ (fun W => decodeLPlus x k (leftSideObsNonneg x k W)) :=
        ae_of_ae_map (aemeasurable_decodeLPlus_leftSideObsNonneg x k)
          hFL.ae_eq_mk
      have hRpull : (Psi x) ∘ (fun W => rightSideObsNonneg x k W) =ᵐ[
          wholePlaneIIDCodeMeasure]
          PsiM ∘ (fun W => rightSideObsNonneg x k W) := by
        filter_upwards [ae_of_ae_map (aemeasurable_boundaryFourObservations x k 2)
          hPsi.ae_eq_mk] with W hW
        exact hW
      have hrightPsi : lemma55RightSideClassOption2 x k =ᵐ[
          wholePlaneIIDCodeMeasure] fun W => Psi x (rightSideObsNonneg x k W) := by
        simpa [Psi, decodeRPlus] using
          lemma55RightSideClassOption2_ae_eq_RPlusPresentationClass x k hk
      exact indepFun_of_ae_eq_comp wholePlaneIIDCodeMeasure
        (fun c => FL (decodeLPlus x k c)) PsiM
        (hFL.measurable_mk.comp (measurable_decodeLPlus x k)) hPsi.measurable_mk
        (leftSideObsNonneg_indep_rightSideObsNonneg x k)
        (by
          filter_upwards [(hLplusEq4 x k hk).trans hLpull] with W hW
          exact hW)
        (by simpa [Function.comp_apply] using hrightPsi.trans hRpull)
    · have hk' : k ≤ 0 := by omega
      let hFL := hLminusMeas x k hk'
      let hFR := hRminusMeas x k hk'
      let FL := hFL.mk (LMinusSidePresentation.classOption4 (x := x))
      let FR := hFR.mk (RMinusSidePresentation.classOption (x := x))
      have hLpull : (LMinusSidePresentation.classOption4 (x := x)) ∘
          (fun W => decodeLMinus x k (leftSideObsNonpos x k W)) =ᵐ[
            wholePlaneIIDCodeMeasure]
          FL ∘ (fun W => decodeLMinus x k (leftSideObsNonpos x k W)) :=
        ae_of_ae_map (aemeasurable_decodeLMinus_leftSideObsNonpos x k)
          hFL.ae_eq_mk
      have hRpull : (RMinusSidePresentation.classOption (x := x)) ∘
          (fun W => decodeRMinus x k (rightSideObsNonpos x k W)) =ᵐ[
            wholePlaneIIDCodeMeasure]
          FR ∘ (fun W => decodeRMinus x k (rightSideObsNonpos x k W)) :=
        ae_of_ae_map (aemeasurable_decodeRMinus_rightSideObsNonpos x k)
          hFR.ae_eq_mk
      have hleft :=
        (lemma55LeftSideClassOption_ae_eq_LMinusSidePresentation_classOption4
          x k hk').trans hLpull
      have hright :=
        (lemma55RightSideClassOption2_ae_eq_RMinusSidePresentation_classOption
          x k hk').trans hRpull
      exact indepFun_of_ae_eq_comp wholePlaneIIDCodeMeasure FL FR
        hFL.measurable_mk hFR.measurable_mk
        (lemma55_nonpos_presentation_indepFun x k)
        (by simpa [Function.comp_apply] using hleft)
        (by simpa [Function.comp_apply] using hright)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [ae_lemma55LeftSideClassOption_isSome x k] with W hW
    cases hval : lemma55LeftSideClassOption x k W with
    | none => simp [hval] at hW
    | some c => rfl
  · filter_upwards [ae_lemma55RightSideClassOption2_isSome x k] with W hW
    cases hval : lemma55RightSideClassOption2 x k W with
    | none => simp [hval] at hW
    | some c => rfl
  · exact hIndep.comp (measurable_lemma55OptionClassValue default)
      (measurable_lemma55OptionClassValue default)
  · intro hk
    have hRlaw : wholePlaneIIDCodeMeasure.map (lemma55RightSideClassOption2 x k) =
        wholePlaneIIDCodeMeasure.map (lemma55RightSideClassOption2 x 0) := by
      calc
        _ = wholePlaneIIDCodeMeasure.map (lemma55RightSideClassOption x k) :=
          Measure.map_congr
            (lemma55RightSideClassOption2_ae_eq_lemma55RightSideClassOption x k hk)
        _ = wholePlaneIIDCodeMeasure.map (lemma55RightSideClassOption x 0) :=
          lemma55_rightLaw_of_sideIdentification x k hk
        _ = _ := (Measure.map_congr
          (lemma55RightSideClassOption2_ae_eq_lemma55RightSideClassOption
            x 0 (by omega))).symm
    have hRmeas (j : ℤ) (hj : 0 ≤ j) :
        AEMeasurable (lemma55RightSideClassOption2 x j) wholePlaneIIDCodeMeasure :=
      (aemeasurable_lemma55RightSideClassOption_nonnegative x j hj).congr
        (lemma55RightSideClassOption2_ae_eq_lemma55RightSideClassOption x j hj).symm
    calc
      _ = (wholePlaneIIDCodeMeasure.map (lemma55RightSideClassOption2 x k)).map
          (lemma55OptionClassValue default) :=
        ((measurable_lemma55OptionClassValue default).aemeasurable
          |>.map_map_of_aemeasurable (hRmeas k hk)).symm
      _ = (wholePlaneIIDCodeMeasure.map (lemma55RightSideClassOption2 x 0)).map
          (lemma55OptionClassValue default) :=
        congrArg (fun μ : Measure (Option GeometricSideClass) =>
          μ.map (lemma55OptionClassValue default)) hRlaw
      _ = _ := (measurable_lemma55OptionClassValue default).aemeasurable
        |>.map_map_of_aemeasurable (hRmeas 0 (by omega))
  · intro hk
    let P := fun j : ℤ => fun W => decodeLMinus x j (leftSideObsNonpos x j W)
    let F := fun r : LMinusSidePresentation x =>
      lemma55OptionClassValue default r.classOption4
    have hF (j : ℤ) (hj : j ≤ 0) :
        AEMeasurable F (wholePlaneIIDCodeMeasure.map (P j)) :=
      (measurable_lemma55OptionClassValue default).comp_aemeasurable
        (hLminusMeas x j hj)
    have hLaw (j : ℤ) (hj : j ≤ 0) :
        wholePlaneIIDCodeMeasure.map (fun W => lemma55OptionClassValue default
          (lemma55LeftSideClassOption x j W)) =
        (wholePlaneIIDCodeMeasure.map (P j)).map F := by
      have heq : (fun W => lemma55OptionClassValue default
          (lemma55LeftSideClassOption x j W)) =ᵐ[wholePlaneIIDCodeMeasure]
          F ∘ P j := by
        filter_upwards [lemma55LeftSideClassOption_ae_eq_LMinusSidePresentation_classOption4
          x j hj] with W hW
        exact congrArg (lemma55OptionClassValue default) hW
      calc
        _ = wholePlaneIIDCodeMeasure.map (F ∘ P j) := Measure.map_congr heq
        _ = _ := (AEMeasurable.map_map_of_aemeasurable (hF j hj)
          (aemeasurable_decodeLMinus_leftSideObsNonpos x j)).symm
    calc
      _ = (wholePlaneIIDCodeMeasure.map (P k)).map F := hLaw k hk
      _ = (wholePlaneIIDCodeMeasure.map (P 0)).map F :=
        congrArg (fun μ => μ.map F)
          (decodeLMinus_leftSideObsNonpos_law_eq_zero x k hk)
      _ = _ := (hLaw 0 (by omega)).symm





















































end DirectedDistances.PaperProofs.Section5

/- Validation: the temporary axiom probe for
lemma55_classValued_of_correctedLPlusReader reported exactly
[propext, Classical.choice, Quot.sound]; the probe was removed. -/
