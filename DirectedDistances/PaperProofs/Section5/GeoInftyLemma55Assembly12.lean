/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSide4CrossWitness5
public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusPairMeasurable2
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55ForgetMarks

 

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: the five class-valued clauses follow from
positive-index left measurability and nonpositive-index right measurability. -/
theorem lemma55_classValued_of_LplusPosMeas_RminusMeas
    (default : GeometricSideClass)
    (hLplusPos : ∀ (x : XDP) (k : ℤ), 0 < k →
      AEMeasurable (lemma55LeftSideClassOption x k) wholePlaneIIDCodeMeasure)
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
  have hcross : ∀ (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
      (s : LPlusSourceWitnessAligned x k r)
      (s' : LPlusSourceWitnessAligned x k r') (hk : 0 ≤ k)
      (hr : r.code = r'.code),
      geometricSideClass
        (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) =
      geometricSideClass
        (lPlusCodeBlockSide4 s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin
          s'.hleft hk) := by
    intro x k r r' s s' hk hr
    exact lPlusCodeBlockSide4_class_eq_of_presentation_codes_eq
      x k r r' s s' hk hr
  have hLplusMeasActual : ∀ (x : XDP) (k : ℤ) (_hk : 0 ≤ k),
      AEMeasurable (lemma55LeftSideClassOption x k) wholePlaneIIDCodeMeasure := by
    intro x k hk
    by_cases hpos : 0 < k
    · exact hLplusPos x k hpos
    · have hk0 : k = 0 := by omega
      subst k
      exact aemeasurable_lemma55LeftSideClassOption_zero x
  have hLminusMeas : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
      AEMeasurable (LMinusSidePresentation.classOption4 (x := x))
        (wholePlaneIIDCodeMeasure.map (fun W =>
          decodeLMinus x k (leftSideObsNonpos x k W))) := by
    intro x k hk
    exact aemeasurable_LMinusSidePresentation_classOption4 x k hk
  exact lemma55_classValued_of_LPlusReader5 default hcross
    hLplusMeasActual hRminusMeas

/-- Helper toward Lemma 5.5: the unmarked source-shaped independence and
same-sign laws follow from positive-index left and nonpositive-index right
measurability. -/
theorem lemma55_unmarked_sides_of_LplusPosMeas_RminusMeas
    (default : GeometricSideClass)
    (hLplusPos : ∀ (x : XDP) (k : ℤ), 0 < k →
      AEMeasurable (lemma55LeftSideClassOption x k) wholePlaneIIDCodeMeasure)
    (hRminusMeas : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
      AEMeasurable (RMinusSidePresentation.classOption (x := x))
        (wholePlaneIIDCodeMeasure.map (fun W =>
          decodeRMinus x k (rightSideObsNonpos x k W)))) :
    ∀ (x : XDP) (k : ℤ),
      IndepFun
        (forgetMarksOptionClassValue default ∘ lemma55LeftSideClassOption x k)
        (forgetMarksOptionClassValue default ∘ lemma55RightSideClassOption2 x k)
        wholePlaneIIDCodeMeasure ∧
      (0 ≤ k →
        wholePlaneIIDCodeMeasure.map
          (forgetMarksOptionClassValue default ∘ lemma55RightSideClassOption2 x k) =
        wholePlaneIIDCodeMeasure.map
          (forgetMarksOptionClassValue default ∘ lemma55RightSideClassOption2 x 0)) ∧
      (k ≤ 0 →
        wholePlaneIIDCodeMeasure.map
          (forgetMarksOptionClassValue default ∘ lemma55LeftSideClassOption x k) =
        wholePlaneIIDCodeMeasure.map
          (forgetMarksOptionClassValue default ∘ lemma55LeftSideClassOption x 0)) := by
  have hclass := lemma55_classValued_of_LplusPosMeas_RminusMeas
    default hLplusPos hRminusMeas
  have hLplusMeasActual : ∀ (x : XDP) (k : ℤ) (_hk : 0 ≤ k),
      AEMeasurable (lemma55LeftSideClassOption x k) wholePlaneIIDCodeMeasure := by
    intro x k hk
    by_cases hpos : 0 < k
    · exact hLplusPos x k hpos
    · have hk0 : k = 0 := by omega
      subst k
      exact aemeasurable_lemma55LeftSideClassOption_zero x
  have hLminusMeas : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
      AEMeasurable (LMinusSidePresentation.classOption4 (x := x))
        (wholePlaneIIDCodeMeasure.map (fun W =>
          decodeLMinus x k (leftSideObsNonpos x k W))) := by
    intro x k hk
    exact aemeasurable_LMinusSidePresentation_classOption4 x k hk
  intro x k
  have hassembly := hclass x k
  have hLoption : AEMeasurable (lemma55LeftSideClassOption x k)
      wholePlaneIIDCodeMeasure := by
    by_cases hk : 0 ≤ k
    · exact hLplusMeasActual x k hk
    · have hk' : k ≤ 0 := by omega
      let obs := fun W => decodeLMinus x k (leftSideObsNonpos x k W)
      have hcomp : AEMeasurable
          ((LMinusSidePresentation.classOption4 (x := x)) ∘ obs)
          wholePlaneIIDCodeMeasure :=
        (hLminusMeas x k hk').comp_aemeasurable
          (aemeasurable_decodeLMinus_leftSideObsNonpos x k)
      exact hcomp.congr
        (lemma55LeftSideClassOption_ae_eq_LMinusSidePresentation_classOption4
          x k hk').symm
  have hRoption : AEMeasurable (lemma55RightSideClassOption2 x k)
      wholePlaneIIDCodeMeasure := by
    by_cases hk : 0 ≤ k
    · exact (aemeasurable_lemma55RightSideClassOption_nonnegative x k hk).congr
        (lemma55RightSideClassOption2_ae_eq_lemma55RightSideClassOption x k hk).symm
    · have hk' : k ≤ 0 := by omega
      let obs := fun W => decodeRMinus x k (rightSideObsNonpos x k W)
      have hcomp : AEMeasurable
          ((RMinusSidePresentation.classOption (x := x)) ∘ obs)
          wholePlaneIIDCodeMeasure :=
        (hRminusMeas x k hk').comp_aemeasurable
          (aemeasurable_decodeRMinus_rightSideObsNonpos x k)
      exact hcomp.congr
        (lemma55RightSideClassOption2_ae_eq_RMinusSidePresentation_classOption
          x k hk').symm
  have hLvalue : AEMeasurable
      (fun W => lemma55OptionClassValue default
        (lemma55LeftSideClassOption x k W)) wholePlaneIIDCodeMeasure :=
    (measurable_lemma55OptionClassValue default).comp_aemeasurable hLoption
  have hRvalue : AEMeasurable
      (fun W => lemma55OptionClassValue default
        (lemma55RightSideClassOption2 x k W)) wholePlaneIIDCodeMeasure :=
    (measurable_lemma55OptionClassValue default).comp_aemeasurable hRoption
  refine ⟨?_, ?_, ?_⟩
  · simpa [forgetMarksOptionClassValue, Function.comp_def] using
      indepFun_forgetMarks hassembly.2.2.1
  · intro hk
    have hRzeroOption : AEMeasurable (lemma55RightSideClassOption2 x 0)
        wholePlaneIIDCodeMeasure :=
      (aemeasurable_lemma55RightSideClassOption_nonnegative x 0 (by omega)).congr
        (lemma55RightSideClassOption2_ae_eq_lemma55RightSideClassOption
          x 0 (by omega)).symm
    have hRzero : AEMeasurable
        (fun W => lemma55OptionClassValue default
          (lemma55RightSideClassOption2 x 0 W)) wholePlaneIIDCodeMeasure :=
      (measurable_lemma55OptionClassValue default).comp_aemeasurable hRzeroOption
    simpa [forgetMarksOptionClassValue, Function.comp_def] using
      map_forgetMarks_eq hRvalue hRzero (hassembly.2.2.2.1 hk)
  · intro hk
    have hLzeroOption : AEMeasurable (lemma55LeftSideClassOption x 0)
        wholePlaneIIDCodeMeasure := hLplusMeasActual x 0 (by omega)
    have hLzero : AEMeasurable
        (fun W => lemma55OptionClassValue default
          (lemma55LeftSideClassOption x 0 W)) wholePlaneIIDCodeMeasure :=
      (measurable_lemma55OptionClassValue default).comp_aemeasurable hLzeroOption
    simpa [forgetMarksOptionClassValue, Function.comp_def] using
      map_forgetMarks_eq hLvalue hLzero (hassembly.2.2.2.2 hk)

end DirectedDistances.PaperProofs.Section5
