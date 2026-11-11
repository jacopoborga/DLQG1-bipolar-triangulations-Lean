/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55Assembly5
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55RightObservable

-- Access the existing fixed-default reader body for its `some` equation.
import all DirectedDistances.PaperProofs.Section5.GeoInftyLemma55ClassValued

/-! Assemble the exposed actual-side observables. Four inherited obligations
remain explicit; no numbered paper result is claimed complete here. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: the five-clause class-valued conclusion for
`lemma55LeftSideClassOption` and `lemma55RightSideClassOption2`. Both presence
conditions and both nonpositive identifications are discharged by the exposed
observables. The nonnegative right-law clause is transferred from the
original reader by its proved almost-everywhere agreement.

Complete remaining hypothesis records:
* `hLplusMeas`: `GeoInftyLemma55FMapsAE.lean:256–260`.
* `hLplusEq`: `GeoInftyLemma55Assembly3.lean:74–77`, specialized to the
  exposed left observable and the indexed class reader.
* `hLminusMeas`: `GeoInftyLMinusDecodedSide5.lean:429–433` (decoder 4).
* `hRminusMeas`: `GeoInftyLemma55FMapsAE3.lean:38–43`.

These are inherited open obligations, not proved premises or an assertion -/
theorem lemma55_classValued_of_exposedObservables
    (default : GeometricSideClass)
    (hLplusMeas : ∀ (x : XDP) (k : ℤ) (_hk : 0 ≤ k),
      AEMeasurable (LPlusSidePresentation.classOptionAt x k)
        (wholePlaneIIDCodeMeasure.map (fun W =>
          decodeLPlus x k (leftSideObsNonneg x k W))))
    (hLplusEq : ∀ (x : XDP) (k : ℤ) (hk : 0 ≤ k),
      lemma55LeftSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
        (LPlusIndexedSidePresentation.classOption x) ∘ (fun W =>
          decodeLPlusWithIndex x k hk (leftSideObsNonneg x k W)))
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
    · let hFL :=
        aemeasurable_LPlusIndexedSidePresentation_classOption_of_classOptionAt
          x k hk (hLplusMeas x k hk)
      let FL := hFL.mk (LPlusIndexedSidePresentation.classOption x)
      let hPsi := aemeasurable_Psi_rightSideObsNonneg_law x k
      let PsiM := hPsi.mk (Psi x)
      have hDecode := measurable_decodeLPlusWithIndex x k hk
      have hLpull :
          (LPlusIndexedSidePresentation.classOption x) ∘ (fun W =>
            decodeLPlusWithIndex x k hk (leftSideObsNonneg x k W)) =ᵐ[
              wholePlaneIIDCodeMeasure]
          FL ∘ (fun W =>
            decodeLPlusWithIndex x k hk (leftSideObsNonneg x k W)) :=
        ae_of_ae_map (hDecode.comp_aemeasurable
          (aemeasurable_leftSideObsNonneg x k)) hFL.ae_eq_mk
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
        (fun c => FL (decodeLPlusWithIndex x k hk c)) PsiM
        (hFL.measurable_mk.comp hDecode) hPsi.measurable_mk
        (leftSideObsNonneg_indep_rightSideObsNonneg x k)
        (by
          filter_upwards [(hLplusEq x k hk).trans hLpull] with W hW
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

/-- Helper toward Lemma 5.5: transfer the nonnegative right-law clause back
to the original right observable using the proved a.e. agreement in
`GeoInftyLemma55RightObservable.lean:181–209`. The four hypotheses have
exactly the records listed for `lemma55_classValued_of_exposedObservables`:
FMapsAE:256, Assembly3:74, LMinusDecodedSide5:429, and FMapsAE3:38.
No law equality is assumed as an additional premise. -/
theorem lemma55_classValued_rightLaw_of_exposedObservables
    (default : GeometricSideClass)
    (hLplusMeas : ∀ (x : XDP) (k : ℤ) (_hk : 0 ≤ k),
      AEMeasurable (LPlusSidePresentation.classOptionAt x k)
        (wholePlaneIIDCodeMeasure.map (fun W =>
          decodeLPlus x k (leftSideObsNonneg x k W))))
    (hLplusEq : ∀ (x : XDP) (k : ℤ) (hk : 0 ≤ k),
      lemma55LeftSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
        (LPlusIndexedSidePresentation.classOption x) ∘ (fun W =>
          decodeLPlusWithIndex x k hk (leftSideObsNonneg x k W)))
    (hLminusMeas : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
      AEMeasurable (LMinusSidePresentation.classOption4 (x := x))
        (wholePlaneIIDCodeMeasure.map (fun W =>
          decodeLMinus x k (leftSideObsNonpos x k W))))
    (hRminusMeas : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
      AEMeasurable (RMinusSidePresentation.classOption (x := x))
        (wholePlaneIIDCodeMeasure.map (fun W =>
          decodeRMinus x k (rightSideObsNonpos x k W))))
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    wholePlaneIIDCodeMeasure.map
      (fun W => lemma55OptionClassValue default (lemma55RightSideClassOption x k W)) =
    wholePlaneIIDCodeMeasure.map
      (fun W => lemma55OptionClassValue default (lemma55RightSideClassOption x 0 W)) := by
  have heq (j : ℤ) (hj : 0 ≤ j) :
      (fun W => lemma55OptionClassValue default
        (lemma55RightSideClassOption2 x j W)) =ᵐ[wholePlaneIIDCodeMeasure]
      (fun W => lemma55OptionClassValue default
        (lemma55RightSideClassOption x j W)) := by
    filter_upwards [lemma55RightSideClassOption2_ae_eq_lemma55RightSideClassOption
      x j hj] with W hW
    exact congrArg (lemma55OptionClassValue default) hW
  calc
    _ = wholePlaneIIDCodeMeasure.map (fun W => lemma55OptionClassValue default
        (lemma55RightSideClassOption2 x k W)) :=
      (Measure.map_congr (heq k hk)).symm
    _ = wholePlaneIIDCodeMeasure.map (fun W => lemma55OptionClassValue default
        (lemma55RightSideClassOption2 x 0 W)) :=
      (lemma55_classValued_of_exposedObservables default hLplusMeas hLplusEq
        hLminusMeas hRminusMeas x k).2.2.2.1 hk
    _ = _ := Measure.map_congr (heq 0 (by omega))



















































end DirectedDistances.PaperProofs.Section5
