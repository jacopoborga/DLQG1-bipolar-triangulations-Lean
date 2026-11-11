/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55Assembly4
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55LeftObservable

/-! Transfer fixed-index L-plus measurability to the indexed presentation law,
then instantiate the actual-left observable. The remaining geometric and
measurability obligations stay explicit; this is not a proof of Lemma 5.5. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: fixed-index class-reader measurability in the
exact shape recorded at `GeoInftyLemma55FMapsAE.lean:256–260` implies the
indexed shape used by `GeoInftyLemma55Assembly4.lean:99–102`. The indexed
observation law is supported on the measurable fiber with boundary index
`k`, where the readers agree. No additional hypothesis is needed. -/
theorem aemeasurable_LPlusIndexedSidePresentation_classOption_of_classOptionAt
    (x : XDP) (k : ℤ) (hk : 0 ≤ k)
    (hMeas : AEMeasurable (LPlusSidePresentation.classOptionAt x k)
      (wholePlaneIIDCodeMeasure.map (fun W =>
        decodeLPlus x k (leftSideObsNonneg x k W)))) :
    AEMeasurable (LPlusIndexedSidePresentation.classOption x)
      (wholePlaneIIDCodeMeasure.map (fun W =>
        decodeLPlusWithIndex x k hk (leftSideObsNonneg x k W))) := by
  let oldObs := fun W => decodeLPlus x k (leftSideObsNonneg x k W)
  let indexedObs := fun W =>
    decodeLPlusWithIndex x k hk (leftSideObsNonneg x k W)
  have hindexedObs : AEMeasurable indexedObs wholePlaneIIDCodeMeasure :=
    (measurable_decodeLPlusWithIndex x k hk).comp_aemeasurable
      (aemeasurable_leftSideObsNonneg x k)
  have hprojection :
      (wholePlaneIIDCodeMeasure.map indexedObs).map
          (fun r : LPlusIndexedSidePresentation x => r.presentation) =
        wholePlaneIIDCodeMeasure.map oldObs := by
    rw [AEMeasurable.map_map_of_aemeasurable
      (measurable_LPlusIndexedSidePresentation_presentation x).aemeasurable
      hindexedObs]
    rfl
  have hold : AEMeasurable (LPlusSidePresentation.classOptionAt x k)
      ((wholePlaneIIDCodeMeasure.map indexedObs).map
        (fun r : LPlusIndexedSidePresentation x => r.presentation)) := by
    rw [hprojection]
    exact hMeas
  have hfixed : AEMeasurable
      (fun r : LPlusIndexedSidePresentation x =>
        LPlusSidePresentation.classOptionAt x k r.presentation)
      (wholePlaneIIDCodeMeasure.map indexedObs) :=
    hold.comp_aemeasurable
      (measurable_LPlusIndexedSidePresentation_presentation x).aemeasurable
  have hindex : Measurable
      (fun r : LPlusIndexedSidePresentation x => r.boundaryIndex) :=
    measurable_fst.comp (comap_measurable _)
  have hfiber : ∀ᵐ r ∂wholePlaneIIDCodeMeasure.map indexedObs,
      r.boundaryIndex = k := by
    apply (ae_map_iff hindexedObs
      (measurableSet_eq_fun hindex measurable_const)).mpr
    exact Filter.Eventually.of_forall (fun _ => rfl)
  apply hfixed.congr
  filter_upwards [hfiber] with r hr
  rw [LPlusIndexedSidePresentation.classOption_eq_classOptionAt, hr]

/-- Helper toward Lemma 5.5: the five-clause class-valued conclusion of
`lemma55_classValued_of_corrected_readers`, for the unfoldable actual-left
observable. Its L-minus equality and left presence come from
`GeoInftyLemma55LeftObservable.lean:82–86` and `:67–69`; right presence is
discharged using `GeoInftyLemma55Assembly4.lean:57–67`.

The five remaining hypotheses, with their exact obligation records, are:
* `hLplusMeas`: `GeoInftyLemma55FMapsAE.lean:256–260` (unindexed shape).
* `hLplusEq`: `GeoInftyLemma55Assembly3.lean:74–77`, with the named
  indexed reader and `A_L := lemma55LeftSideClassOption`.
* `hLminusMeas`: `GeoInftyLMinusDecodedSide5.lean:429–433` (decoder 4).
* `hRminusMeas`: `GeoInftyLemma55FMapsAE3.lean:38–43`.
* `hRminusEq`: `GeoInftyNonposRightSideWhole4.lean:114–118`.

These obligations remain hypotheses; this helper makes no paper-completion
claim and assumes no independence or equality of laws. -/
theorem lemma55_classValued_of_leftObservable
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
    (hRminusEq : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
      lemma55RightSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
        (RMinusSidePresentation.classOption (x := x)) ∘ (fun W =>
          decodeRMinus x k (rightSideObsNonpos x k W))) :
    ∀ (x : XDP) (k : ℤ),
      (lemma55LeftSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => some (lemma55OptionClassValue default
          (lemma55LeftSideClassOption x k W))) ∧
      (lemma55RightSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => some (lemma55OptionClassValue default
          (lemma55RightSideClassOption x k W))) ∧
      IndepFun (fun W => lemma55OptionClassValue default
          (lemma55LeftSideClassOption x k W))
        (fun W => lemma55OptionClassValue default
          (lemma55RightSideClassOption x k W)) wholePlaneIIDCodeMeasure ∧
      (0 ≤ k → wholePlaneIIDCodeMeasure.map
        (fun W => lemma55OptionClassValue default
          (lemma55RightSideClassOption x k W)) =
        wholePlaneIIDCodeMeasure.map
          (fun W => lemma55OptionClassValue default
            (lemma55RightSideClassOption x 0 W))) ∧
      (k ≤ 0 → wholePlaneIIDCodeMeasure.map
        (fun W => lemma55OptionClassValue default
          (lemma55LeftSideClassOption x k W)) =
        wholePlaneIIDCodeMeasure.map
          (fun W => lemma55OptionClassValue default
            (lemma55LeftSideClassOption x 0 W))) := by
  let h : Lemma55SideIdentificationAE3 lemma55LeftSideClassOption :=
    { F_Lplus := LPlusIndexedSidePresentation.classOption
      aemeasurable_F_Lplus := fun x k hk =>
        aemeasurable_LPlusIndexedSidePresentation_classOption_of_classOptionAt
          x k hk (hLplusMeas x k hk)
      actual_left_ae_eq_Lplus := hLplusEq
      F_Lminus := fun _ => LMinusSidePresentation.classOption4
      aemeasurable_F_Lminus := hLminusMeas
      actual_left_ae_eq_Lminus :=
        lemma55LeftSideClassOption_ae_eq_LMinusSidePresentation_classOption4
      F_Rminus := fun _ => RMinusSidePresentation.classOption
      aemeasurable_F_Rminus := hRminusMeas
      actual_right_ae_eq_Rminus := hRminusEq }
  apply lemma55_classValued_of_sideIdentificationAE3
    lemma55LeftSideClassOption h default ae_lemma55LeftSideClassOption_isSome
  intro x k hk
  exact ae_lemma55RightSideClassOption_isSome_of_RMinus_eq x k hk (hRminusEq x k hk)

end DirectedDistances.PaperProofs.Section5
