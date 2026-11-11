/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55Assembly12
public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusMeasurableDescent

/-! # Source-law clauses and the remaining Lemma 5.5 reduction

The ordinary rooted planar side classes are those of
measure, both XDP modes, geometric/missing edges and planar relations are
unchanged. Almost-sure presence justifies the arbitrary fixed Option default.

Both same-sign law clauses below have no reader assumptions. Full
at the end of this file. The explicitly named internal reduction is not an
unconditional source theorem or a claim that Lemma 5.5 is complete. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Lemma 5.5 helper: the actual left class is a.e. measurable at every
nonpositive index, using the complete L-minus reader and its proved descent. -/
theorem aemeasurable_lemma55LeftSideClassOption_nonpositive
    (x : XDP) (k : ℤ) (hk : k ≤ 0) :
    AEMeasurable (lemma55LeftSideClassOption x k) wholePlaneIIDCodeMeasure := by
  have hcomp : AEMeasurable
      ((LMinusSidePresentation.classOption4 (x := x)) ∘
        (fun W => decodeLMinus x k (leftSideObsNonpos x k W)))
      wholePlaneIIDCodeMeasure :=
    (aemeasurable_LMinusSidePresentation_classOption4 x k hk).comp_aemeasurable
      (aemeasurable_decodeLMinus_leftSideObsNonpos x k)
  exact hcomp.congr
    (lemma55LeftSideClassOption_ae_eq_LMinusSidePresentation_classOption4 x k hk).symm

/-- Lemma 5.5 helper: the actual right class is a.e. measurable at every
nonnegative index, by the proved R-plus identification. -/
theorem aemeasurable_lemma55RightSideClassOption2_nonnegative
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    AEMeasurable (lemma55RightSideClassOption2 x k) wholePlaneIIDCodeMeasure :=
  (aemeasurable_lemma55RightSideClassOption_nonnegative x k hk).congr
    (lemma55RightSideClassOption2_ae_eq_lemma55RightSideClassOption x k hk).symm

/-- rooted planar side classes through the existing measurable forgetful reader. -/
theorem map_forgetMarksOptionClassValue_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (default : GeometricSideClass) {f g : Ω → Option GeometricSideClass}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hlaw : μ.map f = μ.map g) :
    μ.map (forgetMarksOptionClassValue default ∘ f) =
      μ.map (forgetMarksOptionClassValue default ∘ g) := by
  calc
    _ = (μ.map f).map (forgetMarksOptionClassValue default) :=
      ((measurable_forgetMarksOptionClassValue default).aemeasurable
        |>.map_map_of_aemeasurable hf).symm
    _ = (μ.map g).map (forgetMarksOptionClassValue default) :=
      congrArg (fun ν : Measure (Option GeometricSideClass) =>
        ν.map (forgetMarksOptionClassValue default)) hlaw
    _ = _ := (measurable_forgetMarksOptionClassValue default).aemeasurable
      |>.map_map_of_aemeasurable hg

/-- The right-side stationarity clause of Lemma 5.5, for every nonnegative
integer and either XDP mode, under the actual iid source law. -/
theorem lemma55_unmarked_right_law_eq_zero
    (default : GeometricSideClass) (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    wholePlaneIIDCodeMeasure.map
        (forgetMarksOptionClassValue default ∘ lemma55RightSideClassOption2 x k) =
      wholePlaneIIDCodeMeasure.map
        (forgetMarksOptionClassValue default ∘ lemma55RightSideClassOption2 x 0) := by
  have hlaw : wholePlaneIIDCodeMeasure.map (lemma55RightSideClassOption2 x k) =
      wholePlaneIIDCodeMeasure.map (lemma55RightSideClassOption2 x 0) := by
    calc
      _ = wholePlaneIIDCodeMeasure.map (lemma55RightSideClassOption x k) :=
        Measure.map_congr
          (lemma55RightSideClassOption2_ae_eq_lemma55RightSideClassOption x k hk)
      _ = wholePlaneIIDCodeMeasure.map (lemma55RightSideClassOption x 0) :=
        lemma55_rightLaw_of_sideIdentification x k hk
      _ = _ := (Measure.map_congr
        (lemma55RightSideClassOption2_ae_eq_lemma55RightSideClassOption
          x 0 (le_refl 0))).symm
  exact map_forgetMarksOptionClassValue_eq default
    (aemeasurable_lemma55RightSideClassOption2_nonnegative x k hk)
    (aemeasurable_lemma55RightSideClassOption2_nonnegative x 0 (le_refl 0)) hlaw

/-- The left-side stationarity clause of Lemma 5.5, for every nonpositive
integer and either XDP mode, under the actual iid source law. -/
theorem lemma55_unmarked_left_law_eq_zero
    (default : GeometricSideClass) (x : XDP) (k : ℤ) (hk : k ≤ 0) :
    wholePlaneIIDCodeMeasure.map
        (forgetMarksOptionClassValue default ∘ lemma55LeftSideClassOption x k) =
      wholePlaneIIDCodeMeasure.map
        (forgetMarksOptionClassValue default ∘ lemma55LeftSideClassOption x 0) := by
  let P := fun j : ℤ => fun W => decodeLMinus x j (leftSideObsNonpos x j W)
  let F := LMinusSidePresentation.classOption4 (x := x)
  have hLaw (j : ℤ) (hj : j ≤ 0) :
      wholePlaneIIDCodeMeasure.map (lemma55LeftSideClassOption x j) =
        (wholePlaneIIDCodeMeasure.map (P j)).map F := by
    calc
      _ = wholePlaneIIDCodeMeasure.map (F ∘ P j) :=
        Measure.map_congr
          (lemma55LeftSideClassOption_ae_eq_LMinusSidePresentation_classOption4 x j hj)
      _ = _ :=
        (AEMeasurable.map_map_of_aemeasurable
          (aemeasurable_LMinusSidePresentation_classOption4 x j hj)
          (aemeasurable_decodeLMinus_leftSideObsNonpos x j)).symm
  have hlaw : wholePlaneIIDCodeMeasure.map (lemma55LeftSideClassOption x k) =
      wholePlaneIIDCodeMeasure.map (lemma55LeftSideClassOption x 0) := by
    calc
      _ = (wholePlaneIIDCodeMeasure.map (P k)).map F := hLaw k hk
      _ = (wholePlaneIIDCodeMeasure.map (P 0)).map F :=
        congrArg (fun μ => μ.map F) (decodeLMinus_leftSideObsNonpos_law_eq_zero x k hk)
      _ = _ := (hLaw 0 (le_refl 0)).symm
  exact map_forgetMarksOptionClassValue_eq default
    (aemeasurable_lemma55LeftSideClassOption_nonpositive x k hk)
    (aemeasurable_lemma55LeftSideClassOption_nonpositive x 0 (le_refl 0)) hlaw





theorem lemma55_unmarked_sourceClosure_reduction
    (default : GeometricSideClass)
    (hLplusPos : ∀ (x : XDP) (k : ℤ), 0 < k →
      AEMeasurable (lemma55LeftSideClassOption x k) wholePlaneIIDCodeMeasure)
    (hRminusSource : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
      AEMeasurable (fun W =>
        (decodeRMinus x k (rightSideObsNonpos x k W)).classOption)
        wholePlaneIIDCodeMeasure) :
    ∀ (x : XDP) (k : ℤ),
      IndepFun
        (forgetMarksOptionClassValue default ∘ lemma55LeftSideClassOption x k)
        (forgetMarksOptionClassValue default ∘ lemma55RightSideClassOption2 x k)
        wholePlaneIIDCodeMeasure ∧
      (0 ≤ k → wholePlaneIIDCodeMeasure.map
        (forgetMarksOptionClassValue default ∘ lemma55RightSideClassOption2 x k) =
        wholePlaneIIDCodeMeasure.map
          (forgetMarksOptionClassValue default ∘ lemma55RightSideClassOption2 x 0)) ∧
      (k ≤ 0 → wholePlaneIIDCodeMeasure.map
        (forgetMarksOptionClassValue default ∘ lemma55LeftSideClassOption x k) =
        wholePlaneIIDCodeMeasure.map
          (forgetMarksOptionClassValue default ∘ lemma55LeftSideClassOption x 0)) := by
  have hRminusMeas : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
      AEMeasurable (RMinusSidePresentation.classOption (x := x))
        (wholePlaneIIDCodeMeasure.map (fun W =>
          decodeRMinus x k (rightSideObsNonpos x k W))) := by
    intro x k hk
    exact aemeasurable_RMinusSidePresentation_classOption_of_source
      x k (hRminusSource x k hk) hk
  intro x k
  exact ⟨(lemma55_unmarked_sides_of_LplusPosMeas_RminusMeas
      default hLplusPos hRminusMeas x k).1,
    lemma55_unmarked_right_law_eq_zero default x k,
    lemma55_unmarked_left_law_eq_zero default x k⟩


































end DirectedDistances.PaperProofs.Section5
