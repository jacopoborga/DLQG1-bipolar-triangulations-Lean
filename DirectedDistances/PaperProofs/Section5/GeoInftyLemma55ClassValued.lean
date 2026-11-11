/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55Presence
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55Assembly3




public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: turn an optional geometric-side class into a
class-valued observable using one fixed default for absent values. -/
noncomputable def lemma55OptionClassValue (default : GeometricSideClass)
    (c : Option GeometricSideClass) : GeometricSideClass := c.getD default

/-- Helper toward Lemma 5.5: the fixed-default class reader is measurable for
the optional-class and geometric-class sigma algebras. -/
theorem measurable_lemma55OptionClassValue (default : GeometricSideClass) :
    Measurable (lemma55OptionClassValue default) := by
  rw [measurable_iff_le_map]
  change (inferInstance : MeasurableSpace GeometricSideClass) ≤
    (MeasurableSpace.map (some : GeometricSideClass → Option GeometricSideClass)
      (inferInstance : MeasurableSpace GeometricSideClass)).map
        (lemma55OptionClassValue default)
  rw [MeasurableSpace.map_comp]
  have hcomp : lemma55OptionClassValue default ∘
      (some : GeometricSideClass → Option GeometricSideClass) = id := by
    funext c
    rfl
  rw [hcomp, MeasurableSpace.map_id]

/-- Helper toward Lemma 5.5: embedding a class-valued observable as `some`
and then reading it with the fixed default preserves its law. -/
theorem map_some_lemma55OptionClassValue {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (default : GeometricSideClass)
    (X : Ω → GeometricSideClass) (hX : AEMeasurable X μ) :
    (μ.map (fun ω => some (X ω))).map (lemma55OptionClassValue default) =
      μ.map X := by
  have hsome : AEMeasurable (fun ω => some (X ω)) μ :=
    measurable_some_geometricSideClass.comp_aemeasurable hX
  calc
    (μ.map (fun ω => some (X ω))).map (lemma55OptionClassValue default) =
        μ.map (lemma55OptionClassValue default ∘ (fun ω => some (X ω))) :=
      (measurable_lemma55OptionClassValue default).aemeasurable
        |>.map_map_of_aemeasurable hsome
    _ = μ.map X := rfl

/-- Helper toward Lemma 5.5: the left class observable is almost everywhere
measurable under the AE3 side-identification fields. -/
theorem aemeasurable_lemma55LeftSideClassOption_of_AE3
    (A_L : Lemma55LeftSideObservable)
    (h : Lemma55SideIdentificationAE3 A_L) (x : XDP) (k : ℤ) :
    AEMeasurable (A_L x k) wholePlaneIIDCodeMeasure := by
  by_cases hk : 0 ≤ k
  · let hF := h.aemeasurable_F_Lplus x k hk
    let F := hF.mk (h.F_Lplus x)
    let obs := fun W => decodeLPlusWithIndex x k hk (leftSideObsNonneg x k W)
    have hobs : AEMeasurable obs wholePlaneIIDCodeMeasure :=
      (measurable_decodeLPlusWithIndex x k hk).comp_aemeasurable
        (aemeasurable_leftSideObsNonneg x k)
    have hproxy : AEMeasurable (fun W => F (obs W)) wholePlaneIIDCodeMeasure :=
      hF.measurable_mk.comp_aemeasurable hobs
    have hpull : (h.F_Lplus x) ∘ obs =ᵐ[wholePlaneIIDCodeMeasure] F ∘ obs := by
      exact ae_of_ae_map hobs hF.ae_eq_mk
    have hactual : A_L x k =ᵐ[wholePlaneIIDCodeMeasure] fun W => F (obs W) := by
      exact (h.actual_left_ae_eq_Lplus x k hk).trans hpull
    exact hproxy.congr hactual.symm
  · have hk' : k ≤ 0 := by omega
    let hF := h.aemeasurable_F_Lminus x k hk'
    let F := hF.mk (h.F_Lminus x)
    let obs := fun W => decodeLMinus x k (leftSideObsNonpos x k W)
    have hobs : AEMeasurable obs wholePlaneIIDCodeMeasure :=
      aemeasurable_decodeLMinus_leftSideObsNonpos x k
    have hproxy : AEMeasurable (fun W => F (obs W)) wholePlaneIIDCodeMeasure :=
      hF.measurable_mk.comp_aemeasurable hobs
    have hpull : (h.F_Lminus x) ∘ obs =ᵐ[wholePlaneIIDCodeMeasure] F ∘ obs := by
      exact ae_of_ae_map hobs hF.ae_eq_mk
    have hactual : A_L x k =ᵐ[wholePlaneIIDCodeMeasure] fun W => F (obs W) := by
      exact (h.actual_left_ae_eq_Lminus x k hk').trans hpull
    exact hproxy.congr hactual.symm

/-- Helper toward Lemma 5.5: the actual right optional class observable is
almost everywhere measurable at nonnegative indices. -/
theorem aemeasurable_lemma55RightSideClassOption_nonnegative
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    AEMeasurable (lemma55RightSideClassOption x k) wholePlaneIIDCodeMeasure := by
  cases x with
  | ldp =>
      change AEMeasurable (m0RightSideClassOption true k) wholePlaneIIDCodeMeasure
      exact aemeasurable_m0RightSideClassOption true k hk
  | sdp =>
      change AEMeasurable (m0RightSideClassOption false k) wholePlaneIIDCodeMeasure
      exact aemeasurable_m0RightSideClassOption false k hk

/-- Helper toward Lemma 5.5: the right class observable is almost everywhere
measurable at nonpositive indices under the AE3 side-identification fields. -/
theorem aemeasurable_lemma55RightSideClassOption_nonpositive_of_AE3
    (A_L : Lemma55LeftSideObservable)
    (h : Lemma55SideIdentificationAE3 A_L) (x : XDP) (k : ℤ) (hk : k ≤ 0) :
    AEMeasurable (lemma55RightSideClassOption x k) wholePlaneIIDCodeMeasure := by
  let hF := h.aemeasurable_F_Rminus x k hk
  let F := hF.mk (h.F_Rminus x)
  let obs := fun W => decodeRMinus x k (rightSideObsNonpos x k W)
  have hobs : AEMeasurable obs wholePlaneIIDCodeMeasure :=
    aemeasurable_decodeRMinus_rightSideObsNonpos x k
  have hproxy : AEMeasurable (fun W => F (obs W)) wholePlaneIIDCodeMeasure :=
    hF.measurable_mk.comp_aemeasurable hobs
  have hpull : (h.F_Rminus x) ∘ obs =ᵐ[wholePlaneIIDCodeMeasure] F ∘ obs := by
    exact ae_of_ae_map hobs hF.ae_eq_mk
  have hactual : lemma55RightSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => F (obs W) := by
    exact (h.actual_right_ae_eq_Rminus x k hk).trans hpull
  exact hproxy.congr hactual.symm







theorem lemma55_classValued_of_sideIdentificationAE3
    (A_L : Lemma55LeftSideObservable)
    (h : Lemma55SideIdentificationAE3 A_L)
    (default : GeometricSideClass)
    (hpresentLeft : ∀ (x : XDP) (k : ℤ),
      ∀ᵐ W ∂wholePlaneIIDCodeMeasure, (A_L x k W).isSome)
    (hpresentRightNonpositive : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
      ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        (lemma55RightSideClassOption x k W).isSome) :
    ∀ (x : XDP) (k : ℤ),
      (A_L x k =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => some (lemma55OptionClassValue default (A_L x k W))) ∧
      (lemma55RightSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => some (lemma55OptionClassValue default
          (lemma55RightSideClassOption x k W))) ∧
      IndepFun (fun W => lemma55OptionClassValue default (A_L x k W))
        (fun W => lemma55OptionClassValue default
          (lemma55RightSideClassOption x k W)) wholePlaneIIDCodeMeasure ∧
      (0 ≤ k → wholePlaneIIDCodeMeasure.map
        (fun W => lemma55OptionClassValue default
          (lemma55RightSideClassOption x k W)) =
        wholePlaneIIDCodeMeasure.map
          (fun W => lemma55OptionClassValue default
            (lemma55RightSideClassOption x 0 W))) ∧
      (k ≤ 0 → wholePlaneIIDCodeMeasure.map
        (fun W => lemma55OptionClassValue default (A_L x k W)) =
        wholePlaneIIDCodeMeasure.map
          (fun W => lemma55OptionClassValue default (A_L x 0 W))) := by
  intro x k
  have hpresenceRight : ∀ j : ℤ,
      ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        (lemma55RightSideClassOption x j W).isSome := by
    intro j
    by_cases hj : 0 ≤ j
    · exact ae_lemma55RightSideClassOption_isSome_nonnegative x j hj
    · have hj' : j ≤ 0 := by omega
      exact hpresentRightNonpositive x j hj'
  have hleftRep (j : ℤ) : A_L x j =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => some (lemma55OptionClassValue default (A_L x j W)) := by
    filter_upwards [hpresentLeft x j] with W hW
    cases hval : A_L x j W with
    | none => simp [hval] at hW
    | some c => simp [lemma55OptionClassValue]
  have hrightRep (j : ℤ) : lemma55RightSideClassOption x j =ᵐ[
      wholePlaneIIDCodeMeasure] fun W => some (lemma55OptionClassValue default
        (lemma55RightSideClassOption x j W)) := by
    filter_upwards [hpresenceRight j] with W hW
    cases hval : lemma55RightSideClassOption x j W with
    | none => simp [hval] at hW
    | some c => simp [lemma55OptionClassValue]
  have hbase := lemma55_of_sideIdentificationAE3 A_L h x k
  refine ⟨hleftRep k, hrightRep k, ?_, ?_, ?_⟩
  · have hsomeIndep : IndepFun
        (fun W => some (lemma55OptionClassValue default (A_L x k W)))
        (fun W => some (lemma55OptionClassValue default
          (lemma55RightSideClassOption x k W))) wholePlaneIIDCodeMeasure :=
      hbase.1.congr (hleftRep k) (hrightRep k)
    have hcomp := hsomeIndep.comp
      (measurable_lemma55OptionClassValue default)
      (measurable_lemma55OptionClassValue default)
    have hleftEq : (lemma55OptionClassValue default) ∘
        (fun W => some (lemma55OptionClassValue default (A_L x k W))) =ᵐ[
          wholePlaneIIDCodeMeasure]
        (fun W => lemma55OptionClassValue default (A_L x k W)) := by
      filter_upwards [] with W
      simp [lemma55OptionClassValue]
    have hrightEq : (lemma55OptionClassValue default) ∘
        (fun W => some (lemma55OptionClassValue default
          (lemma55RightSideClassOption x k W))) =ᵐ[wholePlaneIIDCodeMeasure]
        (fun W => lemma55OptionClassValue default
          (lemma55RightSideClassOption x k W)) := by
      filter_upwards [] with W
      simp [lemma55OptionClassValue]
    exact hcomp.congr hleftEq hrightEq
  · intro hk
    have hRk := aemeasurable_lemma55RightSideClassOption_nonnegative x k hk
    have hR0 := aemeasurable_lemma55RightSideClassOption_nonnegative x 0 (by omega)
    let V j := fun W => lemma55OptionClassValue default
      (lemma55RightSideClassOption x j W)
    have hVrepLaw : wholePlaneIIDCodeMeasure.map (fun W => some (V k W)) =
        wholePlaneIIDCodeMeasure.map (fun W => some (V 0 W)) := by
      calc
        wholePlaneIIDCodeMeasure.map (fun W => some (V k W)) =
            wholePlaneIIDCodeMeasure.map (lemma55RightSideClassOption x k) :=
          (Measure.map_congr (hrightRep k)).symm
        _ = wholePlaneIIDCodeMeasure.map (lemma55RightSideClassOption x 0) :=
          hbase.2.1 hk
        _ = wholePlaneIIDCodeMeasure.map (fun W => some (V 0 W)) :=
          Measure.map_congr (hrightRep 0)
    have hVk : AEMeasurable (V k) wholePlaneIIDCodeMeasure :=
      (measurable_lemma55OptionClassValue default).comp_aemeasurable hRk
    have hV0 : AEMeasurable (V 0) wholePlaneIIDCodeMeasure :=
      (measurable_lemma55OptionClassValue default).comp_aemeasurable hR0
    calc
      wholePlaneIIDCodeMeasure.map (V k) =
          (wholePlaneIIDCodeMeasure.map (fun W => some (V k W))).map
            (lemma55OptionClassValue default) :=
        (map_some_lemma55OptionClassValue wholePlaneIIDCodeMeasure default
          (V k) hVk).symm
      _ = (wholePlaneIIDCodeMeasure.map (fun W => some (V 0 W))).map
          (lemma55OptionClassValue default) :=
        congrArg (fun μ : Measure (Option GeometricSideClass) =>
          μ.map (lemma55OptionClassValue default)) hVrepLaw
      _ = wholePlaneIIDCodeMeasure.map (V 0) :=
        map_some_lemma55OptionClassValue wholePlaneIIDCodeMeasure default
          (V 0) hV0
  · intro hk
    have hLk := aemeasurable_lemma55LeftSideClassOption_of_AE3 A_L h x k
    have hL0 := aemeasurable_lemma55LeftSideClassOption_of_AE3 A_L h x 0
    let V j := fun W => lemma55OptionClassValue default (A_L x j W)
    have hVrepLaw : wholePlaneIIDCodeMeasure.map (fun W => some (V k W)) =
        wholePlaneIIDCodeMeasure.map (fun W => some (V 0 W)) := by
      calc
        wholePlaneIIDCodeMeasure.map (fun W => some (V k W)) =
            wholePlaneIIDCodeMeasure.map (A_L x k) :=
          (Measure.map_congr (hleftRep k)).symm
        _ = wholePlaneIIDCodeMeasure.map (A_L x 0) := hbase.2.2 hk
        _ = wholePlaneIIDCodeMeasure.map (fun W => some (V 0 W)) :=
          Measure.map_congr (hleftRep 0)
    have hVk : AEMeasurable (V k) wholePlaneIIDCodeMeasure :=
      (measurable_lemma55OptionClassValue default).comp_aemeasurable hLk
    have hV0 : AEMeasurable (V 0) wholePlaneIIDCodeMeasure :=
      (measurable_lemma55OptionClassValue default).comp_aemeasurable hL0
    calc
      wholePlaneIIDCodeMeasure.map (V k) =
          (wholePlaneIIDCodeMeasure.map (fun W => some (V k W))).map
            (lemma55OptionClassValue default) :=
        (map_some_lemma55OptionClassValue wholePlaneIIDCodeMeasure default
          (V k) hVk).symm
      _ = (wholePlaneIIDCodeMeasure.map (fun W => some (V 0 W))).map
          (lemma55OptionClassValue default) :=
        congrArg (fun μ : Measure (Option GeometricSideClass) =>
          μ.map (lemma55OptionClassValue default)) hVrepLaw
      _ = wholePlaneIIDCodeMeasure.map (V 0) :=
        map_some_lemma55OptionClassValue wholePlaneIIDCodeMeasure default
          (V 0) hV0

end DirectedDistances.PaperProofs.Section5
