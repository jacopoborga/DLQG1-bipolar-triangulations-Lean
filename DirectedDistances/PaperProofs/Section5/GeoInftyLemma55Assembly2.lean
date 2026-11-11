/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55Assembly
public import DirectedDistances.PaperProofs.Section5.GeoInftyRPlusMeasurableClass3





public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local notation "Code" => (ℕ → Fin 3) × (ℕ → Option FiniteThinMap) × (ℕ → Fin 3)






structure Lemma55SideIdentificationAE (A_L : Lemma55LeftSideObservable) where
  F_Lplus : ∀ x : XDP, LPlusSidePresentation x → Option GeometricSideClass
  aemeasurable_F_Lplus : ∀ (x : XDP) (k : ℤ), 0 ≤ k →
    AEMeasurable (F_Lplus x) (wholePlaneIIDCodeMeasure.map
      (fun W => decodeLPlus x k (leftSideObsNonneg x k W)))
  actual_left_ae_eq_Lplus : ∀ (x : XDP) (k : ℤ), 0 ≤ k →
    A_L x k =ᵐ[wholePlaneIIDCodeMeasure]
      (F_Lplus x) ∘ (fun W => decodeLPlus x k (leftSideObsNonneg x k W))
  F_Lminus : ∀ x : XDP, LMinusSidePresentation x → Option GeometricSideClass
  aemeasurable_F_Lminus : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
    AEMeasurable (F_Lminus x) (wholePlaneIIDCodeMeasure.map
      (fun W => decodeLMinus x k (leftSideObsNonpos x k W)))
  actual_left_ae_eq_Lminus : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
    A_L x k =ᵐ[wholePlaneIIDCodeMeasure]
      (F_Lminus x) ∘ (fun W => decodeLMinus x k (leftSideObsNonpos x k W))
  F_Rminus : ∀ x : XDP, RMinusSidePresentation x → Option GeometricSideClass
  aemeasurable_F_Rminus : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
    AEMeasurable (F_Rminus x) (wholePlaneIIDCodeMeasure.map
      (fun W => decodeRMinus x k (rightSideObsNonpos x k W)))
  actual_right_ae_eq_Rminus : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
    lemma55RightSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
      (F_Rminus x) ∘ (fun W => decodeRMinus x k (rightSideObsNonpos x k W))

/-- Helper toward Lemma 5.5: convert the measurable side identifications to
their almost everywhere measurable form. The resulting structure still
records open side identifications and does not prove Lemma 5.5. -/
def Lemma55SideIdentification.toAE
    {A_L : Lemma55LeftSideObservable} (h : Lemma55SideIdentification A_L) :
    Lemma55SideIdentificationAE A_L where
  F_Lplus := h.F_Lplus
  aemeasurable_F_Lplus := fun x _ _ => (h.measurable_F_Lplus x).aemeasurable
  actual_left_ae_eq_Lplus := h.actual_left_ae_eq_Lplus
  F_Lminus := h.F_Lminus
  aemeasurable_F_Lminus := fun x _ _ => (h.measurable_F_Lminus x).aemeasurable
  actual_left_ae_eq_Lminus := h.actual_left_ae_eq_Lminus
  F_Rminus := h.F_Rminus
  aemeasurable_F_Rminus := fun x _ _ => (h.measurable_F_Rminus x).aemeasurable
  actual_right_ae_eq_Rminus := h.actual_right_ae_eq_Rminus




theorem lemma55_of_sideIdentificationAE
    (A_L : Lemma55LeftSideObservable)
    (h : Lemma55SideIdentificationAE A_L) :
    ∀ (x : XDP) (k : ℤ),
      IndepFun (A_L x k) (lemma55RightSideClassOption x k)
        wholePlaneIIDCodeMeasure ∧
      (0 ≤ k → wholePlaneIIDCodeMeasure.map (lemma55RightSideClassOption x k) =
        wholePlaneIIDCodeMeasure.map (lemma55RightSideClassOption x 0)) ∧
      (k ≤ 0 → wholePlaneIIDCodeMeasure.map (A_L x k) =
        wholePlaneIIDCodeMeasure.map (A_L x 0)) := by
  intro x k
  refine ⟨?_, ?_, ?_⟩
  · by_cases hk : 0 ≤ k
    · let hFL := h.aemeasurable_F_Lplus x k hk
      let FL := hFL.mk (h.F_Lplus x)
      let hPsi := aemeasurable_Psi_rightSideObsNonneg_law x k
      let PsiM := hPsi.mk (Psi x)
      have hLpull :
          (h.F_Lplus x) ∘ (fun W => decodeLPlus x k (leftSideObsNonneg x k W)) =ᵐ[
            wholePlaneIIDCodeMeasure]
          FL ∘ (fun W => decodeLPlus x k (leftSideObsNonneg x k W)) := by
        exact ae_of_ae_map (aemeasurable_decodeLPlus_leftSideObsNonneg x k)
          hFL.ae_eq_mk
      have hRpull :
          (Psi x) ∘ (fun W => rightSideObsNonneg x k W) =ᵐ[
            wholePlaneIIDCodeMeasure]
          PsiM ∘ (fun W => rightSideObsNonneg x k W) := by
        filter_upwards [ae_of_ae_map (aemeasurable_boundaryFourObservations x k 2)
          hPsi.ae_eq_mk] with W hW
        exact hW
      have hleft : A_L x k =ᵐ[wholePlaneIIDCodeMeasure]
          FL ∘ (fun W => decodeLPlus x k (leftSideObsNonneg x k W)) :=
        (h.actual_left_ae_eq_Lplus x k hk).trans hLpull
      have hrightPsi : lemma55RightSideClassOption x k =ᵐ[
          wholePlaneIIDCodeMeasure] fun W => Psi x (rightSideObsNonneg x k W) := by
        cases x with
        | ldp =>
            change m0RightSideClassOption true k =ᵐ[wholePlaneIIDCodeMeasure]
              (fun W => Psi XDP.ldp (rightSideObsNonneg XDP.ldp k W))
            simpa [Psi, decodeRPlus] using
              (m0RightSideClassOption_ae_eq_RPlusPresentationClass true k hk)
        | sdp =>
            change m0RightSideClassOption false k =ᵐ[wholePlaneIIDCodeMeasure]
              (fun W => Psi XDP.sdp (rightSideObsNonneg XDP.sdp k W))
            simpa [Psi, decodeRPlus] using
              (m0RightSideClassOption_ae_eq_RPlusPresentationClass false k hk)
      have hright : lemma55RightSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
          PsiM ∘ (fun W => rightSideObsNonneg x k W) := by
        exact hrightPsi.trans hRpull
      have hFLmeas : Measurable
          (fun c => FL (decodeLPlus x k c)) :=
        hFL.measurable_mk.comp (measurable_decodeLPlus x k)
      exact indepFun_of_ae_eq_comp wholePlaneIIDCodeMeasure
        (fun c => FL (decodeLPlus x k c)) PsiM
        hFLmeas hPsi.measurable_mk
        (leftSideObsNonneg_indep_rightSideObsNonneg x k)
        (by
          filter_upwards [hleft] with W hW
          exact hW)
        (by simpa [Function.comp_apply] using hright)
    · have hk' : k ≤ 0 := by omega
      let hFL := h.aemeasurable_F_Lminus x k hk'
      let hFR := h.aemeasurable_F_Rminus x k hk'
      let FL := hFL.mk (h.F_Lminus x)
      let FR := hFR.mk (h.F_Rminus x)
      have hLpull :
          (h.F_Lminus x) ∘ (fun W => decodeLMinus x k (leftSideObsNonpos x k W)) =ᵐ[
            wholePlaneIIDCodeMeasure]
          FL ∘ (fun W => decodeLMinus x k (leftSideObsNonpos x k W)) := by
        exact ae_of_ae_map (aemeasurable_decodeLMinus_leftSideObsNonpos x k)
          hFL.ae_eq_mk
      have hRpull :
          (h.F_Rminus x) ∘ (fun W => decodeRMinus x k (rightSideObsNonpos x k W)) =ᵐ[
            wholePlaneIIDCodeMeasure]
          FR ∘ (fun W => decodeRMinus x k (rightSideObsNonpos x k W)) := by
        exact ae_of_ae_map (aemeasurable_decodeRMinus_rightSideObsNonpos x k)
          hFR.ae_eq_mk
      have hleft : A_L x k =ᵐ[wholePlaneIIDCodeMeasure]
          FL ∘ (fun W => decodeLMinus x k (leftSideObsNonpos x k W)) :=
        (h.actual_left_ae_eq_Lminus x k hk').trans hLpull
      have hright : lemma55RightSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
          FR ∘ (fun W => decodeRMinus x k (rightSideObsNonpos x k W)) :=
        (h.actual_right_ae_eq_Rminus x k hk').trans hRpull
      exact indepFun_of_ae_eq_comp wholePlaneIIDCodeMeasure FL FR
        hFL.measurable_mk hFR.measurable_mk
        (lemma55_nonpos_presentation_indepFun x k)
        (by simpa [Function.comp_apply] using hleft)
        (by simpa [Function.comp_apply] using hright)
  · intro hk
    exact lemma55_rightLaw_of_sideIdentification x k hk
  · intro hk
    let P := fun j : ℤ =>
      fun W => decodeLMinus x j (leftSideObsNonpos x j W)
    have hPmeas (j : ℤ) : AEMeasurable (P j) wholePlaneIIDCodeMeasure := by
      exact aemeasurable_decodeLMinus_leftSideObsNonpos x j
    have hLk : wholePlaneIIDCodeMeasure.map (A_L x k) =
        (wholePlaneIIDCodeMeasure.map (P k)).map (h.F_Lminus x) := by
      have hAe : A_L x k =ᵐ[wholePlaneIIDCodeMeasure]
          (h.F_Lminus x) ∘ P k := by
        simpa [P] using h.actual_left_ae_eq_Lminus x k hk
      calc
        wholePlaneIIDCodeMeasure.map (A_L x k) =
            wholePlaneIIDCodeMeasure.map ((h.F_Lminus x) ∘ P k) :=
          Measure.map_congr hAe
        _ = (wholePlaneIIDCodeMeasure.map (P k)).map (h.F_Lminus x) :=
          (AEMeasurable.map_map_of_aemeasurable
            (h.aemeasurable_F_Lminus x k hk) (hPmeas k)).symm
    have hL0 : wholePlaneIIDCodeMeasure.map (A_L x 0) =
        (wholePlaneIIDCodeMeasure.map (P 0)).map (h.F_Lminus x) := by
      have hAe : A_L x 0 =ᵐ[wholePlaneIIDCodeMeasure]
          (h.F_Lminus x) ∘ P 0 := by
        simpa [P] using h.actual_left_ae_eq_Lminus x 0 (by omega)
      calc
        wholePlaneIIDCodeMeasure.map (A_L x 0) =
            wholePlaneIIDCodeMeasure.map ((h.F_Lminus x) ∘ P 0) :=
          Measure.map_congr hAe
        _ = (wholePlaneIIDCodeMeasure.map (P 0)).map (h.F_Lminus x) :=
          (AEMeasurable.map_map_of_aemeasurable
            (h.aemeasurable_F_Lminus x 0 (by omega)) (hPmeas 0)).symm
    calc
      wholePlaneIIDCodeMeasure.map (A_L x k) =
          (wholePlaneIIDCodeMeasure.map (P k)).map (h.F_Lminus x) := hLk
      _ = (wholePlaneIIDCodeMeasure.map (P 0)).map (h.F_Lminus x) := by
        exact congrArg (fun μ => μ.map (h.F_Lminus x))
          (decodeLMinus_leftSideObsNonpos_law_eq_zero x k hk)
      _ = wholePlaneIIDCodeMeasure.map (A_L x 0) := hL0.symm





theorem lemma55_of_sideIdentification
    (A_L : Lemma55LeftSideObservable)
    (h : Lemma55SideIdentification A_L) :
    ∀ (x : XDP) (k : ℤ),
      IndepFun (A_L x k) (lemma55RightSideClassOption x k)
        wholePlaneIIDCodeMeasure ∧
      (0 ≤ k → wholePlaneIIDCodeMeasure.map (lemma55RightSideClassOption x k) =
        wholePlaneIIDCodeMeasure.map (lemma55RightSideClassOption x 0)) ∧
      (k ≤ 0 → wholePlaneIIDCodeMeasure.map (A_L x k) =
        wholePlaneIIDCodeMeasure.map (A_L x 0)) :=
  lemma55_of_sideIdentificationAE A_L h.toAE

end DirectedDistances.PaperProofs.Section5
