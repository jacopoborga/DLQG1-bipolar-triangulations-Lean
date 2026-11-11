/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSide4CrossWitness2
public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusMeasurableDescent
public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusMeasurableDescent

import all DirectedDistances.PaperProofs.Section5.GeoInftyLemma55ClassValued

/-! Reader 5 selects only mode-aligned source witnesses. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local notation "LPlusCodeReader5" =>
  (ℕ → Fin 3) × (ℕ → Option FiniteThinMap) × (ℕ → Fin 3)

/-- Helper toward Lemma 5.5. Read the corrected decoder-4 class from a
nonnegative presentation using an aligned source witness. -/
@[expose] noncomputable def LPlusSidePresentation.classOptionAt5
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x) :
    Option GeometricSideClass :=
  if hk : 0 ≤ k then
    if hw : Nonempty (LPlusSourceWitnessAligned x k r) then
      let s := Classical.choice hw
      some (geometricSideClass
        (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk))
    else none
  else none

/-- Helper toward Lemma 5.5. On an aligned source-witness guard, reader 5
returns the corrected class built from that chosen witness. -/
theorem LPlusSidePresentation.classOptionAt5_eq_some
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x) (hk : 0 ≤ k)
    (hw : Nonempty (LPlusSourceWitnessAligned x k r)) :
    LPlusSidePresentation.classOptionAt5 x k r =
      some (geometricSideClass
        (lPlusCodeBlockSide4 (Classical.choice hw).hτ
          (Classical.choice hw).hp (Classical.choice hw).P
          (Classical.choice hw).hqMode (Classical.choice hw).Tpath
          (Classical.choice hw).hfin (Classical.choice hw).hleft hk)) := by
  classical
  simp [LPlusSidePresentation.classOptionAt5, hk, hw]

/-- Helper toward Lemma 5.5. The reader-5 code reader retains the complete
three-coordinate presentation code. -/
@[expose] noncomputable def lPlusSidePresentationClassOptionCode5
    (x : XDP) (k : ℤ) (c : LPlusCodeReader5) : Option GeometricSideClass :=
  LPlusSidePresentation.classOptionAt5 x k (decodeLPlus x k c)

/-- Helper toward Lemma 5.5. Reader 5 factors through the complete code. -/
theorem lPlusSidePresentation_classOptionAt5_eq_codeReader
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x) :
    LPlusSidePresentation.classOptionAt5 x k r =
      lPlusSidePresentationClassOptionCode5 x k r.code := by
  change LPlusSidePresentation.classOptionAt5 x k r =
    LPlusSidePresentation.classOptionAt5 x k (decodeLPlus x k r.code)
  rw [LPlusSidePresentation.decode_code]

/-- Helper toward Lemma 5.5. Every observed nonnegative presentation almost
surely has an aligned source witness, with its source walk equal to the
observed walk. -/
theorem ae_LPlusSidePresentation_exists_alignedWitness
    (x : XDP) (k : ℤ) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ s : LPlusSourceWitnessAligned x k
        (decodeLPlus x k (leftSideObsNonneg x k W)), s.W = W := by
  filter_upwards [ae_lPlusSourceWitness_exists_with_longest x k] with W hW
  let longest := if x = XDP.ldp then true else false
  have hmode : (if longest then XDP.ldp else XDP.sdp) = x := by
    cases x <;> simp [longest]
  obtain ⟨s, hsW, hsl⟩ := hW longest
  have hmode' : (if s.longest then XDP.ldp else XDP.sdp) = x := by
    rw [hsl]
    exact hmode
  exact ⟨⟨s, hmode'⟩, hsW⟩

/-- Helper toward Lemma 5.5. Reader 5 is present almost surely on observed
nonnegative left presentations. -/
theorem ae_decodeLPlus_leftSideObsNonneg_classOptionAt5_isSome
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      (LPlusSidePresentation.classOptionAt5 x k
        (decodeLPlus x k (leftSideObsNonneg x k W))).isSome := by
  filter_upwards [ae_LPlusSidePresentation_exists_alignedWitness x k] with W hW
  obtain ⟨s, _⟩ := hW
  have hw : Nonempty (LPlusSourceWitnessAligned x k
      (decodeLPlus x k (leftSideObsNonneg x k W))) := ⟨s⟩
  simp [LPlusSidePresentation.classOptionAt5, hk, hw]

/-- Helper toward Lemma 5.5. Under the aligned cross-witness class
comparison, the actual left observable agrees almost surely with reader 5. -/
theorem lemma55LeftSideClassOption_ae_eq_LPlusSidePresentation_classOptionAt5
    (hcross : ∀ (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
      (s : LPlusSourceWitnessAligned x k r)
      (s' : LPlusSourceWitnessAligned x k r') (hk : 0 ≤ k)
      (hr : r.code = r'.code),
      geometricSideClass
        (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) =
      geometricSideClass
        (lPlusCodeBlockSide4 s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk))
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    lemma55LeftSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
      (LPlusSidePresentation.classOptionAt5 x k) ∘
        (fun W => decodeLPlus x k (leftSideObsNonneg x k W)) := by
  filter_upwards [ae_lemma55LeftSideClassOption_eq_lPlusCodeBlockSide4 x k hk,
    ae_LPlusSidePresentation_exists_alignedWitness x k] with W hactual haligned
  rcases hactual with ⟨hw, hrest⟩
  let w := Classical.choice hw
  obtain ⟨hτ, hfin, hqMode, hactual⟩ := hrest
  obtain ⟨sObs, _hsW⟩ := haligned
  let r := decodeLPlus x k (leftSideObsNonneg x k W)
  let longest := if x = XDP.ldp then true else false
  have hmode : (if longest then XDP.ldp else XDP.sdp) = x := by
    cases x <;> simp [longest]
  let sSource : LPlusSidePresentationSourceWitness x k r :=
    { W := W
      h := w.h
      H := w.H
      hLL := w.hLL
      longest := longest
      hτ := hτ
      hp := w.hp
      P := w.P k
      hqMode := by simpa [longest] using hqMode
      Tpath := w.T k
      hfin := hfin
      hleft := w.hleft k
      prefixCode_eq := rfl
      coherentCode_eq := rfl
      primedCode_eq := rfl }
  have hmodeSource : (if sSource.longest then XDP.ldp else XDP.sdp) = x := by
    simpa [sSource] using hmode
  let sActual : LPlusSourceWitnessAligned x k r := ⟨sSource, hmodeSource⟩
  have hsameActual :
      lemma55LeftSideClassOption x k W =
        some (geometricSideClass
          (lPlusCodeBlockSide4 sActual.hτ sActual.hp sActual.P sActual.hqMode
            sActual.Tpath sActual.hfin sActual.hleft hk)) := by
    rw [hactual]
  let hwObs : Nonempty (LPlusSourceWitnessAligned x k r) := ⟨sObs⟩
  let sReader := Classical.choice hwObs
  have hclasses := hcross x k r r sActual sReader hk rfl
  have hreader := LPlusSidePresentation.classOptionAt5_eq_some
    x k r hk hwObs
  change lemma55LeftSideClassOption x k W =
    LPlusSidePresentation.classOptionAt5 x k r
  rw [hsameActual, hreader]
  exact congrArg some hclasses

/-- Helper toward Lemma 5.5. Reader-5 composition measurability descends to
the observation law by the certified thin-presentation retraction. -/
theorem aemeasurable_LPlusSidePresentation_classOptionAt5_of_comp
    (x : XDP) (k : ℤ) (_hk : 0 ≤ k)
    (hcomp : AEMeasurable
      ((LPlusSidePresentation.classOptionAt5 x k) ∘
        (fun W => decodeLPlus x k (leftSideObsNonneg x k W)))
      wholePlaneIIDCodeMeasure) :
    AEMeasurable (LPlusSidePresentation.classOptionAt5 x k)
      (wholePlaneIIDCodeMeasure.map
        (fun W => decodeLPlus x k (leftSideObsNonneg x k W))) := by
  let obs (W : ℤ → Fin 3) := decodeLPlus x k (leftSideObsNonneg x k W)
  let f := lPlusThinPresentationRetract x ∘ obs
  let g := (LPlusSidePresentation.classOptionAt5 x k) ∘ lPlusThinPresentationVal x
  have hf : AEMeasurable f wholePlaneIIDCodeMeasure :=
    (measurable_lPlusThinPresentationRetract x).comp_aemeasurable
      (aemeasurable_decodeLPlus_leftSideObsNonneg x k)
  have he : lPlusThinPresentationVal x ∘ f =ᵐ[wholePlaneIIDCodeMeasure] obs := by
    filter_upwards [ae_decodeLPlus_leftSideObsNonneg_hatted_mem_range x k] with W hW
    exact lPlusThinPresentationVal_retract x (obs W) hW
  have hgf : AEMeasurable (g ∘ f) wholePlaneIIDCodeMeasure :=
    hcomp.congr (he.symm.fun_comp (LPlusSidePresentation.classOptionAt5 x k))
  have hdesc : AEMeasurable g (wholePlaneIIDCodeMeasure.map f) :=
    aemeasurable_map_of_aemeasurable_comp wholePlaneIIDCodeMeasure hf hgf
  have hreader : AEMeasurable (LPlusSidePresentation.classOptionAt5 x k)
      ((wholePlaneIIDCodeMeasure.map f).map (lPlusThinPresentationVal x)) :=
    (measurableEmbedding_lPlusThinPresentationVal x).aemeasurable_map_iff.mpr hdesc
  have hmap : (wholePlaneIIDCodeMeasure.map f).map (lPlusThinPresentationVal x) =
      wholePlaneIIDCodeMeasure.map obs := by
    rw [AEMeasurable.map_map_of_aemeasurable
      (measurable_lPlusThinPresentationVal x).aemeasurable hf]
    exact Measure.map_congr he
  rwa [hmap] at hreader

/-- Helper toward Lemma 5.5. Actual-side measurability and the reader-5
almost-everywhere identification give reader-5 measurability. -/
theorem aemeasurable_LPlusSidePresentation_classOptionAt5_of_actual
    (x : XDP) (k : ℤ) (hk : 0 ≤ k)
    (hLplusEq5 : lemma55LeftSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
      (LPlusSidePresentation.classOptionAt5 x k) ∘
        (fun W => decodeLPlus x k (leftSideObsNonneg x k W)))
    (hactual : AEMeasurable (lemma55LeftSideClassOption x k)
      wholePlaneIIDCodeMeasure) :
    AEMeasurable (LPlusSidePresentation.classOptionAt5 x k)
      (wholePlaneIIDCodeMeasure.map
        (fun W => decodeLPlus x k (leftSideObsNonneg x k W))) :=
  aemeasurable_LPlusSidePresentation_classOptionAt5_of_comp x k hk
    (hactual.congr hLplusEq5)

/-- Helper toward Lemma 5.5. The five Assembly-7 clauses hold with reader 5;
the L-minus presentation measurability input is discharged by its proved
descent theorem. -/
theorem lemma55_classValued_of_LPlusReader5
    (default : GeometricSideClass)
    (hcross : ∀ (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
      (s : LPlusSourceWitnessAligned x k r)
      (s' : LPlusSourceWitnessAligned x k r') (hk : 0 ≤ k)
      (hr : r.code = r'.code),
      geometricSideClass
        (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) =
      geometricSideClass
        (lPlusCodeBlockSide4 s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk))
    (hLplusMeasActual : ∀ (x : XDP) (k : ℤ) (_hk : 0 ≤ k),
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
  have hLplusEq5 : ∀ (x : XDP) (k : ℤ) (_hk : 0 ≤ k),
      lemma55LeftSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
        (LPlusSidePresentation.classOptionAt5 x k) ∘ (fun W =>
          decodeLPlus x k (leftSideObsNonneg x k W)) := by
    intro x k hk
    exact lemma55LeftSideClassOption_ae_eq_LPlusSidePresentation_classOptionAt5
      hcross x k hk
  have hLplusMeas5 : ∀ (x : XDP) (k : ℤ) (_hk : 0 ≤ k),
      AEMeasurable (LPlusSidePresentation.classOptionAt5 x k)
        (wholePlaneIIDCodeMeasure.map (fun W =>
          decodeLPlus x k (leftSideObsNonneg x k W))) := by
    intro x k hk
    exact aemeasurable_LPlusSidePresentation_classOptionAt5_of_actual x k hk
      (hLplusEq5 x k hk) (hLplusMeasActual x k hk)
  have hLminusMeas : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
      AEMeasurable (LMinusSidePresentation.classOption4 (x := x))
        (wholePlaneIIDCodeMeasure.map (fun W =>
          decodeLMinus x k (leftSideObsNonpos x k W))) := by
    intro x k hk
    exact aemeasurable_LMinusSidePresentation_classOption4 x k hk
  intro x k
  have hIndep : IndepFun (lemma55LeftSideClassOption x k)
      (lemma55RightSideClassOption2 x k) wholePlaneIIDCodeMeasure := by
    by_cases hk : 0 ≤ k
    · let hFL := hLplusMeas5 x k hk
      let FL := hFL.mk (LPlusSidePresentation.classOptionAt5 x k)
      let hPsi := aemeasurable_Psi_rightSideObsNonneg_law x k
      let PsiM := hPsi.mk (Psi x)
      have hLpull :
          (LPlusSidePresentation.classOptionAt5 x k) ∘ (fun W =>
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
          filter_upwards [(hLplusEq5 x k hk).trans hLpull] with W hW
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
