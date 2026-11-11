/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55ClassValued
public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusDecodedSide5
public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSideMeasurable13

/-! The corrected L-minus reader uses decoder 4, including its exterior marks.
This module makes no claim that Lemma 5.5 is proved. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: every observed nonnegative left presentation
has a source witness almost surely, so its indexed class reader is present.
This asserts presence, without asserting class-reader measurability or its
identification with an arbitrary actual observable. -/
theorem ae_LPlusIndexedSidePresentation_classOption_isSome
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      (LPlusIndexedSidePresentation.classOption x
        (decodeLPlusWithIndex x k hk (leftSideObsNonneg x k W))).isSome := by
  filter_upwards [Xdp.m0Cut_ae_leftmost_xdp_and_pairwise_coalescence,
    wholePlane_ae_boundaryGluing_inputs] with W hgeo hglue
  obtain ⟨H, h, hLL, hp, hpaths⟩ := hgeo
  let longest : Bool := if x = XDP.ldp then true else false
  have hmode : (if longest then XDP.ldp else XDP.sdp) = x := by
    cases x <;> rfl
  obtain ⟨R, T, P, _, hleft, _, _⟩ := hpaths longest
  obtain ⟨hτ, hfin, _, hcoherent⟩ := hglue h k
  let r := decodeLPlus x k (leftSideObsNonneg x k W)
  have hw : Nonempty (LPlusSidePresentationSourceWitness x k r) := by
    refine ⟨⟨W, h, H, hLL, longest, hτ, hp, P k, ?_, T k, hfin,
      hleft k, rfl, rfl, rfl⟩⟩
    rw [hmode]
    exact hcoherent x
  change (LPlusSidePresentation.classOptionAt x k r).isSome
  rw [LPlusSidePresentation.classOptionAt_eq_some x k r hk hw]
  exact Option.isSome_some

/-- Helper toward Lemma 5.5: transport the proved decoded R-minus presence
along the existing actual-reader equality field. This discharges the separate
right-presence hypothesis without assuming an additional presence target. -/
theorem ae_lemma55RightSideClassOption_isSome_of_RMinus_eq
    (x : XDP) (k : ℤ) (hk : k ≤ 0)
    (heq : lemma55RightSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
      (RMinusSidePresentation.classOption (x := x)) ∘
        (fun W => decodeRMinus x k (rightSideObsNonpos x k W))) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      (lemma55RightSideClassOption x k W).isSome := by
  filter_upwards [heq, ae_decodeRMinus_rightSideObsNonpos_classOption_isSome x k hk]
    with W heqW hpresent
  rw [heqW]
  exact hpresent

/-- Helper toward Lemma 5.5: the exact five-clause conclusion of
`lemma55_classValued_of_sideIdentificationAE3`, with the three readers fixed
internally and both separate presence hypotheses discharged from the retained
actual-reader equality fields and proved decoded-reader presence.
The L-minus reader is the corrected decoder-4 reader, never decoder 2.

Remaining inherited hypotheses (all are explicit binders below):
* `hLplusMeas`: L-plus class measurability, recorded open in
  GeoInftyLemma55FMapsAE.lean:256; the indexed reader uses the same index.
* `hLplusEq`: L-plus actual-reader equality,
  GeoInftyLemma55Assembly3.lean:74; its geometric
  precursor is open in GeoInftyLPlusActualSideIso10.lean:890.
* `hLminusMeas`: corrected L-minus class measurability, recorded open in
  GeoInftyLMinusDecodedSide5.lean:429.
* `hLminusEq`: equality for the arbitrary observable,
  GeoInftyLemma55Assembly3.lean:82.
  The concrete reader bridge is open in GeoInftyLemma55Presence2.lean:59;
  the decoder-4 geometric identification itself is already proved.
* `hRminusMeas`: R-minus class measurability, recorded open in
  GeoInftyLemma55FMapsAE3.lean:38.
* `hRminusEq`: R-minus actual-reader equality, recorded open in
  GeoInftyNonposRightSideWhole4.lean:114.

These are the original conditional theorem's remaining obligations, with
its map fields instantiated; they are not claimed proved. In particular,
this theorem does not identify the arbitrary `A_L` with the concrete opaque
left reader and does not prove the paper's submap-valued statement. -/
theorem lemma55_classValued_of_corrected_readers
    (A_L : Lemma55LeftSideObservable)
    (default : GeometricSideClass)
    (hLplusMeas : ∀ (x : XDP) (k : ℤ) (hk : 0 ≤ k),
      AEMeasurable (LPlusIndexedSidePresentation.classOption x)
        (wholePlaneIIDCodeMeasure.map (fun W =>
          decodeLPlusWithIndex x k hk (leftSideObsNonneg x k W))))
    (hLplusEq : ∀ (x : XDP) (k : ℤ) (hk : 0 ≤ k),
      A_L x k =ᵐ[wholePlaneIIDCodeMeasure]
        (LPlusIndexedSidePresentation.classOption x) ∘ (fun W =>
          decodeLPlusWithIndex x k hk (leftSideObsNonneg x k W)))
    (hLminusMeas : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
      AEMeasurable (LMinusSidePresentation.classOption4 (x := x))
        (wholePlaneIIDCodeMeasure.map (fun W =>
          decodeLMinus x k (leftSideObsNonpos x k W))))
    (hLminusEq : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
      A_L x k =ᵐ[wholePlaneIIDCodeMeasure]
        (LMinusSidePresentation.classOption4 (x := x)) ∘ (fun W =>
          decodeLMinus x k (leftSideObsNonpos x k W)))
    (hRminusMeas : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
      AEMeasurable (RMinusSidePresentation.classOption (x := x))
        (wholePlaneIIDCodeMeasure.map (fun W =>
          decodeRMinus x k (rightSideObsNonpos x k W))))
    (hRminusEq : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
      lemma55RightSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
        (RMinusSidePresentation.classOption (x := x)) ∘ (fun W =>
          decodeRMinus x k (rightSideObsNonpos x k W))) :
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
  let h : Lemma55SideIdentificationAE3 A_L :=
    { F_Lplus := LPlusIndexedSidePresentation.classOption
      aemeasurable_F_Lplus := hLplusMeas
      actual_left_ae_eq_Lplus := hLplusEq
      F_Lminus := fun _ => LMinusSidePresentation.classOption4
      aemeasurable_F_Lminus := hLminusMeas
      actual_left_ae_eq_Lminus := hLminusEq
      F_Rminus := fun _ => RMinusSidePresentation.classOption
      aemeasurable_F_Rminus := hRminusMeas
      actual_right_ae_eq_Rminus := hRminusEq }
  have hpresentLeft : ∀ (x : XDP) (k : ℤ),
      ∀ᵐ W ∂wholePlaneIIDCodeMeasure, (A_L x k W).isSome := by
    intro x k
    by_cases hk : 0 ≤ k
    · filter_upwards [hLplusEq x k hk,
        ae_LPlusIndexedSidePresentation_classOption_isSome x k hk]
        with W heq hpresent
      rw [heq]
      exact hpresent
    · have hk' : k ≤ 0 := by omega
      filter_upwards [hLminusEq x k hk',
        ae_decodeLMinus_leftSideObsNonpos_classOption4_isSome x k hk']
        with W heq hpresent
      rw [heq]
      exact hpresent
  apply lemma55_classValued_of_sideIdentificationAE3 A_L h default hpresentLeft
  intro x k hk
  exact ae_lemma55RightSideClassOption_isSome_of_RMinus_eq x k hk (hRminusEq x k hk)





























































end DirectedDistances.PaperProofs.Section5
