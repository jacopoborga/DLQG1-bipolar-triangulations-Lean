/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55RightLawClause
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55ClassIndependence
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55NonnegPresentationIndependence
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55NonposPresentationIndependence

/-! reduction helper; hypotheses are open obligations (Lemma 5.5 not proved). -/

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4

/-- Helper toward Lemma 5.5: the actual left-side optional class observable. -/
abbrev Lemma55LeftSideObservable :=
  XDP → ℤ → (ℤ → Fin 3) → Option GeometricSideClass

/-- Helper toward Lemma 5.5: the actual right-side optional class observable,
indexed by the source's `XDP` choice. -/
@[expose] noncomputable def lemma55RightSideClassOption (x : XDP) (k : ℤ)
    (W : ℤ → Fin 3) : Option GeometricSideClass :=
  m0RightSideClassOption (if x = XDP.ldp then true else false) k W




structure Lemma55SideIdentification (A_L : Lemma55LeftSideObservable) where
  F_Lplus : ∀ x : XDP, LPlusSidePresentation x → Option GeometricSideClass
  measurable_F_Lplus : ∀ x, Measurable (F_Lplus x)
  actual_left_ae_eq_Lplus : ∀ (x : XDP) (k : ℤ), 0 ≤ k →
    A_L x k =ᵐ[wholePlaneIIDCodeMeasure]
      (F_Lplus x) ∘ (fun W => decodeLPlus x k (leftSideObsNonneg x k W))
  F_Lminus : ∀ x : XDP, LMinusSidePresentation x → Option GeometricSideClass
  measurable_F_Lminus : ∀ x, Measurable (F_Lminus x)
  actual_left_ae_eq_Lminus : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
    A_L x k =ᵐ[wholePlaneIIDCodeMeasure]
      (F_Lminus x) ∘ (fun W => decodeLMinus x k (leftSideObsNonpos x k W))
  F_Rminus : ∀ x : XDP, RMinusSidePresentation x → Option GeometricSideClass
  measurable_F_Rminus : ∀ x, Measurable (F_Rminus x)
  actual_right_ae_eq_Rminus : ∀ (x : XDP) (k : ℤ), k ≤ 0 →
    lemma55RightSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
      (F_Rminus x) ∘ (fun W => decodeRMinus x k (rightSideObsNonpos x k W))

/-- Helper toward Lemma 5.5: the right optional-class law is the same at every
nonnegative index as at zero, by the proved right-law clause. -/
theorem lemma55_rightLaw_of_sideIdentification (x : XDP) (k : ℤ)
    (hk : 0 ≤ k) :
    wholePlaneIIDCodeMeasure.map (lemma55RightSideClassOption x k) =
      wholePlaneIIDCodeMeasure.map (lemma55RightSideClassOption x 0) := by
  cases x with
  | ldp =>
      change wholePlaneIIDCodeMeasure.map (m0RightSideClassOption true k) =
        wholePlaneIIDCodeMeasure.map (m0RightSideClassOption true 0)
      exact m0RightSideClassOption_law_eq_zero true k hk
  | sdp =>
      change wholePlaneIIDCodeMeasure.map (m0RightSideClassOption false k) =
        wholePlaneIIDCodeMeasure.map (m0RightSideClassOption false 0)
      exact m0RightSideClassOption_law_eq_zero false k hk

/-- Helper toward Lemma 5.5: the left optional-class law follows from the
nonpositive presentation law and its open side-identification field. -/
theorem lemma55_leftLaw_of_sideIdentification
    (A_L : Lemma55LeftSideObservable)
    (h : Lemma55SideIdentification A_L)
    (x : XDP) (k : ℤ) (hk : k ≤ 0) :
    wholePlaneIIDCodeMeasure.map (A_L x k) =
      wholePlaneIIDCodeMeasure.map (A_L x 0) := by
  let P := fun j : ℤ =>
    fun W => decodeLMinus x j (leftSideObsNonpos x j W)
  have hPmeas (j : ℤ) : AEMeasurable (P j) wholePlaneIIDCodeMeasure := by
    exact aemeasurable_decodeLMinus_leftSideObsNonpos x j
  have hLk := map_eq_map_comp_of_ae_eq wholePlaneIIDCodeMeasure
    (hPmeas k) (h.F_Lminus x) (h.measurable_F_Lminus x)
    (h.actual_left_ae_eq_Lminus x k hk)
  have hL0 := map_eq_map_comp_of_ae_eq wholePlaneIIDCodeMeasure
    (hPmeas 0) (h.F_Lminus x) (h.measurable_F_Lminus x)
    (h.actual_left_ae_eq_Lminus x 0 (by omega))
  calc
    wholePlaneIIDCodeMeasure.map (A_L x k) =
        (wholePlaneIIDCodeMeasure.map (P k)).map (h.F_Lminus x) := hLk
    _ = (wholePlaneIIDCodeMeasure.map (P 0)).map (h.F_Lminus x) := by
      exact congrArg (fun μ => μ.map (h.F_Lminus x))
        (decodeLMinus_leftSideObsNonpos_law_eq_zero x k hk)
    _ = wholePlaneIIDCodeMeasure.map (A_L x 0) := hL0.symm






















end DirectedDistances.PaperProofs.Section5
