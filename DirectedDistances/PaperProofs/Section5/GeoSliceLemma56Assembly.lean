/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SplitIndependence
public import DirectedDistances.Probability.SplitIndependenceComposition
public import DirectedDistances.Probability.DeterminedStationarity2
public import DirectedDistances.PaperProofs.Section5.GeoSliceDetermination4
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55Assembly2

/-! # Conditional assembly

The file records the side-determination obligations for an indexed slice
observation and proves the exact independence and two common-law clauses from
those obligations and the conclusion of Lemma 5.5. The observation still
needs to be connected to the geometric slice carrier. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.Probability
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4





structure M0CutGeodesicSliceSideContainment
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))}
    {hp : BoundaryHitWitnesses (kmswPastCode W)} {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) : Prop where
  left : ∀ j k : ℤ, j ≤ k → ∀ a b : ℕ,
    (hab : M0CutLeastEdgeCoalescence (P (j - 1)) (P j) a b) →
    (m0CutGeodesicSlice (hp := hp) P j a b hab).vertices ⊆
        m0GeodesicSideVertices hp (P k) .left ∧
      (m0CutGeodesicSlice (hp := hp) P j a b hab).edges ⊆
        m0GeodesicSideEdges hp (P k) .left
  right : ∀ k j : ℤ, k < j → ∀ a b : ℕ,
    (hab : M0CutLeastEdgeCoalescence (P (j - 1)) (P j) a b) →
    (m0CutGeodesicSlice (hp := hp) P j a b hab).vertices ⊆
        m0GeodesicSideVertices hp (P k) .right ∧
      (m0CutGeodesicSlice (hp := hp) P j a b hab).edges ⊆
        m0GeodesicSideEdges hp (P k) .right

/-- Helper toward Lemma 5.6: the right side observable is almost everywhere
measurable on the nonnegative index range used to transfer the slice laws. -/
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

/-- Helper toward Lemma 5.6: the two actual side-class observations are
almost everywhere measurable when the corresponding measurable side
identifications from the Lemma 5.5 assembly are supplied. -/
theorem aemeasurable_lemma55SideObservables_of_identification
    (A_L : Lemma55LeftSideObservable)
    (h : Lemma55SideIdentificationAE A_L) (x : XDP) (k : ℤ) :
    AEMeasurable (A_L x k) wholePlaneIIDCodeMeasure ∧
      AEMeasurable (lemma55RightSideClassOption x k)
        wholePlaneIIDCodeMeasure := by
  by_cases hk : 0 ≤ k
  · constructor
    · let hF := h.aemeasurable_F_Lplus x k hk
      let F := hF.mk (h.F_Lplus x)
      have hcode : AEMeasurable (leftSideObsNonneg x k)
          wholePlaneIIDCodeMeasure := by
        change AEMeasurable (fun W =>
          (boundaryFourObservations x k 0 W,
            (boundaryFourObservations x k 1 W,
              boundaryFourObservations x k 3 W))) wholePlaneIIDCodeMeasure
        exact (aemeasurable_boundaryFourObservations x k 0).prodMk
          ((aemeasurable_boundaryFourObservations x k 1).prodMk
            (aemeasurable_boundaryFourObservations x k 3))
      have hFmeas : Measurable (fun c => F (decodeLPlus x k c)) :=
        hF.measurable_mk.comp (measurable_decodeLPlus x k)
      have hproxy : AEMeasurable
          (fun W => F (decodeLPlus x k (leftSideObsNonneg x k W)))
          wholePlaneIIDCodeMeasure := hFmeas.comp_aemeasurable hcode
      have hpull : (h.F_Lplus x) ∘
          (fun W => decodeLPlus x k (leftSideObsNonneg x k W)) =ᵐ[
            wholePlaneIIDCodeMeasure]
          F ∘ (fun W => decodeLPlus x k (leftSideObsNonneg x k W)) :=
        ae_of_ae_map (aemeasurable_decodeLPlus_leftSideObsNonneg x k)
          hF.ae_eq_mk
      have hleft : A_L x k =ᵐ[wholePlaneIIDCodeMeasure]
          (fun W => F (decodeLPlus x k (leftSideObsNonneg x k W))) :=
        (h.actual_left_ae_eq_Lplus x k hk).trans hpull
      exact hproxy.congr hleft.symm
    · exact aemeasurable_lemma55RightSideClassOption_nonnegative x k hk
  · have hk' : k ≤ 0 := by omega
    constructor
    · let hF := h.aemeasurable_F_Lminus x k hk'
      let F := hF.mk (h.F_Lminus x)
      have hcode : AEMeasurable (leftSideObsNonpos x k)
          wholePlaneIIDCodeMeasure := by
        change AEMeasurable (fun W =>
          (boundaryFourObservations x k 3 W,
            boundaryFourObservations x k 1 W)) wholePlaneIIDCodeMeasure
        exact (aemeasurable_boundaryFourObservations x k 3).prodMk
          (aemeasurable_boundaryFourObservations x k 1)
      have hFmeas : Measurable (fun c => F (decodeLMinus x k c)) :=
        hF.measurable_mk.comp (measurable_decodeLMinus x k)
      have hproxy : AEMeasurable
          (fun W => F (decodeLMinus x k (leftSideObsNonpos x k W)))
          wholePlaneIIDCodeMeasure := hFmeas.comp_aemeasurable hcode
      have hpull : (h.F_Lminus x) ∘
          (fun W => decodeLMinus x k (leftSideObsNonpos x k W)) =ᵐ[
            wholePlaneIIDCodeMeasure]
          F ∘ (fun W => decodeLMinus x k (leftSideObsNonpos x k W)) :=
        ae_of_ae_map (aemeasurable_decodeLMinus_leftSideObsNonpos x k)
          hF.ae_eq_mk
      have hleft : A_L x k =ᵐ[wholePlaneIIDCodeMeasure]
          (fun W => F (decodeLMinus x k (leftSideObsNonpos x k W))) :=
        (h.actual_left_ae_eq_Lminus x k hk').trans hpull
      exact hproxy.congr hleft.symm
    · let hF := h.aemeasurable_F_Rminus x k hk'
      let F := hF.mk (h.F_Rminus x)
      have hcode : AEMeasurable (rightSideObsNonpos x k)
          wholePlaneIIDCodeMeasure := by
        change AEMeasurable (fun W =>
          (boundaryFourObservations x k 0 W,
            boundaryFourObservations x k 2 W)) wholePlaneIIDCodeMeasure
        exact (aemeasurable_boundaryFourObservations x k 0).prodMk
          (aemeasurable_boundaryFourObservations x k 2)
      have hFmeas : Measurable (fun c => F (decodeRMinus x k c)) :=
        hF.measurable_mk.comp (measurable_decodeRMinus x k)
      have hproxy : AEMeasurable
          (fun W => F (decodeRMinus x k (rightSideObsNonpos x k W)))
          wholePlaneIIDCodeMeasure := hFmeas.comp_aemeasurable hcode
      have hpull : (h.F_Rminus x) ∘
          (fun W => decodeRMinus x k (rightSideObsNonpos x k W)) =ᵐ[
            wholePlaneIIDCodeMeasure]
          F ∘ (fun W => decodeRMinus x k (rightSideObsNonpos x k W)) :=
        ae_of_ae_map (aemeasurable_decodeRMinus_rightSideObsNonpos x k)
          hF.ae_eq_mk
      have hright : lemma55RightSideClassOption x k =ᵐ[
          wholePlaneIIDCodeMeasure]
          (fun W => F (decodeRMinus x k (rightSideObsNonpos x k W))) :=
        (h.actual_right_ae_eq_Rminus x k hk').trans hpull
      exact hproxy.congr hright.symm

/-- Helper toward Lemma 5.6: package the proved almost-sure vertex and edge
containment facts for the selected leftmost family. -/
theorem m0Cut_ae_geodesicSlice_sideContainmentData :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      ∀ longest : Bool,
        ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
          M0CutGeodesicSliceSideContainment (hp := hp) P := by
  filter_upwards [m0Cut_ae_geodesicSlice_left_right_side_containment] with W hW
  obtain ⟨H, h, hLL, hp, hselected⟩ := hW
  refine ⟨H, h, hLL, hp, fun longest => ?_⟩
  obtain ⟨P, T, hleft, huniq, hc, hleftSide, hrightSide,
      hsliceLeft, hsliceRight⟩ := hselected longest
  exact ⟨P, ⟨hsliceLeft, hsliceRight⟩⟩

/-- Helper toward Lemma 5.6: a family of slice observations is determined by
the appropriate side observations when the two side observations measurably
reconstruct the past and future restrictions, and each slice is a fixed
measurable function of its side observation on the index ranges used for the
two common-law clauses. This structure contains only measurability and
geometric determination facts; it contains none of Lemma 5.6's probabilistic
conclusions. -/
structure GeoSliceDeterminationData
    (A_L : Lemma55LeftSideObservable) (x : XDP)
    (G : ℤ → (ℤ → Fin 3) → Option GeometricSideClass) where
  measurable_slice : ∀ j, Measurable (G j)
  aemeasurable_left : ∀ k,
    AEMeasurable (A_L x k) wholePlaneIIDCodeMeasure
  aemeasurable_right : ∀ k,
    AEMeasurable (lemma55RightSideClassOption x k) wholePlaneIIDCodeMeasure
  pastFromLeft : ∀ k, Option GeometricSideClass →
    (∀ _j : {j : ℤ // j ≤ k}, Option GeometricSideClass)
  measurable_pastFromLeft : ∀ k, Measurable (pastFromLeft k)
  futureFromRight : ∀ k, Option GeometricSideClass →
    (∀ _j : {j : ℤ // k + 1 ≤ j}, Option GeometricSideClass)
  measurable_futureFromRight : ∀ k, Measurable (futureFromRight k)
  past_determined_by_left : ∀ k,
    (fun W (j : {j : ℤ // j ≤ k}) => G j W) =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => pastFromLeft k (A_L x k W)
  future_determined_by_right : ∀ k,
    (fun W (j : {j : ℤ // k + 1 ≤ j}) => G j W) =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => futureFromRight k (lemma55RightSideClassOption x k W)
  sliceFromLeft : Option GeometricSideClass → Option GeometricSideClass
  measurable_sliceFromLeft : Measurable sliceFromLeft
  nonpositive_slice_determined_by_left : ∀ k, k ≤ 0 →
    G k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => sliceFromLeft (A_L x k W)
  sliceFromRight : Option GeometricSideClass → Option GeometricSideClass
  measurable_sliceFromRight : Measurable sliceFromRight
  positive_slice_determined_by_right : ∀ k, 1 ≤ k →
    G k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => sliceFromRight (lemma55RightSideClassOption x (k - 1) W)






theorem lemma56_of_sliceDetermination
    (A_L : Lemma55LeftSideObservable) (x : XDP)
    (G : ℤ → (ℤ → Fin 3) → Option GeometricSideClass)
    (hG : GeoSliceDeterminationData A_L x G)
    (h55 : ∀ k : ℤ,
      IndepFun (A_L x k) (lemma55RightSideClassOption x k)
        wholePlaneIIDCodeMeasure ∧
      (0 ≤ k → wholePlaneIIDCodeMeasure.map (lemma55RightSideClassOption x k) =
        wholePlaneIIDCodeMeasure.map (lemma55RightSideClassOption x 0)) ∧
      (k ≤ 0 → wholePlaneIIDCodeMeasure.map (A_L x k) =
        wholePlaneIIDCodeMeasure.map (A_L x 0))) :
    iIndepFun G wholePlaneIIDCodeMeasure ∧
      (∀ k : ℤ, 1 ≤ k →
        wholePlaneIIDCodeMeasure.map (G k) =
          wholePlaneIIDCodeMeasure.map (G 1)) ∧
      (∀ k : ℤ, k ≤ 0 →
        wholePlaneIIDCodeMeasure.map (G k) =
          wholePlaneIIDCodeMeasure.map (G 0)) := by
  let R : ℤ → (ℤ → Fin 3) → Option GeometricSideClass :=
    fun k => lemma55RightSideClassOption x k
  have hind : iIndepFun G wholePlaneIIDCodeMeasure :=
    iIndepFun_of_independent_cut_sides
      (A := fun k => A_L x k)
      (B := R)
      (hAB := fun k => (h55 k).1)
      (F := hG.pastFromLeft)
      (G := hG.futureFromRight)
      (hF := hG.measurable_pastFromLeft)
      (hG := hG.measurable_futureFromRight)
      (hdetL := hG.past_determined_by_left)
      (hdetR := hG.future_determined_by_right)
      (hX := hG.measurable_slice)
  have hpositive : ∀ k : ℤ, 1 ≤ k →
      wholePlaneIIDCodeMeasure.map (G k) =
        wholePlaneIIDCodeMeasure.map (G 1) := by
    apply map_eq_of_ae_determined_right_range
      (Φ_R := hG.sliceFromRight)
      (hΦ_R := hG.measurable_sliceFromRight)
      (hR := hG.aemeasurable_right)
      (hLawR := fun j hj => (h55 j).2.1 hj)
      (hDetR := hG.positive_slice_determined_by_right)
  have hnonpositive : ∀ k : ℤ, k ≤ 0 →
      wholePlaneIIDCodeMeasure.map (G k) =
        wholePlaneIIDCodeMeasure.map (G 0) := by
    apply map_eq_of_ae_determined_left_range
      (Φ_L := hG.sliceFromLeft)
      (hΦ_L := hG.measurable_sliceFromLeft)
      (hL := hG.aemeasurable_left)
      (hLawL := fun j hj => (h55 j).2.2 hj)
      (hDetL := hG.nonpositive_slice_determined_by_left)
  exact ⟨hind, hpositive, hnonpositive⟩







































end DirectedDistances.PaperProofs.Section5
