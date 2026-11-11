/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceLemma56Assembly4
public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusCanonicalCodingMeasurable5

/-! Right-side readers of the exposed normalized cut observations. These are
supporting factorizations, not a completion claim for Lemma 5.6. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.6. Retraction preserves the complete observed
right hatted code almost surely, at each integer boundary index. -/
theorem ae_rightThinCodeVal_retract_rightSideObsNonneg4 (x : XDP) (k : ℤ) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      rightThinCodeVal (rightThinCodeRetract (rightSideObsNonneg x k W)) =
        rightSideObsNonneg x k W := by
  filter_upwards [(boundaryFutureThinSides_package x k).2.2.2.2.2] with W hq
  have hc := coherentRightThinCode_val x ⟨boundaryFutureHattedPath k W, hq⟩
  change rightThinCodeVal
      (coherentRightThinCode x ⟨boundaryFutureHattedPath k W, hq⟩) =
    rightSideObsNonneg x k W at hc
  rw [← hc, rightThinCodeRetract_val]

/-- Helper toward Lemma 5.6. Re-embedding the retracted R-minus observation
at its own boundary index recovers its full presentation almost surely. -/
theorem ae_rMinusThinPresentationVal_retract_rightSideObsNonpos4
    (x : XDP) (k : ℤ) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      rMinusThinPresentationVal x k
        (rMinusThinPresentationRetract x
          (decodeRMinus x k (rightSideObsNonpos x k W))) =
        decodeRMinus x k (rightSideObsNonpos x k W) := by
  filter_upwards [ae_rightThinCodeVal_retract_rightSideObsNonneg4 x k] with W hW
  exact congrArg
    (fun c => decodeRMinus x k ((rightSideObsNonpos x k W).1, c)) hW

/-- Helper toward Lemma 5.6. Read the nonnegative right class from the
hatted code, ignoring the fixed unused prefix and boundary index. -/
@[expose] noncomputable def geoSlice56RightPlusClassOption4 (x : XDP)
    (c : RMinusThinPresentation) : Option GeometricSideClass :=
  Psi x (rightThinCodeVal c.2)

/-- Helper toward Lemma 5.6. Read the negative right class from its full
certified presentation, retaining its boundary index. -/
@[expose] noncomputable def geoSlice56RightMinusClassOption4 (x : XDP) (k : ℤ)
    (c : RMinusThinPresentation) : Option GeometricSideClass :=
  (rMinusThinPresentationVal x k c).classOption

/-- Helper toward Lemma 5.6. Select the appropriate right-side reader at
each boundary index, using the R-plus layout at zero. -/
@[expose] noncomputable def geoSlice56RightClassOption4 (x : XDP) (k : ℤ)
    (c : RMinusThinPresentation) : Option GeometricSideClass :=
  if 0 ≤ k then geoSlice56RightPlusClassOption4 x c
  else geoSlice56RightMinusClassOption4 x k c

/-- Helper toward Lemma 5.6. At every nonnegative index the actual right
observable factors through one index-free function of the normalized cut. -/
theorem lemma55RightSideClassOption2_ae_eq_rightPlusCut4
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    lemma55RightSideClassOption2 x k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => geoSlice56RightPlusClassOption4 x
        (geoSlice56RightCutObservation4 x k W) := by
  filter_upwards
    [lemma55RightSideClassOption2_ae_eq_RPlusPresentationClass x k hk,
      ae_rightThinCodeVal_retract_rightSideObsNonneg4 x k] with W hactual hcode
  simpa only [geoSlice56RightCutObservation4, ite_eq_left hk,
    geoSlice56RightPlusClassOption4, rPlusThinIntoRMinus4, hcode, Psi, decodeRPlus]
    using hactual

/-- Helper toward Lemma 5.6. At every negative index the actual right
observable factors through its index-dependent normalized-cut reader. -/
theorem lemma55RightSideClassOption2_ae_eq_rightMinusCut4
    (x : XDP) (k : ℤ) (hk : k < 0) :
    lemma55RightSideClassOption2 x k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => geoSlice56RightMinusClassOption4 x k
        (geoSlice56RightCutObservation4 x k W) := by
  filter_upwards
    [lemma55RightSideClassOption2_ae_eq_RMinusSidePresentation_classOption
      x k (le_of_lt hk),
      ae_rMinusThinPresentationVal_retract_rightSideObsNonpos4 x k]
    with W hactual hval
  simpa only [geoSlice56RightCutObservation4, ite_eq_right (by omega : ¬ 0 ≤ k),
    geoSlice56RightMinusClassOption4, hval, Function.comp_apply] using hactual

/-- Helper toward Lemma 5.6. At every index the actual right observable
factors through the explicit normalized-cut reader. -/
theorem lemma55RightSideClassOption2_ae_eq_rightCut4 (x : XDP) (k : ℤ) :
    lemma55RightSideClassOption2 x k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => geoSlice56RightClassOption4 x k
        (geoSlice56RightCutObservation4 x k W) := by
  by_cases hk : 0 ≤ k
  · simpa only [geoSlice56RightClassOption4, ite_eq_left hk] using
      lemma55RightSideClassOption2_ae_eq_rightPlusCut4 x k hk
  · simpa only [geoSlice56RightClassOption4, ite_eq_right hk] using
      lemma55RightSideClassOption2_ae_eq_rightMinusCut4 x k (by omega)

/-- Helper toward Lemma 5.6. Every slice witness right class has the
explicit per-index factorization through the normalized cut, almost surely. -/
theorem ae_sliceRightSideClass_eq_rightCut4 (x : XDP) (k : ℤ) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ s : M0CutGeodesicSliceWitness W x,
      some (geometricSideClass (m0GeodesicSide s.hp (s.P k) .right)) =
        geoSlice56RightClassOption4 x k (geoSlice56RightCutObservation4 x k W) := by
  filter_upwards [ae_lemma55RightSideClassOption2_eq_sliceSideClass x k,
    lemma55RightSideClassOption2_ae_eq_rightCut4 x k] with W hslice hcut
  intro s
  exact (hslice s).symm.trans hcut

/-- Helper toward Lemma 5.6. Every nonnegative slice witness right class
factors through the same index-free function, simultaneously on one event. -/
theorem ae_all_sliceRightSideClass_eq_rightPlusCut4 (x : XDP) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ j : ℤ, 0 ≤ j →
      ∀ s : M0CutGeodesicSliceWitness W x,
        some (geometricSideClass (m0GeodesicSide s.hp (s.P j) .right)) =
          geoSlice56RightPlusClassOption4 x (geoSlice56RightCutObservation4 x j W) := by
  apply ae_all_iff.mpr
  intro j
  by_cases hj : 0 ≤ j
  · filter_upwards [ae_lemma55RightSideClassOption2_eq_sliceSideClass x j,
      lemma55RightSideClassOption2_ae_eq_rightPlusCut4 x j hj] with W hslice hcut
    intro _ s
    exact (hslice s).symm.trans hcut
  · exact Filter.Eventually.of_forall (fun _ h => (hj h).elim)

/-- Helper toward Lemma 5.6. Default the explicit per-index right reader
outside its almost-sure source-valid domain. -/
@[expose] noncomputable def readR4 (default : GeometricSideClass) (x : XDP)
    (j : ℤ) (c : RMinusThinPresentation) : GeometricSideClass :=
  (geoSlice56RightClassOption4 x j c).getD default

/-- Helper toward Lemma 5.6. Default the shared nonnegative right reader
outside its almost-sure source-valid domain. -/
@[expose] noncomputable def readRplus4 (default : GeometricSideClass) (x : XDP)
    (c : RMinusThinPresentation) : GeometricSideClass :=
  (geoSlice56RightPlusClassOption4 x c).getD default

/-- Helper toward Lemma 5.6. The explicit per-index reader satisfies
exactly the right-reader hypothesis of the conditional side-reader reduction. -/
theorem hReadR4 (default : GeometricSideClass) (x : XDP) :
    ∀ j : ℤ, ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ s : M0CutGeodesicSliceWitness W x,
        readR4 default x j (geoSlice56RightCutObservation4 x j W) =
          geometricSideClass (m0GeodesicSide s.hp (s.P j) .right) := by
  intro j
  filter_upwards [ae_sliceRightSideClass_eq_rightCut4 x j] with W hW
  intro s
  exact (congrArg (fun o : Option GeometricSideClass => o.getD default) (hW s)).symm

/-- Helper toward Lemma 5.6. The explicit shared reader satisfies exactly
the nonnegative right-reader hypothesis, with all indices on one event. -/
theorem hReadRplus4 (default : GeometricSideClass) (x : XDP) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ j : ℤ, 0 ≤ j →
      ∀ s : M0CutGeodesicSliceWitness W x,
        readRplus4 default x (geoSlice56RightCutObservation4 x j W) =
          geometricSideClass (m0GeodesicSide s.hp (s.P j) .right) := by
  filter_upwards [ae_all_sliceRightSideClass_eq_rightPlusCut4 x] with W hW
  intro j hj s
  exact (congrArg (fun o : Option GeometricSideClass => o.getD default) (hW j hj s)).symm

end DirectedDistances.PaperProofs.Section5

