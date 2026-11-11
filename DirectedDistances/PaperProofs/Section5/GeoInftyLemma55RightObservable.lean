/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSideWhole11
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55Reduction
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55FMapsAE

/-! observable is the class of the actual right side, made unfoldable and
witnessed without the R-plus field; this is not a manuscript change and makes
no paper-completion claim. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: the selected-family data needed to read an
actual right side, with no R-plus realization or isomorphism field. -/
structure M0RightSideObservableWitness (W : ℤ → Fin 3) (longest : Bool) where
  H : WholePlaneRotationHypothesis W
  h : BoundaryHitWitnesses (shiftedStream W 0)
  hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))
  hp : BoundaryHitWitnesses (kmswPastCode W)
  T : ∀ j : ℤ, InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h j)
  P : ∀ j : ℤ, M0CutInfiniteGeodesic W H h hLL j longest
  hleft : ∀ j, Xdp.CutLeftmostXdp W H h hp hLL longest j (P j) (T j)
  huniq : ∀ j Q, Xdp.CutLeftmostXdp W H h hp hLL longest j Q (T j) → Q = P j

/-- Helper toward Lemma 5.5: the selected actual right-side class on the
selected-family event, and `none` outside that event. -/
@[expose] noncomputable def lemma55RightSideClassOption2 (x : XDP) (k : ℤ)
    (W : ℤ → Fin 3) : Option GeometricSideClass :=
  if h : Nonempty (M0RightSideObservableWitness W
      (if x = XDP.ldp then true else false)) then
    some (geometricSideClass
      (m0GeodesicSide (Classical.choice h).hp
        ((Classical.choice h).P k) .right))
  else none

/-- Helper toward Lemma 5.5: on nonempty selected-family data, expose the
class of its actual right side. -/
theorem lemma55RightSideClassOption2_eq_some_of_nonempty (x : XDP) (k : ℤ)
    (W : ℤ → Fin 3)
    (hnonempty : Nonempty (M0RightSideObservableWitness W
      (if x = XDP.ldp then true else false))) :
    lemma55RightSideClassOption2 x k W =
      some (geometricSideClass
        (m0GeodesicSide (Classical.choice hnonempty).hp
          ((Classical.choice hnonempty).P k) .right)) := by
  unfold lemma55RightSideClassOption2
  rw [dite_eq_left hnonempty]

/-- Helper toward Lemma 5.5: an empty selected-family event has no actual
right-side class. -/
theorem lemma55RightSideClassOption2_eq_none_of_isEmpty (x : XDP) (k : ℤ)
    (W : ℤ → Fin 3)
    (h : IsEmpty (M0RightSideObservableWitness W
      (if x = XDP.ldp then true else false))) :
    lemma55RightSideClassOption2 x k W = none := by
  cases x
  · have hn : ¬ Nonempty (M0RightSideObservableWitness W true) := by
      rintro ⟨w⟩
      exact h.false w
    simp [lemma55RightSideClassOption2, hn]
  · have hn : ¬ Nonempty (M0RightSideObservableWitness W false) := by
      rintro ⟨w⟩
      exact h.false w
    simp [lemma55RightSideClassOption2, hn]

/-- Helper toward Lemma 5.5: the selected-family data for both modes is
available almost surely. -/
theorem ae_m0RightSideObservableWitness :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ longest : Bool, Nonempty (M0RightSideObservableWitness W longest) := by
  filter_upwards [ae_boundaryGluing_nonneg_right_markedIso_decodeRPlus] with W hreader
  obtain ⟨H, h, hLL, hp, hall⟩ := hreader
  intro longest
  obtain ⟨_R, T, P, _hR, hleft, huniq, _hcoal, _hside⟩ := hall longest
  exact ⟨⟨H, h, hLL, hp, T, P, hleft, huniq⟩⟩

/-- Helper toward Lemma 5.5: the actual right-side observable is present
almost surely at every mode and integer index. -/
theorem ae_lemma55RightSideClassOption2_isSome (x : XDP) (k : ℤ) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      (lemma55RightSideClassOption2 x k W).isSome := by
  cases x with
  | ldp =>
      filter_upwards [ae_m0RightSideObservableWitness] with W hW
      have hw : Nonempty (M0RightSideObservableWitness W true) := hW true
      simp [lemma55RightSideClassOption2, hw]
  | sdp =>
      filter_upwards [ae_m0RightSideObservableWitness] with W hW
      have hw : Nonempty (M0RightSideObservableWitness W false) := hW false
      simp [lemma55RightSideClassOption2, hw]

private theorem option_map_geometricSideClass_eq_some_of_isSome
    (M : Option GeometricSideSubmap) (hM : M.isSome) :
    M.map geometricSideClass =
      some (geometricSideClass (M.get hM)) := by
  calc
    M.map geometricSideClass =
        (some (M.get hM)).map geometricSideClass :=
      congrArg (fun a : Option GeometricSideSubmap => a.map geometricSideClass)
        (Option.some_get hM).symm
    _ = some (geometricSideClass (M.get hM)) := rfl

/-- Helper toward Lemma 5.5: the actual observable agrees almost surely
with the R-plus presentation class at every nonnegative index. -/
theorem lemma55RightSideClassOption2_ae_eq_RPlusPresentationClass
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    lemma55RightSideClassOption2 x k =ᵐ[wholePlaneIIDCodeMeasure]
      (fun W => (decodeRPlus x k (rightSideObsNonneg x k W)).realization.map
        geometricSideClass) := by
  cases x with
  | ldp =>
      filter_upwards [ae_m0RightSideObservableWitness,
        wholePlane_ae_boundaryGluing_inputs] with W hW hglue
      let w : M0RightSideObservableWitness W true := Classical.choice (hW true)
      obtain ⟨hτ, hfin, _hroot, hcoherent⟩ := hglue w.h k
      have hq := hcoherent XDP.ldp
      let r := decodeRPlus XDP.ldp k (rightSideObsNonneg XDP.ldp k W)
      have hreal : r.realization.isSome :=
        decodeRPlus_rightSideObsNonneg_realization_isSome XDP.ldp k W hq
      have hiso := boundaryGluing_nonneg_right_markedIso_decodeRPlus
        hτ w.hp (w.P k) hq (w.T k) hfin (w.hleft k) hk
      have hoption : lemma55RightSideClassOption2 XDP.ldp k W =
          some (geometricSideClass (m0GeodesicSide w.hp (w.P k) .right)) := by
        simpa [w] using lemma55RightSideClassOption2_eq_some_of_nonempty
          XDP.ldp k W (hW true)
      have hclass :
          geometricSideClass (m0GeodesicSide w.hp (w.P k) .right) =
            geometricSideClass (r.realization.get hreal) :=
        (geometricSideClass_eq_iff _ _).2 hiso
      have hmap := option_map_geometricSideClass_eq_some_of_isSome
        r.realization hreal
      change lemma55RightSideClassOption2 XDP.ldp k W =
        r.realization.map geometricSideClass
      rw [hoption]
      exact (congrArg some hclass).trans hmap.symm
  | sdp =>
      filter_upwards [ae_m0RightSideObservableWitness,
        wholePlane_ae_boundaryGluing_inputs] with W hW hglue
      let w : M0RightSideObservableWitness W false := Classical.choice (hW false)
      obtain ⟨hτ, hfin, _hroot, hcoherent⟩ := hglue w.h k
      have hq := hcoherent XDP.sdp
      let r := decodeRPlus XDP.sdp k (rightSideObsNonneg XDP.sdp k W)
      have hreal : r.realization.isSome :=
        decodeRPlus_rightSideObsNonneg_realization_isSome XDP.sdp k W hq
      have hiso := boundaryGluing_nonneg_right_markedIso_decodeRPlus
        hτ w.hp (w.P k) hq (w.T k) hfin (w.hleft k) hk
      have hoption : lemma55RightSideClassOption2 XDP.sdp k W =
          some (geometricSideClass (m0GeodesicSide w.hp (w.P k) .right)) := by
        simpa [w] using lemma55RightSideClassOption2_eq_some_of_nonempty
          XDP.sdp k W (hW false)
      have hclass :
          geometricSideClass (m0GeodesicSide w.hp (w.P k) .right) =
            geometricSideClass (r.realization.get hreal) :=
        (geometricSideClass_eq_iff _ _).2 hiso
      have hmap := option_map_geometricSideClass_eq_some_of_isSome
        r.realization hreal
      change lemma55RightSideClassOption2 XDP.sdp k W =
        r.realization.map geometricSideClass
      rw [hoption]
      exact (congrArg some hclass).trans hmap.symm

/-- Helper toward Lemma 5.5: at every nonnegative index the new observable
agrees almost surely with the existing right-side class reader. -/
theorem lemma55RightSideClassOption2_ae_eq_lemma55RightSideClassOption
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    lemma55RightSideClassOption2 x k =ᵐ[wholePlaneIIDCodeMeasure]
      lemma55RightSideClassOption x k := by
  cases x with
  | ldp =>
      have hnew := lemma55RightSideClassOption2_ae_eq_RPlusPresentationClass
        XDP.ldp k hk
      have hold := m0RightSideClassOption_ae_eq_RPlusPresentationClass true k hk
      filter_upwards [hnew, hold] with W hnew hold
      change lemma55RightSideClassOption2 XDP.ldp k W =
        m0RightSideClassOption true k W
      have hold' : m0RightSideClassOption true k W =
          (decodeRPlus XDP.ldp k (rightSideObsNonneg XDP.ldp k W)).realization.map
            geometricSideClass := by
        simpa using hold
      exact hnew.trans hold'.symm
  | sdp =>
      have hnew := lemma55RightSideClassOption2_ae_eq_RPlusPresentationClass
        XDP.sdp k hk
      have hold := m0RightSideClassOption_ae_eq_RPlusPresentationClass false k hk
      filter_upwards [hnew, hold] with W hnew hold
      change lemma55RightSideClassOption2 XDP.sdp k W =
        m0RightSideClassOption false k W
      have hold' : m0RightSideClassOption false k W =
          (decodeRPlus XDP.sdp k (rightSideObsNonneg XDP.sdp k W)).realization.map
            geometricSideClass := by
        simpa using hold
      exact hnew.trans hold'.symm

/-- Helper toward Lemma 5.5: at every nonpositive index the new observable
agrees almost surely with the R-minus decoded whole-side class reader. -/
theorem lemma55RightSideClassOption2_ae_eq_RMinusSidePresentation_classOption
    (x : XDP) (k : ℤ) (hk : k ≤ 0) :
    lemma55RightSideClassOption2 x k =ᵐ[wholePlaneIIDCodeMeasure]
      (RMinusSidePresentation.classOption (x := x)) ∘
        (fun W => decodeRMinus x k (rightSideObsNonpos x k W)) := by
  cases x with
  | ldp =>
      filter_upwards [ae_m0RightSideObservableWitness,
        wholePlane_ae_boundaryGluing_inputs] with W hW hglue
      let w : M0RightSideObservableWitness W true := Classical.choice (hW true)
      obtain ⟨hτ, hfin, _hroot, hcoherent⟩ := hglue w.h k
      have hq := hcoherent XDP.ldp
      let r := decodeRMinus XDP.ldp k (rightSideObsNonpos XDP.ldp k W)
      obtain ⟨hreal, hiso⟩ := boundaryGluing_nonpos_right_markedIso_wholeRealization
        hτ w.hp (w.P k) hq (w.T k) hfin (w.hleft k) hk
      have hoption : lemma55RightSideClassOption2 XDP.ldp k W =
          some (geometricSideClass (m0GeodesicSide w.hp (w.P k) .right)) := by
        simpa [w] using lemma55RightSideClassOption2_eq_some_of_nonempty
          XDP.ldp k W (hW true)
      have hclass :
          geometricSideClass (r.wholeRealization.get hreal) =
            geometricSideClass (m0GeodesicSide w.hp (w.P k) .right) :=
        (geometricSideClass_eq_iff _ _).2 hiso
      have hmap := option_map_geometricSideClass_eq_some_of_isSome
        r.wholeRealization hreal
      have hclassOption : r.classOption =
          some (geometricSideClass (r.wholeRealization.get hreal)) := by
        simpa [RMinusSidePresentation.classOption, optionalGeometricSideClass]
          using hmap
      change lemma55RightSideClassOption2 XDP.ldp k W = r.classOption
      rw [hoption]
      exact (congrArg some hclass.symm).trans hclassOption.symm
  | sdp =>
      filter_upwards [ae_m0RightSideObservableWitness,
        wholePlane_ae_boundaryGluing_inputs] with W hW hglue
      let w : M0RightSideObservableWitness W false := Classical.choice (hW false)
      obtain ⟨hτ, hfin, _hroot, hcoherent⟩ := hglue w.h k
      have hq := hcoherent XDP.sdp
      let r := decodeRMinus XDP.sdp k (rightSideObsNonpos XDP.sdp k W)
      obtain ⟨hreal, hiso⟩ := boundaryGluing_nonpos_right_markedIso_wholeRealization
        hτ w.hp (w.P k) hq (w.T k) hfin (w.hleft k) hk
      have hoption : lemma55RightSideClassOption2 XDP.sdp k W =
          some (geometricSideClass (m0GeodesicSide w.hp (w.P k) .right)) := by
        simpa [w] using lemma55RightSideClassOption2_eq_some_of_nonempty
          XDP.sdp k W (hW false)
      have hclass :
          geometricSideClass (r.wholeRealization.get hreal) =
            geometricSideClass (m0GeodesicSide w.hp (w.P k) .right) :=
        (geometricSideClass_eq_iff _ _).2 hiso
      have hmap := option_map_geometricSideClass_eq_some_of_isSome
        r.wholeRealization hreal
      have hclassOption : r.classOption =
          some (geometricSideClass (r.wholeRealization.get hreal)) := by
        simpa [RMinusSidePresentation.classOption, optionalGeometricSideClass]
          using hmap
      change lemma55RightSideClassOption2 XDP.sdp k W = r.classOption
      rw [hoption]
      exact (congrArg some hclass.symm).trans hclassOption.symm

end DirectedDistances.PaperProofs.Section5
