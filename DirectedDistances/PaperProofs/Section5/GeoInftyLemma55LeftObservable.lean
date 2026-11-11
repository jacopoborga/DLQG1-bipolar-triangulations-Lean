/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusDecodedSide5
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55LeftLawClause

/-! observable below is a definitional copy of `m0LeftSideClassOption` made
unfoldable, not a manuscript change. No paper-completion claim is made. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: the unfoldable actual-left observable, copied
definitionally from `m0LeftSideClassOption`. -/
@[expose] noncomputable def lemma55LeftSideClassOption (x : XDP) (k : ℤ)
    (W : ℤ → Fin 3) : Option GeometricSideClass :=
  if h : Nonempty (M0LeftSideReaderWitness W
      (if x = XDP.ldp then true else false)) then
    some (geometricSideClass
      (m0GeodesicSide (Classical.choice h).hp
        ((Classical.choice h).P k) .left))
  else none

/-- Helper toward Lemma 5.5: on nonempty reader data, expose the selected
actual left-side class. -/
theorem lemma55LeftSideClassOption_eq_some_of_nonempty (x : XDP) (k : ℤ)
    (W : ℤ → Fin 3)
    (hnonempty : Nonempty (M0LeftSideReaderWitness W
      (if x = XDP.ldp then true else false))) :
    lemma55LeftSideClassOption x k W =
      some (geometricSideClass
        (m0GeodesicSide (Classical.choice hnonempty).hp
          ((Classical.choice hnonempty).P k) .left)) := by
  unfold lemma55LeftSideClassOption
  rw [dite_eq_left hnonempty]

/-- Helper toward Lemma 5.5: an empty reader has no actual left-side class. -/
theorem lemma55LeftSideClassOption_eq_none_of_isEmpty (x : XDP) (k : ℤ)
    (W : ℤ → Fin 3)
    (h : IsEmpty (M0LeftSideReaderWitness W
      (if x = XDP.ldp then true else false))) :
    lemma55LeftSideClassOption x k W = none := by
  cases x
  · have hn : ¬ Nonempty (M0LeftSideReaderWitness W true) := by
      rintro ⟨w⟩
      exact h.false w
    simp [lemma55LeftSideClassOption, hn]
  · have hn : ¬ Nonempty (M0LeftSideReaderWitness W false) := by
      rintro ⟨w⟩
      exact h.false w
    simp [lemma55LeftSideClassOption, hn]

/-- Helper toward Lemma 5.5: the actual-left observable is present almost
surely at every mode and index. -/
theorem ae_lemma55LeftSideClassOption_isSome (x : XDP) (k : ℤ) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      (lemma55LeftSideClassOption x k W).isSome := by
  cases x with
  | ldp =>
      filter_upwards [ae_m0LeftSideReaderWitness] with W hW
      have hw : Nonempty (M0LeftSideReaderWitness W true) := hW true
      simp [lemma55LeftSideClassOption, hw]
  | sdp =>
      filter_upwards [ae_m0LeftSideReaderWitness] with W hW
      have hw : Nonempty (M0LeftSideReaderWitness W false) := hW false
      simp [lemma55LeftSideClassOption, hw]

/-- Helper toward Lemma 5.5: identify the actual-left observable with the
corrected L-minus class reader almost surely at every nonpositive index. -/
theorem lemma55LeftSideClassOption_ae_eq_LMinusSidePresentation_classOption4
    (x : XDP) (k : ℤ) (hk : k ≤ 0) :
    lemma55LeftSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
      (LMinusSidePresentation.classOption4) ∘
        (fun W => decodeLMinus x k (leftSideObsNonpos x k W)) := by
  classical
  cases x with
  | ldp =>
      filter_upwards [ae_m0LeftSideReaderWitness,
        wholePlane_ae_boundaryGluing_inputs] with W hreaders hglue
      let hnonempty : Nonempty (M0LeftSideReaderWitness W true) := hreaders true
      -- Build the decoded preimage from the same choice used by the observable.
      let w : M0LeftSideReaderWitness W true := Classical.choice hnonempty
      obtain ⟨hτ, hfin, _hroot, hcoherent⟩ := hglue w.h k
      let q : LMinusPreimage XDP.ldp := {
        W := W
        h := w.h
        H := w.H
        hLL := w.hLL
        longest := true
        mode_eq := rfl
        k := k
        hk := hk
        hp := w.hp
        hτ := hτ
        hqMode := hcoherent XDP.ldp
        hfin := hfin
        P := w.P k
        Tpath := w.T k
        hleft := w.hleft k
      }
      have hactual :
          (decodeLMinus XDP.ldp k (leftSideObsNonpos XDP.ldp k W)).classOption4 =
            some (geometricSideClass (m0GeodesicSide w.hp (w.P k) .left)) := by
        simpa [q, lMinusCodeOf] using q.classOption4_eq_actual
      have hoption := lemma55LeftSideClassOption_eq_some_of_nonempty
        XDP.ldp k W hnonempty
      change lemma55LeftSideClassOption XDP.ldp k W =
        (decodeLMinus XDP.ldp k (leftSideObsNonpos XDP.ldp k W)).classOption4
      rw [hoption]
      exact hactual.symm
  | sdp =>
      filter_upwards [ae_m0LeftSideReaderWitness,
        wholePlane_ae_boundaryGluing_inputs] with W hreaders hglue
      let hnonempty : Nonempty (M0LeftSideReaderWitness W false) := hreaders false
      -- Build the decoded preimage from the same choice used by the observable.
      let w : M0LeftSideReaderWitness W false := Classical.choice hnonempty
      obtain ⟨hτ, hfin, _hroot, hcoherent⟩ := hglue w.h k
      let q : LMinusPreimage XDP.sdp := {
        W := W
        h := w.h
        H := w.H
        hLL := w.hLL
        longest := false
        mode_eq := rfl
        k := k
        hk := hk
        hp := w.hp
        hτ := hτ
        hqMode := hcoherent XDP.sdp
        hfin := hfin
        P := w.P k
        Tpath := w.T k
        hleft := w.hleft k
      }
      have hactual :
          (decodeLMinus XDP.sdp k (leftSideObsNonpos XDP.sdp k W)).classOption4 =
            some (geometricSideClass (m0GeodesicSide w.hp (w.P k) .left)) := by
        simpa [q, lMinusCodeOf] using q.classOption4_eq_actual
      have hoption := lemma55LeftSideClassOption_eq_some_of_nonempty
        XDP.sdp k W hnonempty
      change lemma55LeftSideClassOption XDP.sdp k W =
        (decodeLMinus XDP.sdp k (leftSideObsNonpos XDP.sdp k W)).classOption4
      rw [hoption]
      exact hactual.symm

end DirectedDistances.PaperProofs.Section5
end
