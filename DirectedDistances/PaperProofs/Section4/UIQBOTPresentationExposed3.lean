/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTPresentationExposed2

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open MeasureTheory Filter

/-- Helper toward Definition 3.2: the unlabeled exposed presentation has only
the finite LR(0)-to-UL(0) join at a side endpoint. -/
theorem uiqbotCanonicalBoundaryPresentationX_joinSet
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
    let S := uiqbotCanonicalBoundaryDartExternalSucc w hfin
    {p : InfiniteBoundaryDartIndex P × InfiniteBoundaryDartIndex P |
      sideNext P p.1 = none ∧
        nextNonemptySide P (sideTag P p.1) (sideTag P p.2) ∧
        S (InfiniteBoundaryDartIndex.dart P p.1) =
          InfiniteBoundaryDartIndex.dart P p.2} =
      {(InfiniteBoundaryDartIndex.lowerRight
          ((uiqbotCanonicalLowerRightIndexEquivX
            w hfin htrans hR hL0).symm 0),
        InfiniteBoundaryDartIndex.upperLeft
          ((uiqbotCanonicalUpperLeftIndexEquivX
            w hfin htrans hR hL0).symm 0))} := by
  classical
  let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
  let S := uiqbotCanonicalBoundaryDartExternalSucc w hfin
  have hroot : S (P.lowerRight.darts
      ((uiqbotCanonicalLowerRightIndexEquivX
        w hfin htrans hR hL0).symm 0)) =
      P.upperLeft.darts
        ((uiqbotCanonicalUpperLeftIndexEquivX
          w hfin htrans hR hL0).symm 0) := by
    convert uiqbotCanonicalBoundaryPresentationLabeledX_rootSuccessor
      w hfin htrans hR hL0 using 1 <;> rfl
  change {p : InfiniteBoundaryDartIndex P × InfiniteBoundaryDartIndex P |
      sideNext P p.1 = none ∧
        nextNonemptySide P (sideTag P p.1) (sideTag P p.2) ∧
        S (InfiniteBoundaryDartIndex.dart P p.1) =
          InfiniteBoundaryDartIndex.dart P p.2} =
      {(InfiniteBoundaryDartIndex.lowerRight
          ((uiqbotCanonicalLowerRightIndexEquivX
            w hfin htrans hR hL0).symm 0),
        InfiniteBoundaryDartIndex.upperLeft
          ((uiqbotCanonicalUpperLeftIndexEquivX
            w hfin htrans hR hL0).symm 0))}
  ext pair
  rcases pair with ⟨i, j⟩
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hstop, hnext, hsucc⟩
    have hi := (uiqbotCanonicalBoundaryPresentationX_sideNext_none_iff
      w hfin htrans hR hL0 i).mp hstop
    rw [hi] at hnext hsucc
    have hjtag : sideTag P j = 0 := by
      apply (uiqbotCanonicalBoundaryPresentationX_nextNonemptySide
        w hfin htrans hR hL0 (sideTag P j)).mp
      simpa [sideTag] using hnext
    cases j with
    | upperLeft j =>
        rw [InfiniteBoundaryDartIndex.dart_eq,
          InfiniteBoundaryDartIndex.dart_eq] at hsucc
        change S (P.lowerRight.darts
            ((uiqbotCanonicalLowerRightIndexEquivX
              w hfin htrans hR hL0).symm 0)) = P.upperLeft.darts j at hsucc
        have hj : (uiqbotCanonicalUpperLeftIndexEquivX
            w hfin htrans hR hL0).symm 0 = j :=
          P.upperLeft.darts.injective (hroot.symm.trans hsucc)
        exact Prod.ext hi
          (congrArg InfiniteBoundaryDartIndex.upperLeft hj.symm)
    | upperRight j => cases j
    | lowerRight j => simp [sideTag] at hjtag
    | lowerLeft j => cases j
  · rintro hpair
    rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (uiqbotCanonicalBoundaryPresentationX_sideNext_none_iff
        w hfin htrans hR hL0 _).mpr rfl
    · apply (uiqbotCanonicalBoundaryPresentationX_nextNonemptySide
        w hfin htrans hR hL0 0).mpr
      rfl
    · rw [InfiniteBoundaryDartIndex.dart_eq,
        InfiniteBoundaryDartIndex.dart_eq]
      exact hroot

/-- Helper toward Definition 3.2: transporting the boundary indices to the
labeled presentation preserves the unique finite root join. -/
@[expose] def uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
    let Q := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    InfiniteBoundaryDartIndex Q ≃ InfiniteBoundaryDartIndex P := by
  let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
  let Q := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  exact {
    toFun := fun i => match i with
      | .upperLeft i => .upperLeft i
      | .upperRight i => .upperRight i
      | .lowerRight i => .lowerRight i
      | .lowerLeft i => .lowerLeft i
    invFun := fun i => match i with
      | .upperLeft i => .upperLeft i
      | .upperRight i => .upperRight i
      | .lowerRight i => .lowerRight i
      | .lowerLeft i => .lowerLeft i
    left_inv := by intro i; cases i <;> rfl
    right_inv := by intro i; cases i <;> rfl }
















































end DirectedDistances.PaperProofs.Section4

end
