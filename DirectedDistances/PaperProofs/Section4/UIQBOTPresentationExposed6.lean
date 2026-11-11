/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTPresentationExposed5

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open MeasureTheory Filter

/-- Helper toward Definition 3.2: the exposed Y index equivalence is the
constructor-preserving equivalence for the lower-left endpoint update. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY_eq_update
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    let v := boundaryDartTerminal M (P.lowerRight.darts
      ((uiqbotCanonicalLowerRightIndexEquivX w hfin htrans hR hL0).symm 0))
    uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY
        w hfin htrans hR hL0 =
      uiqbotEndpointUpdateIndexEquiv P (some v) (some v) := by
  dsimp only
  let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  let v := boundaryDartTerminal M (P.lowerRight.darts
    ((uiqbotCanonicalLowerRightIndexEquivX w hfin htrans hR hL0).symm 0))
  apply Equiv.ext
  intro i
  cases i <;> rfl

/-- Helper toward Definition 3.2: the Y index equivalence preserves the
within-side successor, including its endpoint. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY_sideNext
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
    let Q := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    let e := uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY
      w hfin htrans hR hL0
    ∀ i : InfiniteBoundaryDartIndex Q,
      Option.map e (sideNext Q i) = sideNext P (e i) := by
  dsimp only
  let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  let v := boundaryDartTerminal M (P.lowerRight.darts
    ((uiqbotCanonicalLowerRightIndexEquivX w hfin htrans hR hL0).symm 0))
  intro i
  rw [uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY_eq_update]
  exact uiqbotEndpointUpdateIndexEquiv_sideNext P (some v) (some v) i

/-- Helper toward Definition 3.2: the Y index equivalence preserves side
labels. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY_sideTag
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
    let Q := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    let e := uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY
      w hfin htrans hR hL0
    ∀ i : InfiniteBoundaryDartIndex Q, sideTag P (e i) = sideTag Q i := by
  dsimp only
  let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  let v := boundaryDartTerminal M (P.lowerRight.darts
    ((uiqbotCanonicalLowerRightIndexEquivX w hfin htrans hR hL0).symm 0))
  intro i
  rw [uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY_eq_update]
  exact uiqbotEndpointUpdateIndexEquiv_sideTag P (some v) (some v) i

/-- Helper toward Definition 3.2: the Y index equivalence selects the same
oriented dart. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY_dart
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
    let Q := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    let e := uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY
      w hfin htrans hR hL0
    ∀ i : InfiniteBoundaryDartIndex Q,
      InfiniteBoundaryDartIndex.dart P (e i) =
        InfiniteBoundaryDartIndex.dart Q i := by
  dsimp only
  let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  let v := boundaryDartTerminal M (P.lowerRight.darts
    ((uiqbotCanonicalLowerRightIndexEquivX w hfin htrans hR hL0).symm 0))
  intro i
  rw [uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY_eq_update]
  exact uiqbotEndpointUpdateIndexEquiv_dart P (some v) (some v) i

/-- Helper toward Definition 3.2: the labeled Y join predicate is equivalent
to membership of the transported pair in the unlabeled join set. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_joinSet_mem_iff_Y
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (q : InfiniteBoundaryDartIndex
      (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0) ×
      InfiniteBoundaryDartIndex
        (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0)) :
    q ∈ uiqbotPresentationJoinSet
        (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0)
        (uiqbotCanonicalBoundaryDartExternalSucc w hfin) ↔
      (uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY
          w hfin htrans hR hL0 q.1,
        uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY
          w hfin htrans hR hL0 q.2) ∈
        uiqbotPresentationJoinSet
          (uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0)
          (uiqbotCanonicalBoundaryDartExternalSucc w hfin) := by
  let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
  let Q := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let S := uiqbotCanonicalBoundaryDartExternalSucc w hfin
  let e := uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY
    w hfin htrans hR hL0
  change (sideNext Q q.1 = none ∧
      nextNonemptySide Q (sideTag Q q.1) (sideTag Q q.2) ∧
      S (InfiniteBoundaryDartIndex.dart Q q.1) =
        InfiniteBoundaryDartIndex.dart Q q.2) ↔
    (sideNext P (e q.1) = none ∧
      nextNonemptySide P (sideTag P (e q.1)) (sideTag P (e q.2)) ∧
      S (InfiniteBoundaryDartIndex.dart P (e q.1)) =
        InfiniteBoundaryDartIndex.dart P (e q.2))
  constructor
  · rintro ⟨hstop, hnext, hsucc⟩
    refine ⟨?_, ?_, ?_⟩
    · have htransport :=
        uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY_sideNext
          w hfin htrans hR hL0 q.1
      rw [← htransport]
      simpa using hstop
    · have htag₁ :=
        uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY_sideTag
          w hfin htrans hR hL0 q.1
      have htag₂ :=
        uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY_sideTag
          w hfin htrans hR hL0 q.2
      rw [← htag₁, ← htag₂] at hnext
      have hn : nextNonemptySide Q (sideTag P (e q.1)) (sideTag P (e q.2)) ↔
          nextNonemptySide P (sideTag P (e q.1)) (sideTag P (e q.2)) := by rfl
      exact hn.mp hnext
    · have hdart₁ :=
        uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY_dart
          w hfin htrans hR hL0 q.1
      have hdart₂ :=
        uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY_dart
          w hfin htrans hR hL0 q.2
      rw [← hdart₁, ← hdart₂] at hsucc
      exact hsucc
  · rintro ⟨hstop, hnext, hsucc⟩
    refine ⟨?_, ?_, ?_⟩
    · have htransport :=
        uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY_sideNext
          w hfin htrans hR hL0 q.1
      rw [← htransport] at hstop
      simpa using hstop
    · have htag₁ :=
        uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY_sideTag
          w hfin htrans hR hL0 q.1
      have htag₂ :=
        uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY_sideTag
          w hfin htrans hR hL0 q.2
      have hn : nextNonemptySide Q (sideTag P (e q.1)) (sideTag P (e q.2)) ↔
          nextNonemptySide P (sideTag P (e q.1)) (sideTag P (e q.2)) := by rfl
      have hnext' := hn.mpr hnext
      rw [← htag₁, ← htag₂]
      exact hnext'
    · have hdart₁ :=
        uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY_dart
          w hfin htrans hR hL0 q.1
      have hdart₂ :=
        uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY_dart
          w hfin htrans hR hL0 q.2
      rw [← hdart₁, ← hdart₂]
      exact hsucc

/-- Helper toward Definition 3.2: the Y labeled join set is the image of the
unlabeled join set under the inverse Y index equivalence on both coordinates. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_joinSet_transport_Y
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
    let Q := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    let S := uiqbotCanonicalBoundaryDartExternalSucc w hfin
    let e := uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY
      w hfin htrans hR hL0
    uiqbotPresentationJoinSet Q S =
      Set.image (fun p : InfiniteBoundaryDartIndex P × InfiniteBoundaryDartIndex P =>
        (e.symm p.1, e.symm p.2)) (uiqbotPresentationJoinSet P S) := by
  classical
  let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
  let Q := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let S := uiqbotCanonicalBoundaryDartExternalSucc w hfin
  let e := uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY
    w hfin htrans hR hL0
  change uiqbotPresentationJoinSet Q S = _
  let f := fun p : InfiniteBoundaryDartIndex P × InfiniteBoundaryDartIndex P =>
    (e.symm p.1, e.symm p.2)
  ext q
  rw [uiqbotCanonicalBoundaryPresentationLabeledX_joinSet_mem_iff_Y]
  change (e q.1, e q.2) ∈ uiqbotPresentationJoinSet P S ↔
    q ∈ Set.image f (uiqbotPresentationJoinSet P S)
  constructor
  · intro h
    exact ⟨(e q.1, e q.2), h, by simp [f]⟩
  · rintro ⟨p, hp, hq⟩
    change (e.symm p.1, e.symm p.2) = q at hq
    have hp₁ : p.1 = e q.1 := by
      have h := congrArg e (congrArg Prod.fst hq)
      simpa using h
    have hp₂ : p.2 = e q.2 := by
      have h := congrArg e (congrArg Prod.snd hq)
      simpa using h
    change (p.1, p.2) ∈ uiqbotPresentationJoinSet P S at hp
    rw [hp₁, hp₂] at hp
    exact hp

/-- Helper toward Definition 3.2: the labeled Y join set consists of the
root lower-right dart and root upper-left dart. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_joinSet_Y
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    let S := uiqbotCanonicalBoundaryDartExternalSucc w hfin
    {p : InfiniteBoundaryDartIndex P × InfiniteBoundaryDartIndex P |
      sideNext P p.1 = none ∧
        nextNonemptySide P (sideTag P p.1) (sideTag P p.2) ∧
        S (InfiniteBoundaryDartIndex.dart P p.1) =
          InfiniteBoundaryDartIndex.dart P p.2} =
      {(InfiniteBoundaryDartIndex.lowerRight
          ((uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
            w hfin htrans hR hL0).symm 0),
        InfiniteBoundaryDartIndex.upperLeft
          ((uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
            w hfin htrans hR hL0).symm 0))} := by
  classical
  let P := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
  let Q := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let S := uiqbotCanonicalBoundaryDartExternalSucc w hfin
  let e := uiqbotCanonicalBoundaryPresentationLabeledXIndexEquivY
    w hfin htrans hR hL0
  change uiqbotPresentationJoinSet Q S = _
  rw [uiqbotCanonicalBoundaryPresentationLabeledX_joinSet_transport_Y
    w hfin htrans hR hL0]
  have hUnlabeled : uiqbotPresentationJoinSet P S =
      {(InfiniteBoundaryDartIndex.lowerRight
          ((uiqbotCanonicalLowerRightIndexEquivX
            w hfin htrans hR hL0).symm 0),
        InfiniteBoundaryDartIndex.upperLeft
          ((uiqbotCanonicalUpperLeftIndexEquivX
            w hfin htrans hR hL0).symm 0))} := by
    simpa only [uiqbotPresentationJoinSet] using
      uiqbotCanonicalBoundaryPresentationX_joinSet w hfin htrans hR hL0
  rw [hUnlabeled]
  simp only [Set.image_singleton]
  congr 1





































end DirectedDistances.PaperProofs.Section4

end

