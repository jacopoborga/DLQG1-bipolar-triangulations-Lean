/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTIntervalOrder2Clauses

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open MeasureTheory Filter

/-- Helper toward Definition 3.2: a UL dart occurrence and an LR dart
occurrence of the labeled canonical presentation are distinct as oriented
geometric darts. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_upperLeft_ne_lowerRight_dart
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (i j : ℕ) :
    InfiniteBoundaryDartIndex.dart
        (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0)
        (.upperLeft i) ≠
      InfiniteBoundaryDartIndex.dart
        (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0)
        (.lowerRight j) := by
  let D := uiqbotPresentationDrawing w hfin
  let iota := kmswGeometricEdgeEquiv w hfin D
  let f := uiqbotKMSWQuotientDartEquiv D iota
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  have hUL : f (P.upperLeft.darts i) = (kmswLeftBoundaryEdge w i, false) := by
    change f (iota (kmswLeftBoundaryEdge w i),
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)).forward
        ⟨iota (kmswLeftBoundaryEdge w i), by simp [uiqbotMapWithNoMissing]⟩) = _
    exact uiqbotKMSWQuotientDartEquiv_directed D iota (kmswLeftBoundaryEdge w i)
  have hLR : f (P.lowerRight.darts j) = (kmswRightBoundaryEdge w j, true) := by
    change f (iota (kmswRightBoundaryEdge w j),
      !(uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)).forward
        ⟨iota (kmswRightBoundaryEdge w j), by simp [uiqbotMapWithNoMissing]⟩) = _
    simpa [uiqbotMapWithNoMissing, uiqbotPresentationDirectedMapX] using
      uiqbotKMSWQuotientDartEquiv_reverseDirected D iota
        (kmswRightBoundaryEdge w j)
  intro h
  rw [InfiniteBoundaryDartIndex.dart_eq, InfiniteBoundaryDartIndex.dart_eq] at h
  have h' := congrArg f h
  rw [hUL, hLR] at h'
  have hbits := congrArg Prod.snd h'
  cases hbits

/-- Helper toward Definition 3.2: the external successor joins the last LR
dart, at constructor index zero, to the first UL dart at constructor index
zero. -/
theorem uiqbotCanonicalBoundaryDartExternalSucc_labeled_rootJunction
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    uiqbotCanonicalBoundaryDartExternalSucc w hfin
        (P.lowerRight.darts
          ((uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
            w hfin htrans hR hL0).symm 0)) =
      P.upperLeft.darts
        ((uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
          w hfin htrans hR hL0).symm 0) := by
  convert uiqbotCanonicalBoundaryPresentationLabeledX_rootSuccessor
    w hfin htrans hR hL0 using 1 <;> rfl

/-- Helper toward Definition 3.2: after unfolding the unguarded join-label
predicate, its only constrained pair is the terminal LR(0) dart and the
initial UL(0) dart. The UR and LL index types are empty. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_unconditionalJoinSet
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    let S := uiqbotCanonicalBoundaryDartExternalSucc w hfin
    let iLR := (uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
      w hfin htrans hR hL0).symm 0
    let iUL := (uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
      w hfin htrans hR hL0).symm 0
    {p : InfiniteBoundaryDartIndex P × InfiniteBoundaryDartIndex P |
      sideNext P p.1 = none ∧
        S (InfiniteBoundaryDartIndex.dart P p.1) =
          InfiniteBoundaryDartIndex.dart P p.2} =
      {(InfiniteBoundaryDartIndex.lowerRight iLR,
        InfiniteBoundaryDartIndex.upperLeft iUL)} := by
  classical
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let S := uiqbotCanonicalBoundaryDartExternalSucc w hfin
  let iLR := (uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
    w hfin htrans hR hL0).symm 0
  let iUL := (uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
    w hfin htrans hR hL0).symm 0
  have hroot' : uiqbotCanonicalBoundaryDartExternalSucc w hfin
      ((uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).lowerRight.darts
        ((uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
          w hfin htrans hR hL0).symm 0)) =
      (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).upperLeft.darts
        ((uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
          w hfin htrans hR hL0).symm 0) :=
    uiqbotCanonicalBoundaryPresentationLabeledX_rootSuccessor
      w hfin htrans hR hL0
  have hrootP : S (P.lowerRight.darts
      ((uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
        w hfin htrans hR hL0).symm 0)) =
      P.upperLeft.darts
        ((uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
          w hfin htrans hR hL0).symm 0) := by
    change uiqbotCanonicalBoundaryDartExternalSucc w hfin
      ((uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).lowerRight.darts
        ((uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
          w hfin htrans hR hL0).symm 0)) =
      (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).upperLeft.darts
        ((uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
          w hfin htrans hR hL0).symm 0)
    exact hroot'
  change {p : InfiniteBoundaryDartIndex P × InfiniteBoundaryDartIndex P |
      sideNext P p.1 = none ∧
        S (InfiniteBoundaryDartIndex.dart P p.1) =
          InfiniteBoundaryDartIndex.dart P p.2} = _
  ext pair
  rcases pair with ⟨i, j⟩
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hstop, hsucc⟩
    cases i with
    | upperLeft i =>
        simp [sideNext, P, uiqbotCanonicalBoundaryPresentationLabeledX,
          uiqbotCanonicalBoundaryPresentationX, uiqbotDefinition32Presentation] at hstop
    | upperRight i => cases i
    | lowerLeft i => cases i
    | lowerRight i =>
        change ℕ at i
        have hi : i = (uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
            w hfin htrans hR hL0).symm 0 := by
          have hi0 : i = 0 := by
            by_cases hi0 : i = 0
            · exact hi0
            · simp [sideNext, P, uiqbotCanonicalBoundaryPresentationLabeledX,
                uiqbotCanonicalBoundaryPresentationX, uiqbotDefinition32Presentation,
                hi0] at hstop
          convert hi0 using 1 <;> rfl
        subst i
        cases j with
        | upperLeft j =>
            change ℕ at j
            rw [InfiniteBoundaryDartIndex.dart_eq,
              InfiniteBoundaryDartIndex.dart_eq] at hsucc
            change S (P.lowerRight.darts
              ((uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
                w hfin htrans hR hL0).symm 0)) = P.upperLeft.darts j at hsucc
            have hsucc' : S (P.lowerRight.darts
                ((uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
                  w hfin htrans hR hL0).symm 0)) = P.upperLeft.darts j := by
              exact hsucc
            have hj : (uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
                w hfin htrans hR hL0).symm 0 = j :=
              P.upperLeft.darts.injective (hrootP.symm.trans hsucc')
            subst j
            apply Set.mem_singleton_iff.mpr
            simp [iLR, iUL,
              uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv,
              uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv] <;> rfl
        | upperRight j => cases j
        | lowerLeft j => cases j
        | lowerRight j =>
            change ℕ at j
            rw [InfiniteBoundaryDartIndex.dart_eq,
              InfiniteBoundaryDartIndex.dart_eq] at hsucc
            change S (P.lowerRight.darts
              ((uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
                w hfin htrans hR hL0).symm 0)) = P.lowerRight.darts j at hsucc
            have hsucc' : S (P.lowerRight.darts
                ((uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
                  w hfin htrans hR hL0).symm 0)) = P.lowerRight.darts j := by
              exact hsucc
            have hbad : P.upperLeft.darts
                ((uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
                  w hfin htrans hR hL0).symm 0) = P.lowerRight.darts j :=
              hrootP.symm.trans hsucc'
            have hbad' : InfiniteBoundaryDartIndex.dart P (.upperLeft
                ((uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
                  w hfin htrans hR hL0).symm 0)) =
                InfiniteBoundaryDartIndex.dart P (.lowerRight j) := by
              rw [InfiniteBoundaryDartIndex.dart_eq, InfiniteBoundaryDartIndex.dart_eq]
              exact hbad
            exact False.elim
              ((uiqbotCanonicalBoundaryPresentationLabeledX_upperLeft_ne_lowerRight_dart
                w hfin htrans hR hL0
                ((uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
                  w hfin htrans hR hL0).symm 0) j) hbad')
  · intro hp
    rcases Set.mem_singleton_iff.mp hp with hp
    rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · simp [sideNext, P, iLR,
        uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv,
        uiqbotCanonicalBoundaryPresentationLabeledX,
        uiqbotCanonicalBoundaryPresentationX, uiqbotDefinition32Presentation,
        Equiv.refl, id] <;> rfl
    · rw [InfiniteBoundaryDartIndex.dart_eq, InfiniteBoundaryDartIndex.dart_eq]
      change S (P.lowerRight.darts
        ((uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
          w hfin htrans hR hL0).symm 0)) = P.upperLeft.darts
          ((uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
            w hfin htrans hR hL0).symm 0)
      exact hroot'

/-- Helper toward Definition 3.2: the labeled canonical presentation
satisfies the unguarded boundary join endpoint-label predicate. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_BoundaryJoinEndpointLabels
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    BoundaryJoinEndpointLabels P (uiqbotCanonicalBoundaryDartExternalSucc w hfin) := by
  classical
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let S := uiqbotCanonicalBoundaryDartExternalSucc w hfin
  let iLR := (uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
    w hfin htrans hR hL0).symm 0
  let iUL := (uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
    w hfin htrans hR hL0).symm 0
  have hrequired : RequiredBoundaryJoinEndpointLabels P S := by
    simpa [P, S] using
      uiqbotCanonicalBoundaryPresentationLabeledX_requiredJoinLabels_Y
        w hfin htrans hR hL0
  have hroot' : uiqbotCanonicalBoundaryDartExternalSucc w hfin
      ((uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).lowerRight.darts
        ((uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
          w hfin htrans hR hL0).symm 0)) =
      (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).upperLeft.darts
        ((uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
          w hfin htrans hR hL0).symm 0) :=
    uiqbotCanonicalBoundaryPresentationLabeledX_rootSuccessor
      w hfin htrans hR hL0
  have hrootP : S (P.lowerRight.darts iLR) = P.upperLeft.darts iUL := by
    change uiqbotCanonicalBoundaryDartExternalSucc w hfin
      ((uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).lowerRight.darts
        ((uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
          w hfin htrans hR hL0).symm 0)) =
      (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).upperLeft.darts
        ((uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
          w hfin htrans hR hL0).symm 0)
    exact hroot'
  have hstop : sideNext P (.lowerRight iLR) = none := by
    simp [sideNext, P, iLR,
      uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv,
      uiqbotCanonicalBoundaryPresentationLabeledX,
      uiqbotCanonicalBoundaryPresentationX, uiqbotDefinition32Presentation,
      Equiv.refl, id] <;> rfl
  have hUL : Nonempty P.upperLeft.Index := ⟨iUL⟩
  have hLR : Nonempty P.lowerRight.Index := ⟨iLR⟩
  have hUR : IsEmpty P.upperRight.Index := by
    change IsEmpty Empty
    infer_instance
  have hLL : IsEmpty P.lowerLeft.Index := by
    change IsEmpty Empty
    infer_instance
  have hnext : nextNonemptySide P 2 0 := by
    unfold nextNonemptySide
    refine ⟨hUL, by norm_num [sideDistance], ?_⟩
    intro c hc₁ hc₂
    fin_cases c <;> simp_all [sideDistance, sideNonempty]
  change ∀ i j : InfiniteBoundaryDartIndex P,
    S (InfiniteBoundaryDartIndex.dart P i) = InfiniteBoundaryDartIndex.dart P j →
    sideNext P i = none →
    let v := boundaryDartTerminal
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin))
      (InfiniteBoundaryDartIndex.dart P i)
    (∀ z, sideTerminalVertex? P (sideTag P i) = some z → z = v) ∧
      (∀ z, sideInitialVertex? P (sideTag P j) = some z → z = v) ∧
      ∀ k : Fin 4,
        0 < sideDistance (sideTag P i) k →
        sideDistance (sideTag P i) k < sideDistance (sideTag P i) (sideTag P j) →
        (∀ z, sideInitialVertex? P k = some z → z = v) ∧
        (∀ z, sideTerminalVertex? P k = some z → z = v)
  intro i j hsucc hstop
  have hpair : (i, j) ∈ {p : InfiniteBoundaryDartIndex P × InfiniteBoundaryDartIndex P |
      sideNext P p.1 = none ∧
        S (InfiniteBoundaryDartIndex.dart P p.1) =
          InfiniteBoundaryDartIndex.dart P p.2} := ⟨hstop, hsucc⟩
  have hset : {p : InfiniteBoundaryDartIndex P × InfiniteBoundaryDartIndex P |
      sideNext P p.1 = none ∧
        S (InfiniteBoundaryDartIndex.dart P p.1) =
          InfiniteBoundaryDartIndex.dart P p.2} =
      {(InfiniteBoundaryDartIndex.lowerRight iLR,
        InfiniteBoundaryDartIndex.upperLeft iUL)} := by
    simpa [P, S] using
      uiqbotCanonicalBoundaryPresentationLabeledX_unconditionalJoinSet
        w hfin htrans hR hL0
  rw [hset] at hpair
  have hp := Set.mem_singleton_iff.mp hpair
  have hi : i = .lowerRight iLR := congrArg Prod.fst hp
  have hj : j = .upperLeft iUL := congrArg Prod.snd hp
  subst i
  subst j
  have hrootDart : S (InfiniteBoundaryDartIndex.dart P (.lowerRight iLR)) =
      InfiniteBoundaryDartIndex.dart P (.upperLeft iUL) := by
    rw [InfiniteBoundaryDartIndex.dart_eq, InfiniteBoundaryDartIndex.dart_eq]
    change S (P.lowerRight.darts
      ((uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
        w hfin htrans hR hL0).symm 0)) = P.upperLeft.darts
        ((uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
          w hfin htrans hR hL0).symm 0)
    exact hrootP
  have hlabels := hrequired (.lowerRight iLR) (.upperLeft iUL) hrootDart hstop
    (by simpa [sideTag] using hnext)
  rcases hlabels with ⟨hterminal, hinitial, hintervening⟩
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact Option.some.inj (hz.symm.trans hterminal)
  · intro z hz
    exact Option.some.inj (hz.symm.trans hinitial)
  · intro k hk₁ hk₂
    rcases hintervening k hk₁ hk₂ with ⟨hki, hkt⟩
    constructor
    · intro z hz
      exact Option.some.inj (hz.symm.trans hki)
    · intro z hz
      exact Option.some.inj (hz.symm.trans hkt)

end DirectedDistances.PaperProofs.Section4

end

