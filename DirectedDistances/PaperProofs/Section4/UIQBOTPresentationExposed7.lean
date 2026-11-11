/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTPresentationExposed6

/-! Helper toward Definition 3.2: endpoint labels at the unique finite root
join of the labeled canonical UIQBOT boundary presentation. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open MeasureTheory Filter

/-- Helper toward Definition 3.2: the unique root join has its incident
endpoint labels and the labels on every intervening empty side. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_requiredJoinLabels_Y
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    RequiredBoundaryJoinEndpointLabels P
      (uiqbotCanonicalBoundaryDartExternalSucc w hfin) := by
  dsimp only [RequiredBoundaryJoinEndpointLabels]
  let X := uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0
  let Q := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  let S := uiqbotCanonicalBoundaryDartExternalSucc w hfin
  let iLRidxQ := (uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
    w hfin htrans hR hL0).symm 0
  let iULidxQ := (uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
    w hfin htrans hR hL0).symm 0
  let iLRidxX := (uiqbotCanonicalLowerRightIndexEquivX
    w hfin htrans hR hL0).symm 0
  let iULidxX := (uiqbotCanonicalUpperLeftIndexEquivX
    w hfin htrans hR hL0).symm 0
  let iLR : InfiniteBoundaryDartIndex Q := .lowerRight iLRidxQ
  let iUL : InfiniteBoundaryDartIndex Q := .upperLeft iULidxQ
  have hULdarts : Q.upperLeft.darts iULidxQ = X.upperLeft.darts iULidxX := by
    simp [iULidxQ, iULidxX, Q, X,
      uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv,
      uiqbotCanonicalUpperLeftIndexEquivX,
      uiqbotCanonicalBoundaryPresentationLabeledX]; rfl
  have hLRdarts : Q.lowerRight.darts iLRidxQ = X.lowerRight.darts iLRidxX := by
    simp [iLRidxQ, iLRidxX, Q, X,
      uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv,
      uiqbotCanonicalLowerRightIndexEquivX,
      uiqbotCanonicalBoundaryPresentationLabeledX]; rfl
  have hroot :
      boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart Q iLR) =
        boundaryDartInitial M (InfiniteBoundaryDartIndex.dart Q iUL) := by
    rw [InfiniteBoundaryDartIndex.dart_eq, InfiniteBoundaryDartIndex.dart_eq]
    simp [iLR, iUL]
    rw [hLRdarts, hULdarts]
    simpa [iLR, iUL, iLRidxX, iULidxX, X, M,
      uiqbotCanonicalLowerRightIndexEquivX,
      uiqbotCanonicalUpperLeftIndexEquivX,
      uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv,
      uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv] using
        uiqbotCanonicalBoundaryPresentationX_rootJunction
          w hfin htrans hR hL0
  have hULzero :
      boundaryDartInitial M (InfiniteBoundaryDartIndex.dart Q iUL) = 0 := by
    rw [InfiniteBoundaryDartIndex.dart_eq]
    simp [iUL]
    rw [hULdarts]
    let D := uiqbotPresentationDirectedMapX w hfin
    let M0 := uiqbotMapWithNoMissing D
    let iota := kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin)
    have hmiss (e : ℕ) : ¬ M.toPlaneMapWithMissing.missing (iota e) := by
      simp [M, uiqbotMapWithNoMissing]
    have hcompat (e : ℕ) :
        D.tail (iota e) = edgeWest w e ∧ D.head (iota e) = edgeEast w e := by
      have hiota :
          iota e = Quotient.mk (uiqbotPresentationDrawing w hfin).edgeSetoid (e, false) :=
        kmswGeometricEdgeEquiv_apply w hfin (uiqbotPresentationDrawing w hfin) e
      have htail (q : (uiqbotPresentationDrawing w hfin).GeometricEdge) :
          D.tail q = (if !q.out.2 then kmswLimitDartVertex w q.out
            else kmswLimitDartVertex w (q.out.1, !q.out.2)) := by rfl
      have hhead (q : (uiqbotPresentationDrawing w hfin).GeometricEdge) :
          D.head q = (if !q.out.2 then kmswLimitDartVertex w (q.out.1, !q.out.2)
            else kmswLimitDartVertex w q.out) := by rfl
      rw [hiota, htail, hhead]
      obtain hout | hout :=
        (uiqbotPresentationDrawing w hfin).geometricEdge_out_mk (e, false)
      · rw [hout]
        simp [kmswLimitDartVertex, edgeWest, edgeEast]
      · rw [hout]
        simp [kmswLimitDartVertex, edgeWest, edgeEast]
    have hULinitial (e : ℕ) :
        boundaryDartInitial M
            (iota e, M0.forward ⟨iota e, hmiss e⟩) = edgeWest w e := by
      by_cases hf : D.forward (iota e)
      · simpa [boundaryDartInitial_eq, M, M0, uiqbotMapWithNoMissing, hf,
          D, DirectedPlaneMap.head, DirectedPlaneMap.tail] using hcompat e |>.1
      · simpa [boundaryDartInitial_eq, M, M0, uiqbotMapWithNoMissing, hf,
          D, DirectedPlaneMap.head, DirectedPlaneMap.tail] using hcompat e |>.1
    have hleftzero : edgeWest w (kmswLeftBoundaryEdge w 0) = 0 :=
      (kmswLeftBoundary_infinite_present_path w htrans hL0 hR).2.2.1
    change boundaryDartInitial M
      (iota (kmswLeftBoundaryEdge w 0),
        M0.forward ⟨iota (kmswLeftBoundaryEdge w 0), hmiss _⟩) = 0
    rw [hULinitial, hleftzero]
  have hLRzero :
      boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart Q iLR) = 0 :=
    hroot.trans hULzero
  have hLLlabels :
      Q.lowerLeft.initialVertex? =
          some (boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart Q iLR)) ∧
        Q.lowerLeft.terminalVertex? =
          some (boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart Q iLR)) := by
    rw [InfiniteBoundaryDartIndex.dart_eq]
    simp [iLR]
    rw [hLRdarts]
    simpa [iLR, iLRidxX, X, M,
      uiqbotCanonicalLowerRightIndexEquivX,
      uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv] using
        uiqbotCanonicalBoundaryPresentationLabeled_rootLabelsX
          w hfin htrans hR hL0
  have hLRlabel :
      Q.lowerRight.terminalVertex? =
        some (boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart Q iLR)) := by
    have hstored : Q.lowerRight.terminalVertex? = some 0 := by rfl
    rw [hLRzero]
    exact hstored
  have hULlabel :
      Q.upperLeft.initialVertex? =
        some (boundaryDartTerminal M (InfiniteBoundaryDartIndex.dart Q iLR)) := by
    have hstored : Q.upperLeft.initialVertex? = some 0 := by rfl
    rw [hLRzero]
    exact hstored
  intro i j hsucc hstop hnext
  have hij : (i, j) ∈ uiqbotPresentationJoinSet Q S := by
    change sideNext Q i = none ∧
      nextNonemptySide Q (sideTag Q i) (sideTag Q j) ∧
      S (InfiniteBoundaryDartIndex.dart Q i) =
        InfiniteBoundaryDartIndex.dart Q j
    exact ⟨hstop, hnext, hsucc⟩
  have hclass : uiqbotPresentationJoinSet Q S = {(iLR, iUL)} := by
    simpa [Q, S, iLR, iUL, iLRidxQ, iULidxQ, uiqbotPresentationJoinSet,
      uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv,
      uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv] using
        uiqbotCanonicalBoundaryPresentationLabeledX_joinSet_Y
          w hfin htrans hR hL0
  rw [hclass] at hij
  have heq : (i, j) = (iLR, iUL) := Set.mem_singleton_iff.mp hij
  have hi : i = iLR := congrArg Prod.fst heq
  have hj : j = iUL := congrArg Prod.snd heq
  subst i
  subst j
  refine ⟨hLRlabel, hULlabel, ?_⟩
  intro k hk₁ hk₂
  have htagLR :
      sideTag (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0) iLR =
        (2 : Fin 4) := by simp [iLR, sideTag]
  have htagUL :
      sideTag (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0) iUL =
        (0 : Fin 4) := by simp [iUL, sideTag]
  have hk : k = (3 : Fin 4) := by
    rw [htagLR] at hk₁ hk₂
    rw [htagUL] at hk₂
    fin_cases k
    · norm_num [sideDistance] at hk₂
    · norm_num [sideDistance] at hk₂
    · norm_num [sideDistance] at hk₁
    · rfl
  subst k
  simpa [sideInitialVertex?, sideTerminalVertex?] using hLLlabels

end DirectedDistances.PaperProofs.Section4

end
