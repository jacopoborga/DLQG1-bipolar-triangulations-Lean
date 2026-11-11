/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTPresentationExposed7

/-! Helpers toward Definition 3.2 for clauses of the strengthened interval-order predicate. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open MeasureTheory Filter

/-- Helper toward Definition 3.2: the labeled canonical presentation has a
valid upper-right side because that side is empty. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_UROkInf
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    UROkInf (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0) := by
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  haveI : IsEmpty P.upperRight.Index := by
    change IsEmpty Empty
    exact inferInstance
  exact UROkInf_of_isEmpty P

/-- Helper toward Definition 3.2: the labeled canonical presentation has a
valid lower-left side because that side is empty. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_LLOkInf
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    LLOkInf (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0) := by
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  haveI : IsEmpty P.lowerLeft.Index := by
    change IsEmpty Empty
    exact inferInstance
  exact LLOkInf_of_isEmpty P

/-- Helper toward Definition 3.2: endpoint labels on an empty side are
consistent whenever its two optional marks agree. -/
theorem emptyBoundarySide_endpointLabels
    {V E : Type*} {M : DirectedPlaneMapWithMissing V E}
    (B : InfiniteBoundarySide V E) [IsEmpty B.Index]
    (hlabels : B.initialVertex? = B.terminalVertex?) :
    BoundarySideEndpointLabels M B := by
  unfold BoundarySideEndpointLabels
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    refine ⟨?_, ?_⟩
    · intro hnonempty
      rcases hnonempty with ⟨i⟩
      exact isEmptyElim i
    · intro i hi
      exact isEmptyElim i
  · intro v hv
    refine ⟨?_, ?_⟩
    · intro hnonempty
      rcases hnonempty with ⟨i⟩
      exact isEmptyElim i
    · intro i hi
      exact isEmptyElim i
  · intro _ v z hv hz
    exact Option.some.inj (hv.symm.trans (hlabels.trans hz))

/-- Helper toward Definition 3.2: the empty upper-right side has correct
stored endpoint labels. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_upperRightEndpointLabels
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    BoundarySideEndpointLabels
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin))
      (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).upperRight := by
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  haveI : IsEmpty P.upperRight.Index := by
    change IsEmpty Empty
    exact inferInstance
  apply emptyBoundarySide_endpointLabels
  rfl

/-- Helper toward Definition 3.2: the empty lower-left side has correct
stored endpoint labels. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_lowerLeftEndpointLabels
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    BoundarySideEndpointLabels
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin))
      (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).lowerLeft := by
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  haveI : IsEmpty P.lowerLeft.Index := by
    change IsEmpty Empty
    exact inferInstance
  apply emptyBoundarySide_endpointLabels
  rfl

/-- Helper toward Definition 3.2: the actual UL(0) and LR(0) endpoints of the
labeled canonical presentation are both the root vertex 0. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_rootEndpointVertices
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    boundaryDartTerminal M (P.lowerRight.darts
      ((uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
        w hfin htrans hR hL0).symm 0)) = 0 ∧
    boundaryDartInitial M (P.upperLeft.darts
      ((uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
        w hfin htrans hR hL0).symm 0)) = 0 := by
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  let iLR := (uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
    w hfin htrans hR hL0).symm 0
  let iUL := (uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
    w hfin htrans hR hL0).symm 0
  have hroot : boundaryDartTerminal M (P.lowerRight.darts iLR) =
      boundaryDartInitial M (P.upperLeft.darts iUL) := by
    change boundaryDartTerminal M
        ((uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0).lowerRight.darts
          ((uiqbotCanonicalLowerRightIndexEquivX w hfin htrans hR hL0).symm 0)) =
      boundaryDartInitial M
        ((uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0).upperLeft.darts
          ((uiqbotCanonicalUpperLeftIndexEquivX w hfin htrans hR hL0).symm 0))
    exact uiqbotCanonicalBoundaryPresentationX_rootJunction w hfin htrans hR hL0
  have hreq := uiqbotCanonicalBoundaryPresentationLabeledX_requiredJoinLabels_Y
    w hfin htrans hR hL0
  have hjoinSet := uiqbotCanonicalBoundaryPresentationLabeledX_joinSet_Y
    w hfin htrans hR hL0
  have hpair : (InfiniteBoundaryDartIndex.lowerRight iLR,
      InfiniteBoundaryDartIndex.upperLeft iUL) ∈
      {p : InfiniteBoundaryDartIndex P × InfiniteBoundaryDartIndex P |
        sideNext P p.1 = none ∧
          nextNonemptySide P (sideTag P p.1) (sideTag P p.2) ∧
          uiqbotCanonicalBoundaryDartExternalSucc w hfin
              (InfiniteBoundaryDartIndex.dart P p.1) =
            InfiniteBoundaryDartIndex.dart P p.2} := by
    have hset :
        {p : InfiniteBoundaryDartIndex P × InfiniteBoundaryDartIndex P |
          sideNext P p.1 = none ∧
            nextNonemptySide P (sideTag P p.1) (sideTag P p.2) ∧
            uiqbotCanonicalBoundaryDartExternalSucc w hfin
                (InfiniteBoundaryDartIndex.dart P p.1) =
              InfiniteBoundaryDartIndex.dart P p.2} =
        {(InfiniteBoundaryDartIndex.lowerRight iLR,
          InfiniteBoundaryDartIndex.upperLeft iUL)} := by
      simpa [P, iLR, iUL] using hjoinSet
    rw [hset]
    exact Set.mem_singleton_iff.mpr rfl
  obtain ⟨hstop, hnext, hsucc⟩ := hpair
  have hreqRoot := hreq
    (InfiniteBoundaryDartIndex.lowerRight iLR)
    (InfiniteBoundaryDartIndex.upperLeft iUL) hsucc hstop hnext
  have hstored : P.lowerRight.terminalVertex? = some 0 := by rfl
  have hlabel : P.lowerRight.terminalVertex? =
      some (boundaryDartTerminal M (P.lowerRight.darts iLR)) := by
    simpa [sideTerminalVertex?, sideTag, InfiniteBoundaryDartIndex.dart_eq] using
      hreqRoot.1
  have hzero : boundaryDartTerminal M (P.lowerRight.darts iLR) = 0 := by
    exact Option.some.inj (hlabel.symm.trans hstored)
  have hzero' : boundaryDartTerminal M (P.lowerRight.darts iLR) = 0 := by
    simpa [InfiniteBoundaryDartIndex.dart_eq] using hzero
  refine ⟨hzero', ?_⟩
  calc
    boundaryDartInitial M (P.upperLeft.darts iUL) =
        boundaryDartTerminal M (P.lowerRight.darts iLR) := hroot.symm
    _ = 0 := hzero'












































































































end DirectedDistances.PaperProofs.Section4

end

