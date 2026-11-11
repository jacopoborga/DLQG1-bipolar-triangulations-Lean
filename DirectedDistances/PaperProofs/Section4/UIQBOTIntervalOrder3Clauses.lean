/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTIntervalOrder2Clauses

/-! Helpers toward Definition 3.2 for the remaining canonical UIQBOT side clauses. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open MeasureTheory Filter

/-- Helper toward Definition 3.2: the labeled canonical upper-left side has
the stored root label at its first traversal vertex. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_upperLeftEndpointLabels
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    BoundarySideEndpointLabels
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin))
      (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).upperLeft := by
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  let iUL := (uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv
    w hfin htrans hR hL0).symm 0
  change ℕ at iUL
  have hiUL : iUL = 0 := by rfl
  have hnext (i : ℕ) :
      (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).upperLeft.next i =
        some (i + 1) := by
    simp [uiqbotCanonicalBoundaryPresentationLabeledX,
      uiqbotCanonicalBoundaryPresentationX, uiqbotDefinition32Presentation]
  have hroot : boundaryDartInitial M
      ((uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).upperLeft.darts
        iUL) = 0 := by
    simpa [iUL, uiqbotCanonicalBoundaryPresentationLabeledXUpperLeftIndexEquiv] using
      (uiqbotCanonicalBoundaryPresentationLabeledX_rootEndpointVertices
        w hfin htrans hR hL0).2
  unfold BoundarySideEndpointLabels
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    change P.upperLeft.initialVertex? = some v at hv
    have hlabel : P.upperLeft.initialVertex? = some (0 : ℕ) := by
      simp only [P, uiqbotCanonicalBoundaryPresentationLabeledX,
        uiqbotCanonicalBoundaryPresentationX, uiqbotDefinition32Presentation]
    have hv0 : (0 : ℕ) = v := by
      have h : (some (0 : ℕ)) = some v := hlabel.symm.trans hv
      exact Option.some.inj h
    refine ⟨?_, ?_⟩
    · intro _
      refine ⟨iUL, ?_, ?_⟩
      · intro j hj
        change ℕ at j
        rw [hnext j] at hj
        have heq : j + 1 = iUL := Option.some.inj hj
        rw [hiUL] at heq
        exact Nat.succ_ne_zero j heq
      · exact hroot.trans hv0
    · intro i hi
      change ℕ at i
      cases i with
      | zero =>
          change boundaryDartInitial M
            ((uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).upperLeft.darts
              (0 : ℕ)) = v
          simpa [hiUL] using hroot.trans hv0
      | succ i =>
          exfalso
          have hcontra :
              (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).upperLeft.next i =
                some i.succ := by
            rw [hnext]
          exact hi i hcontra
  · intro v hv
    change P.upperLeft.terminalVertex? = some v at hv
    have hterminal : P.upperLeft.terminalVertex? = none := by
      simp only [P, uiqbotCanonicalBoundaryPresentationLabeledX,
        uiqbotCanonicalBoundaryPresentationX, uiqbotDefinition32Presentation]
    have : False := by
      rw [hterminal] at hv
      cases hv
    exact False.elim this
  · intro hempty v z hv hz
    exact False.elim (hempty.false iUL)

/-- Helper toward Definition 3.2: the labeled canonical lower-right side
stops at its stored root label. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_lowerRightEndpointLabels
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    BoundarySideEndpointLabels
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin))
      (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).lowerRight := by
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  let iLR := (uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv
    w hfin htrans hR hL0).symm 0
  change ℕ at iLR
  have hiLR : iLR = 0 := by rfl
  have hnext (i : ℕ) :
      (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).lowerRight.next i =
        (if i = 0 then none else some (i - 1)) := by
    simp [uiqbotCanonicalBoundaryPresentationLabeledX,
      uiqbotCanonicalBoundaryPresentationX, uiqbotDefinition32Presentation]
  have hroot : boundaryDartTerminal M
      ((uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).lowerRight.darts
        iLR) = 0 := by
    simpa [iLR, uiqbotCanonicalBoundaryPresentationLabeledXLowerRightIndexEquiv] using
      (uiqbotCanonicalBoundaryPresentationLabeledX_rootEndpointVertices
        w hfin htrans hR hL0).1
  unfold BoundarySideEndpointLabels
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    change P.lowerRight.initialVertex? = some v at hv
    have hinitial : P.lowerRight.initialVertex? = none := by
      simp only [P, uiqbotCanonicalBoundaryPresentationLabeledX,
        uiqbotCanonicalBoundaryPresentationX, uiqbotDefinition32Presentation]
    rw [hinitial] at hv
    cases hv
  · intro v hv
    change P.lowerRight.terminalVertex? = some v at hv
    have hlabel : P.lowerRight.terminalVertex? = some (0 : ℕ) := by
      simp only [P, uiqbotCanonicalBoundaryPresentationLabeledX,
        uiqbotCanonicalBoundaryPresentationX, uiqbotDefinition32Presentation]
    have hv0 : (0 : ℕ) = v := by
      have h : (some (0 : ℕ)) = some v := hlabel.symm.trans hv
      exact Option.some.inj h
    refine ⟨?_, ?_⟩
    · intro _
      refine ⟨iLR, ?_, ?_⟩
      · have hzero :
            (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).lowerRight.next
              (0 : ℕ) = none := by
          rw [hnext (0 : ℕ)]
          rfl
        change (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).lowerRight.next
          iLR = none
        rw [hiLR]
        exact hzero
      · exact hroot.trans hv0
    · intro i hi
      change ℕ at i
      cases i with
      | zero =>
          change boundaryDartTerminal M
            ((uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).lowerRight.darts
              (0 : ℕ)) = v
          simpa [hiLR] using hroot.trans hv0
      | succ i =>
          exfalso
          change (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).lowerRight.next
            i.succ = none at hi
          have hEq :
              (uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0).lowerRight.next
                i.succ = some i := by
            rw [hnext]
            rfl
          have hbad : (some i : Option ℕ) = none := hEq.symm.trans hi
          cases hbad
  · intro hempty v z hv hz
    exact False.elim (hempty.false iLR)































































































end DirectedDistances.PaperProofs.Section4
