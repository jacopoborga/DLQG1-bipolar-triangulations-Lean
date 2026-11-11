/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTBoundaryIntervalOrder3

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: label the degenerate lower-left side of the
canonical UIQBOT presentation at the terminal vertex of LR(0). -/
@[expose] noncomputable def uiqbotCanonicalBoundaryPresentationLabeled
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMap w hfin)
    InfiniteBoundaryPresentation M := by
  let P := uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMap w hfin)
  let v := boundaryDartTerminal M (P.lowerRight.darts
    ((uiqbotCanonicalLowerRightIndexEquiv w hfin htrans hR hL0).symm 0))
  exact { P with lowerLeft := { P.lowerLeft with
    initialVertex? := some v
    terminalVertex? := some v } }

/-- Helper toward Definition 3.2: the labeled presentation changes only the
two lower-left endpoint labels. -/
theorem uiqbotCanonicalBoundaryPresentationLabeled_otherFields
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0
    let Q := uiqbotCanonicalBoundaryPresentationLabeled w hfin htrans hR hL0
    Q.upperLeft = P.upperLeft ∧ Q.upperRight = P.upperRight ∧
      Q.lowerRight = P.lowerRight ∧ Q.lowerLeft.Index = P.lowerLeft.Index ∧
      Q.lowerLeft.darts = P.lowerLeft.darts ∧ Q.lowerLeft.next = P.lowerLeft.next := by
  exact ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, rfl⟩⟩⟩⟩⟩

/-- Helper toward Definition 3.2: the lower-left labels both equal the
terminal vertex of LR(0). -/
theorem uiqbotCanonicalBoundaryPresentationLabeled_rootLabels
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMap w hfin)
    let P := uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0
    let Q := uiqbotCanonicalBoundaryPresentationLabeled w hfin htrans hR hL0
    Q.lowerLeft.initialVertex? = some (boundaryDartTerminal M (P.lowerRight.darts
      ((uiqbotCanonicalLowerRightIndexEquiv w hfin htrans hR hL0).symm 0))) ∧
      Q.lowerLeft.terminalVertex? = some (boundaryDartTerminal M (P.lowerRight.darts
        ((uiqbotCanonicalLowerRightIndexEquiv w hfin htrans hR hL0).symm 0))) := by
  exact ⟨rfl, rfl⟩





















































































end DirectedDistances.PaperProofs.Section4

end
