/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTExternalFaceIntervalOrderInstance
public import DirectedDistances.PaperProofs.Section4.UIQBOTOkInf

/-! # Labeled UIQBOT external-face interval-order instance

Helpers toward Definition 3.2. This file transfers the KMSW boundary-ray
classification to the labeled presentation on the quotient dart carrier. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open Filter

/-- Helper toward Definition 3.2: the external darts of the KMSW limit map,
transported to the quotient carrier, are exactly the darts enumerated by the
labeled canonical UIQBOT presentation. -/
theorem uiqbotCanonicalBoundaryPresentationLabeledX_externalDartCoverage
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
    let D := uiqbotPresentationDrawing w hfin
    let iota := kmswGeometricEdgeEquiv w hfin D
    let f := uiqbotKMSWQuotientDartEquiv D iota
    ∀ d, limitExternalDart w (f d) ↔
      ∃ i : InfiniteBoundaryDartIndex P,
        InfiniteBoundaryDartIndex.dart P i = d := by
  dsimp only
  let D := uiqbotPresentationDrawing w hfin
  let iota := kmswGeometricEdgeEquiv w hfin D
  let f := uiqbotKMSWQuotientDartEquiv D iota
  let e := f.symm
  let P := uiqbotCanonicalBoundaryPresentationLabeledX w hfin htrans hR hL0
  have hUL (i : ℕ) : P.upperLeft.darts i = e (kmswLeftBoundaryEdge w i, false) := by
    apply f.injective
    calc
      f (P.upperLeft.darts i) = (kmswLeftBoundaryEdge w i, false) := by
        change f (iota (kmswLeftBoundaryEdge w i),
          (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)).forward
            ⟨iota (kmswLeftBoundaryEdge w i), by simp [uiqbotMapWithNoMissing]⟩) = _
        exact uiqbotKMSWQuotientDartEquiv_directed D iota
          (kmswLeftBoundaryEdge w i)
      _ = f (e (kmswLeftBoundaryEdge w i, false)) := by simp [e]
  have hLR (i : ℕ) : P.lowerRight.darts i = e (kmswRightBoundaryEdge w i, true) := by
    apply f.injective
    calc
      f (P.lowerRight.darts i) = (kmswRightBoundaryEdge w i, true) := by
        change f (iota (kmswRightBoundaryEdge w i),
          !(uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)).forward
            ⟨iota (kmswRightBoundaryEdge w i), by simp [uiqbotMapWithNoMissing]⟩) = _
        simpa [uiqbotMapWithNoMissing, uiqbotPresentationDirectedMapX] using
          uiqbotKMSWQuotientDartEquiv_reverseDirected D iota
            (kmswRightBoundaryEdge w i)
      _ = f (e (kmswRightBoundaryEdge w i, true)) := by simp [e]
  intro d
  rw [limitExternalDart_iff w htrans hR hL0 (f d)]
  constructor
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · refine ⟨.upperLeft i, ?_⟩
      rw [InfiniteBoundaryDartIndex.dart_eq]
      have heq : d = e (kmswLeftBoundaryEdge w i, false) := by
        simpa [e] using congrArg e hi
      exact (hUL i).trans heq.symm
    · refine ⟨.lowerRight i, ?_⟩
      rw [InfiniteBoundaryDartIndex.dart_eq]
      have heq : d = e (kmswRightBoundaryEdge w i, true) := by
        simpa [e] using congrArg e hi
      exact (hLR i).trans heq.symm
  · rintro ⟨i, hi⟩
    cases i with
    | upperLeft i =>
        rw [InfiniteBoundaryDartIndex.dart_eq] at hi
        left
        refine ⟨i, ?_⟩
        have hd : f (P.upperLeft.darts i) = f d := congrArg f hi
        have hdart : f (P.upperLeft.darts i) =
            (kmswLeftBoundaryEdge w i, false) := by
          simpa [e] using congrArg f (hUL i)
        exact hd.symm.trans hdart
    | upperRight i => cases i
    | lowerRight i =>
        rw [InfiniteBoundaryDartIndex.dart_eq] at hi
        right
        refine ⟨i, ?_⟩
        have hd : f (P.lowerRight.darts i) = f d := congrArg f hi
        have hdart : f (P.lowerRight.darts i) =
            (kmswRightBoundaryEdge w i, true) := by
          simpa [e] using congrArg f (hLR i)
        exact hd.symm.trans hdart
    | lowerLeft i => cases i














































































































end DirectedDistances.PaperProofs.Section4

end
