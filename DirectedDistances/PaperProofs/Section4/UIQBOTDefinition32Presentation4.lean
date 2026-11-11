/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTDefinition32Presentation3

/-! # UIQBOT infinite boundary frontier encoding

`IsBoundaryOrderOfInf` is a set-level frontier encoding with multiplicity
conditions. It does not express the cyclic interval order of the frontier. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open Filter

/-- Helper toward Definition 3.2: the realization drawing's external
frontier consists exactly of the two KMSW boundary streams. -/
theorem uiqbotCanonicalBoundaryPresentation_externalFrontierStream
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (e : ℕ) :
    (∃ F : (uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing.Face,
      (uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing.IsExternal F ∧
        Set.range ((uiqbotPresentationDrawing w hfin).toPlaneGraphDrawing.arc
          (kmswGeometricEdgeEquiv w hfin (uiqbotPresentationDrawing w hfin) e))
          ⊆ frontier F.val) ↔
      (∃ i, e = kmswLeftBoundaryEdge w i) ∨
      (∃ i, e = kmswRightBoundaryEdge w i) := by
  exact uiqbot_externalFrontier_iff_boundaryStream w hfin htrans hR hL0 e





























/-- Helper toward Definition 3.2: no geometric edge appears more than twice
in the canonical UIQBOT boundary index family. -/
theorem uiqbotCanonicalBoundaryPresentation_edgeOccursAtMostTwice
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (e : (uiqbotPresentationDrawing w hfin).GeometricEdge)
    (i j k : InfiniteBoundaryDartIndex
      (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0)) :
    (InfiniteBoundaryDartIndex.dart
      (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) i).1 = e →
    (InfiniteBoundaryDartIndex.dart
      (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) j).1 = e →
    (InfiniteBoundaryDartIndex.dart
      (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) k).1 = e →
    i = j ∨ i = k ∨ j = k := by
  exact uiqbot_boundaryPresentation_edge_occurs_at_most_twice
    w hfin htrans hR hL0 e i j k

/-- Helper toward Definition 3.2: two distinct canonical occurrences of one
edge have opposite dart directions. -/
theorem uiqbotCanonicalBoundaryPresentation_repeatedEdgesHaveOppositeDarts
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (e : (uiqbotPresentationDrawing w hfin).GeometricEdge)
    (i j : InfiniteBoundaryDartIndex
      (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0)) :
    i ≠ j →
    (InfiniteBoundaryDartIndex.dart
      (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) i).1 = e →
    (InfiniteBoundaryDartIndex.dart
      (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) j).1 = e →
    ∃ b c : Bool, b ≠ c ∧
      InfiniteBoundaryDartIndex.dart
        (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) i = (e, b) ∧
      InfiniteBoundaryDartIndex.dart
        (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) j = (e, c) := by
  exact uiqbot_boundaryPresentation_repeat_has_both_darts
    w hfin htrans hR hL0 e i j























































end DirectedDistances.PaperProofs.Section4

end
