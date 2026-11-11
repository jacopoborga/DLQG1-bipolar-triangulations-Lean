/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTDefinition32Presentation7
import all DirectedDistances.PlanarMap.InfiniteBoundaryPresentationData

/-! # UIQBOT boundary presentation clauses

`IsBoundaryOrderOfInf` is the project's set-level encoding. The cyclic
open obligation. These helpers make no paper-completion claim. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open unitInterval

/-- Helper toward Definition 3.2: the canonical presentation satisfies the
set-level frontier, multiplicity, and repeated-edge incidence clauses. -/
theorem uiqbotCanonicalBoundaryPresentation_isBoundaryOrderOfInf
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    IsBoundaryOrderOfInf
      (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMap w hfin))
      (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) := by
  unfold IsBoundaryOrderOfInf
  refine ⟨?_, ?_, ?_⟩
  · exact uiqbotCanonicalBoundaryPresentation_frontierSet w hfin htrans hR hL0
  · exact uiqbotCanonicalBoundaryPresentation_edgeOccursAtMostTwice w hfin htrans hR hL0
  · exact uiqbotCanonicalBoundaryPresentation_repeatedEdgeIncidences w hfin htrans hR hL0




























































end DirectedDistances.PaperProofs.Section4

end
