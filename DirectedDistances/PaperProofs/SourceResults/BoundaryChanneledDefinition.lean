/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundaryChanneledIncoming
public import DirectedDistances.PlanarMap.KMSWMapSimpleBoundary

/-! Supporting lemmas for paper labels `def-reverse-map` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open DirectedDistances.PlanarMap

 
theorem def_reverse_map_provider {l r n : ℕ} (R : KMSWMapRep l r n) :
    ((KMSWMapIsoClass.mk R).IsChanneled ↔
      ∀ d, ¬ R.B.map.missing d → R.B.map.tail d →
        dartHeadVertex R.B.map d ∈ R.B.boundaryVerticesBase →
        dartHeadVertex R.B.map d ≠ R.B.sink →
        R.B.boundaryEdgeBase d) ∧
    (R.IsSimpleOuterBoundary →
      ((∀ d, ¬ R.B.map.missing d → R.B.map.tail d →
          dartHeadVertex R.B.map d ∈ R.B.boundaryVerticesBase →
          dartHeadVertex R.B.map d ≠ R.B.sink →
          R.B.boundaryEdgeBase d) ↔
        ∀ v, v ∈ R.B.boundaryVerticesBase →
          v ≠ R.B.source → v ≠ R.B.sink →
          ∃! d, ¬ R.B.map.missing d ∧ R.B.map.tail d ∧
            dartHeadVertex R.B.map d = v)) := by
  constructor
  · exact KMSWMapIsoClass.isChanneled_mk R
  · intro hs
    let B := R.toStrong hs
    have h := isBoundaryChanneled_iff_exactlyOneIncoming B
    exact h

end DirectedDistances.PaperProofs.SourceResults
