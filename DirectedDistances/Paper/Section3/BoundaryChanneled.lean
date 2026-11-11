 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.BoundaryChanneledDefinition

/-!
# Definition 3.17 (`def-reverse-map`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/














public section
namespace DirectedDistances.Paper.Section3

open DirectedDistances.PlanarMap

 
theorem def_reverse_map {l r n : ℕ} (R : KMSWMapRep l r n) :
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
            dartHeadVertex R.B.map d = v)) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.def_reverse_map_provider R
 
 

end DirectedDistances.Paper.Section3
 
