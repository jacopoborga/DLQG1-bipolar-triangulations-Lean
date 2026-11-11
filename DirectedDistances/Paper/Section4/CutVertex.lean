 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.CutVertex

/-!
# Definition 4.2 (`def-cut-vertex`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/

















public section
namespace DirectedDistances.Paper.Section4

open Filter MeasureTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section4

 
theorem cutVertex_characterization :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∃! w : ℕ → Fin 3, integrateCodes w = p ∧ edgeWest w 0 = 0 ∧
        ∀ v, sourceCutVertex w v ↔ v = 0 ∨ DeletingDisconnects w v :=
 
by exact DirectedDistances.PaperProofs.SourceResults.cutVertex_characterization
 
 

end DirectedDistances.Paper.Section4
 
