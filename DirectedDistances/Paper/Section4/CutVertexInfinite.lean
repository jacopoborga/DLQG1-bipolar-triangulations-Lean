 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.CutVertexInfinite

/-!
# Proposition 4.3 (`prop-cut-vertex`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/






















public section
namespace DirectedDistances.Paper.Section4

open Filter MeasureTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section4

 
theorem cut_vertex_infinite :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∃! w : ℕ → Fin 3, integrateCodes w = p ∧
        {v : ℕ | sourceCutVertex w v}.Infinite :=
 
by exact DirectedDistances.PaperProofs.SourceResults.cut_vertex_infinite
 
 

end DirectedDistances.Paper.Section4
 
