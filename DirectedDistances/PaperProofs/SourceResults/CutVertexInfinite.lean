/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.TopologicalCutVertexFinal

/- # Isolated proof provider for Proposition 4.3 (`prop-cut-vertex`)

counting are separate gates. No conclusion or source hypothesis is added. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open Filter MeasureTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section4

/-- Proposition 4.3 isolated provider; packaging only. -/
theorem cut_vertex_infinite :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∃! w : ℕ → Fin 3, integrateCodes w = p ∧
        {v : ℕ | sourceCutVertex w v}.Infinite :=
by exact DirectedDistances.PaperProofs.Section4.cut_vertex_infinite_final

end DirectedDistances.PaperProofs.SourceResults
