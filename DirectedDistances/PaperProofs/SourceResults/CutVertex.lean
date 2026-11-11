/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.TopologicalCutVertexFinal

/- # Isolated proof provider for Definition 4.2 (`def-cut-vertex`)

counting are separate gates. No conclusion or source hypothesis is added. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open Filter MeasureTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section4

/-- Definition 4.2 isolated provider; packaging only. -/
theorem cutVertex_characterization :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∃! w : ℕ → Fin 3, integrateCodes w = p ∧ edgeWest w 0 = 0 ∧
        ∀ v, sourceCutVertex w v ↔ v = 0 ∨ DeletingDisconnects w v :=
by exact DirectedDistances.PaperProofs.Section4.cutVertex_characterization_final

end DirectedDistances.PaperProofs.SourceResults
