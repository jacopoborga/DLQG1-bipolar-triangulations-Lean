/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.TopologicalCutVertexFinal

/- # Isolated proof provider for Lemma 4.8 (`lem-cut-equiv`)

counting are separate gates. No conclusion or source hypothesis is added. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open Filter MeasureTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section4

/-- Lemma 4.8 isolated provider; packaging only. -/
theorem cut_equiv :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∃! w : ℕ → Fin 3, integrateCodes w = p ∧
        ∀ n : ℕ,
          (sourceCutVertex w (activeInitial w n) ∧
            ∀ j < n, activeInitial w j ≠ activeInitial w n) ↔
          ((∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
            ∀ j, n ≤ j → (p n).1 ≤ (p j).1) :=
by exact DirectedDistances.PaperProofs.Section4.cut_equiv_final

end DirectedDistances.PaperProofs.SourceResults
