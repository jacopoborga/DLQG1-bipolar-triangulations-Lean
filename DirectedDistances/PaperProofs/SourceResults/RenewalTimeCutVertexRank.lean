/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.TopologicalCutVertexFinal

/- # Isolated proof provider for Lemma 4.9 A5 (`lem-renewal`)

counting are separate gates. No conclusion or source hypothesis is added. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open Filter MeasureTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section4

/-- Lemma 4.9 A5 isolated provider; packaging only. -/
theorem renewalTime_cutVertex_rank :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∃! w : ℕ → Fin 3, integrateCodes w = p ∧
        ∀ (m : ℕ) (t : ℕ∞),
          DirectedDistances.Paper.Section4.renewalTime m p = t ↔
            IsPositiveSuccessTime
              (fun n => sourceCutVertex w (activeInitial w n) ∧
                ∀ j < n, activeInitial w j ≠ activeInitial w n) m t :=
by exact DirectedDistances.PaperProofs.Section4.renewalTime_cutVertex_rank_final

end DirectedDistances.PaperProofs.SourceResults
