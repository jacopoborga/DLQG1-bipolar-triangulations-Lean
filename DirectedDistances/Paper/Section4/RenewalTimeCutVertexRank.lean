 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.RenewalTimeCutVertexRank

/-!
# Lemma 4.9 (`lem-renewal`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/
















public section
namespace DirectedDistances.Paper.Section4

open Filter MeasureTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section4

 
theorem renewalTime_cutVertex_rank :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∃! w : ℕ → Fin 3, integrateCodes w = p ∧
        ∀ (m : ℕ) (t : ℕ∞),
          renewalTime m p = t ↔
            IsPositiveSuccessTime
              (fun n => sourceCutVertex w (activeInitial w n) ∧
                ∀ j < n, activeInitial w j ≠ activeInitial w n) m t :=
 
by exact DirectedDistances.PaperProofs.SourceResults.renewalTime_cutVertex_rank
 
 

end DirectedDistances.Paper.Section4
 
