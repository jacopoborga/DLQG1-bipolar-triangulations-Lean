 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.CutEquiv

/-!
# Lemma 4.8 (`lem-cut-equiv`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/















public section
namespace DirectedDistances.Paper.Section4

open Filter MeasureTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section4

 
theorem cut_equiv :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∃! w : ℕ → Fin 3, integrateCodes w = p ∧
        ∀ n : ℕ,
          (sourceCutVertex w (activeInitial w n) ∧
            ∀ j < n, activeInitial w j ≠ activeInitial w n) ↔
          ((∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
            ∀ j, n ≤ j → (p n).1 ≤ (p j).1) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.cut_equiv
 
 

end DirectedDistances.Paper.Section4
 
