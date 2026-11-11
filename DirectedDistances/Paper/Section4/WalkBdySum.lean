 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.WalkBdySum

/-!
# Lemma 4.12 (`lem-walk-bdy-sum`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/








public section
namespace DirectedDistances.Paper.Section4
open MeasureTheory DirectedDistances.RandomWalk
open scoped ENNReal
 
theorem walk_bdy_sum :
    ∑' n : ℕ, conditionedVectorPathLaw 0 0 {p : ℕ → ℤ × ℤ |
      (∀ j, j < n + 1 → (p (n + 1)).2 ≤ (p j).2 - 1) ∧
      ∀ j, n + 1 ≤ j → (p (n + 1)).1 ≤ (p j).1} = ∞ :=
 
by exact DirectedDistances.PaperProofs.Section4.walk_bdy_sum
 
 

end DirectedDistances.Paper.Section4
 
