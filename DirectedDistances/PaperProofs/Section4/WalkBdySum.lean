/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.BlockBoundUnconditional

/-! Supporting lemmas for paper labels `lem-cond-walk-bm`, `lem-walk-bdy-sum` (see CORRESPONDENCE.md). -/












public section
namespace DirectedDistances.PaperProofs.Section4

open MeasureTheory DirectedDistances.RandomWalk
open scoped ENNReal

/-- Lemma 4.12 (`lem-walk-bdy-sum`): `∑_{n=1}^∞ P̂_{(0,0)}[A_n ∩ B_n] = ∞`. -/
theorem walk_bdy_sum :
    ∑' n : ℕ, conditionedVectorPathLaw 0 0 {p : ℕ → ℤ × ℤ |
      (∀ j, j < n + 1 → (p (n + 1)).2 ≤ (p j).2 - 1) ∧
      ∀ j, n + 1 ≤ j → (p (n + 1)).1 ≤ (p j).1} = ∞ :=
  conditionedVectorPathLaw_tsum_success_eq_top

end DirectedDistances.PaperProofs.Section4
