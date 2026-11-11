/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.RenewalTimeCharacterization

/-! Supporting lemmas for paper labels `lem-renewal` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.PaperProofs.Section4
open DirectedDistances.RandomWalk



theorem existsUnique_renewalTime (m : ℕ) (p : ℕ → ℤ × ℤ) :
    ∃! t : ℕ∞, IsPositiveSuccessTime
      (fun j => (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m t :=
  existsUnique_positiveSuccessTime
    (fun j => (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
      ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m

end DirectedDistances.PaperProofs.Section4
