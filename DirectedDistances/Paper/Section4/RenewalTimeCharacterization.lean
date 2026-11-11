 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.RenewalTimeCharacterization

/-!
# Lemma 4.9 (`lem-renewal`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/







public section
namespace DirectedDistances.Paper.Section4
open DirectedDistances.RandomWalk



theorem renewalTime_characterization (m : ℕ) (p : ℕ → ℤ × ℤ) :
    IsPositiveSuccessTime
      (fun j => (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m (renewalTime m p) ∧
      ∀ t : ℕ∞, renewalTime m p = t ↔
        IsPositiveSuccessTime
          (fun j => (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
            ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m t :=
 
by exact DirectedDistances.PaperProofs.Section4.renewalTime_characterization m p
 
 

end DirectedDistances.Paper.Section4
 
