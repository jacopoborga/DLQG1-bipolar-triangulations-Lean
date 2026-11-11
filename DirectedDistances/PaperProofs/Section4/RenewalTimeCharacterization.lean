/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Paper.Section4.RenewalTime







public section
namespace DirectedDistances.PaperProofs.Section4
open DirectedDistances.RandomWalk



theorem renewalTime_characterization (m : ℕ) (p : ℕ → ℤ × ℤ) :
    IsPositiveSuccessTime
      (fun j => (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m (Paper.Section4.renewalTime m p) ∧
      ∀ t : ℕ∞, Paper.Section4.renewalTime m p = t ↔
        IsPositiveSuccessTime
          (fun j => (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
            ∀ i, j ≤ i → (p j).1 ≤ (p i).1) m t := by
  have hs := Classical.choose_spec (Paper.Section4.existsUnique_renewalTime m p)
  refine ⟨hs.1, fun t => ⟨?_, ?_⟩⟩
  · intro h
    exact h ▸ hs.1
  · intro h
    exact (hs.2 t h).symm

end DirectedDistances.PaperProofs.Section4
