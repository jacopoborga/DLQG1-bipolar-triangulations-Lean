 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.ConeProbLower

/-!
# Lemma 5.17 (`lem-cone-prob-lower`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/








public section
namespace DirectedDistances.Paper.Section5

 
theorem cone_prob_lower_corrected :
    ∀ A : ℝ, 1 < A → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ l : ℤ,
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (l : ℝ) →
      (l : ℝ) ≤ A * Real.sqrt (n : ℝ) →
      l ≤ (n : ℤ) →
      (∃ q : ℤ, (n : ℤ) = l + 3 * q) →
      c * (n : ℝ) ^ (-3 : ℝ) ≤
        DirectedDistances.RandomWalk.iidCodeMeasure.real {ω : ℕ → Fin 3 |
          (∀ j ≤ n, 0 ≤ ((l, 0) + DirectedDistances.RandomWalk.codeWalk ω j).1 ∧
            0 ≤ ((l, 0) + DirectedDistances.RandomWalk.codeWalk ω j).2) ∧
          (l, 0) + DirectedDistances.RandomWalk.codeWalk ω n = (0, 0)} :=
 
by exact DirectedDistances.PaperProofs.Section5.cone_prob_lower_corrected
 
 

end DirectedDistances.Paper.Section5
 
