/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ConeProbLowerCorrected

/-! # Provider for corrected Lemma 5.17 (`lem-cone-prob-lower`)

ONE constant `c(A) > 0`, but quantifies only over `ℓ ≤ n` with `n ≡ ℓ (mod 3)`. Outside
this domain the endpoint event is impossible, and the uncorrected printed bound is false
(`RandomWalk.coneProbLower_source_bound_false`).

validated helper chain:
- the exact closed-quadrant return count (`RandomWalk.quadrantReturnCount_closedForm`);
- its identification with the source event (`RandomWalk.iidCodeMeasure_real_coneEvent`,
  `RandomWalk.coneWordCount_eq_quadrantReturnCount`);
- the uniform analytic bound (`RandomWalk.coneClosedForm_lower`).

The source walk has iid uniform increments in `{(1,-1), (-1,0), (0,1)}`, coded by
`ω (i + 1)`; coordinate `0` of the code is fixed and unused. The start `ℓ : ℤ` is an
integer, and its nonnegativity is derived from the band, not assumed. The event keeps
the CLOSED quadrant at every time `0, …, n` and the exact endpoint `(0,0)`. -/

public section
namespace DirectedDistances.PaperProofs.Section5

/-- Corrected Lemma 5.17 (`lem-cone-prob-lower`): the original statement of
domain `ℓ ≤ n`, `n ≡ ℓ (mod 3)`. One `c(A) > 0` works for every admissible `n ≥ 1` and
every integer `ℓ` in the band `[A⁻¹ √n, A √n]`. -/
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
  fun A hA => DirectedDistances.RandomWalk.coneProbLower_corrected A hA

end DirectedDistances.PaperProofs.Section5
