 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.AppendixA.PositiveSine

/-!
# Lemma A.4 (`lem:bound-im-part`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/








public section
namespace DirectedDistances.Paper.AppendixA

open Filter
open scoped Topology ENNReal

 
theorem positive_sine :
    ∀ (f : ℕ → ℝ) (hf_nonneg : ∀ k, 0 ≤ f k) (c' ν : ℝ)
    (_hc : 0 < c') (_hν₀ : 0 < ν) (_hν₁ : ν < 1)
    (hTail : Tendsto (fun k : ℕ => (∑' j, ENNReal.ofReal (f (j + k))) /
      ENNReal.ofReal ((k : ℝ) ^ (-ν))) atTop (𝓝 (ENNReal.ofReal c'))),
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
      HasSum (fun k : ℕ => f k * Real.sin (t * (k : ℝ)))
        (∑' k, f k * Real.sin (t * (k : ℝ))) ∧
      0 < ∑' k, f k * Real.sin (t * (k : ℝ)) :=
 
by exact DirectedDistances.PaperProofs.AppendixA.positive_sine
 
 

end DirectedDistances.Paper.AppendixA
 
