 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.AppendixA.Abel

/-!
# Lemma A.5 (`lem:abel`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/









public section
namespace DirectedDistances.Paper.AppendixA

open Filter
open scoped Topology Interval ENNReal

 
theorem abel :
    ∀ (f : ℕ → ℝ) (hf_nonneg : ∀ k, 0 ≤ f k) (c' ν : ℝ)
    (_hc : 0 < c') (_hν₀ : 0 < ν) (_hν₁ : ν < 1)
    (hTail : Tendsto (fun k : ℕ => (∑' j, ENNReal.ofReal (f (j + k))) /
      ENNReal.ofReal ((k : ℝ) ^ (-ν))) atTop (𝓝 (ENNReal.ofReal c')))
    (t : ℝ) (ht : 0 < t),
    HasSum (fun k : ℕ => f k * Real.sin (t * (k : ℝ)))
        (∑' k, f k * Real.sin (t * (k : ℝ))) ∧
      Tendsto
        (fun N : ℕ => ∑ k ∈ Finset.range N,
          (∑' j, ENNReal.ofReal (f (j + (k + 1)))).toReal *
            (Real.sin (((k + 1 : ℕ) : ℝ) * t) - Real.sin ((k : ℝ) * t)))
        atTop (𝓝 (∑' k, f k * Real.sin (t * (k : ℝ)))) ∧
      Tendsto
        (fun R : ℝ => ∫ u in 0..R,
          (∑' j, ENNReal.ofReal (f (j + (⌊u / t⌋₊ + 1)))).toReal * Real.cos u)
        atTop (𝓝 (∑' k, f k * Real.sin (t * (k : ℝ)))) :=
 
by exact DirectedDistances.PaperProofs.AppendixA.abel
 
 

end DirectedDistances.Paper.AppendixA
 
