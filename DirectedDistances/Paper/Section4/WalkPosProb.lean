 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.WalkPosProb

/-!
# Lemma 4.10 (`lem-walk-pos-prob`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/








public section
namespace DirectedDistances.Paper.Section4




theorem conditioned_walk_barrier_probability :
    ∀ (x : ℕ) (y : ℤ) (ν : MeasureTheory.Measure (ℕ → ℤ × ℤ))
      [MeasureTheory.IsProbabilityMeasure ν]
      (hRN : ∀ n : ℕ,
        ν.map (fun q => fun j : Fin (n + 1) => q j.val) =
          ((MeasureTheory.Measure.uniformOfFinset
            (Finset.univ : Finset (Fin n → Fin 3))).map
            (DirectedDistances.RandomWalk.lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
            (fun q => if ∀ j, 0 ≤ (q j).1 then
              ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0))
      (s : ℕ), s ≤ x →
      ν.real {p | ∀ j, (x : ℤ) - (s : ℤ) ≤ (p j).1} =
        ((s : ℝ) + 1) / ((x : ℝ) + 1) :=
 
by exact DirectedDistances.PaperProofs.Section4.conditioned_walk_barrier_probability
 
 

end DirectedDistances.Paper.Section4
 
