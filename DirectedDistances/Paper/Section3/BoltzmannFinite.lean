 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoltzmannFiniteVertex

/-!
# Lemma 3.12 (`lem-boltzmann-finite`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/






















public section
namespace DirectedDistances.Paper.Section3

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section3
open scoped ENNReal


















theorem boltzmann_finite (r : ℕ) (hr : 1 ≤ r) :
    (∫⁻ ω, ENNReal.ofReal (((codeWalk ω (boltzmannTau r ω)).1 : ℝ) + 1)
        ∂(iidCodeMeasure[|boltzmannEvent r])) < ⊤ ∧
      (0 < rightVertexMarkedPartition r ∧ rightVertexMarkedPartition r < ⊤ ∧
        IsProbabilityMeasure (rightVertexMarkedBoltzmannLaw r)) :=
 
by exact DirectedDistances.PaperProofs.Section3.boltzmann_finite_vertex r hr
 
 

end DirectedDistances.Paper.Section3
 
