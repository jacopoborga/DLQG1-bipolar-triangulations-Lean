/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoltzmannMarks
public import DirectedDistances.KMSW.BoltzmannMarkedRightLawProcedure

/-! Supporting lemmas for paper labels `lem-boltzmann-finite` (see CORRESPONDENCE.md). -/

















public section
namespace DirectedDistances.PaperProofs.Section3

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk
open scoped ENNReal

 
theorem boltzmann_finite_vertex (r : ℕ) (hr : 1 ≤ r) :
    (∫⁻ ω, ENNReal.ofReal (((codeWalk ω (boltzmannTau r ω)).1 : ℝ) + 1)
        ∂(iidCodeMeasure[|boltzmannEvent r])) < ⊤ ∧
      (0 < rightVertexMarkedPartition r ∧ rightVertexMarkedPartition r < ⊤ ∧
        IsProbabilityMeasure (rightVertexMarkedBoltzmannLaw r)) :=
  ⟨boltzmann_conditional_measure_lintegral_lt_top r hr,
    ⟨(rightVertexMarkedPartition_normalizer_procedureReading r hr).1,
      (rightVertexMarkedPartition_normalizer_procedureReading r hr).2,
      rightVertexMarkedBoltzmannLaw_isProbabilityMeasure_procedureReading r hr⟩⟩

end DirectedDistances.PaperProofs.Section3
