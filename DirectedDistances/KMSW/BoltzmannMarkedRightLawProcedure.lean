/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.BoltzmannMarkedRightLaw
public import DirectedDistances.KMSW.BoltzmannRightLawProcedure

/-! # Procedure-reading left-boundary-vertex-marked Boltzmann law

result. The finite-expectation clause is already available as
`lem_boltzmann_finite_expectation`; this module supplies the well-definedness
of the left-vertex-marked law. -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory ProbabilityTheory

/-- The marked-map partition identity with the final-prefix premise discharged
by the procedure reading. Procedure reading of `lem-boltzmann-finite` -/
theorem rightVertexMarkedPartition_eq_markedWalkPartitionFunction_procedureReading
    (r : ℕ) (hr : 1 ≤ r) :
    rightVertexMarkedPartition r = markedWalkPartitionFunction r := by
  exact rightVertexMarkedPartition_eq_markedWalkPartitionFunction r hr
    (fun ℓ n _ => kmswPeanoPrefixExistsFinal_all ℓ r n)

/-- The marked-map partition is positive and finite after discharging the
final-prefix premise by the procedure reading. Procedure reading of
result. -/
theorem rightVertexMarkedPartition_normalizer_procedureReading (r : ℕ)
    (hr : 1 ≤ r) :
    0 < rightVertexMarkedPartition r ∧ rightVertexMarkedPartition r < ⊤ := by
  exact rightVertexMarkedPartition_normalizer r hr
    (fun ℓ n _ => kmswPeanoPrefixExistsFinal_all ℓ r n)

/-- The normalized law on maps with a marked left-boundary vertex is a
probability measure under the procedure reading. Procedure reading of
result. -/
theorem rightVertexMarkedBoltzmannLaw_isProbabilityMeasure_procedureReading
    (r : ℕ) (hr : 1 ≤ r) :
    IsProbabilityMeasure (rightVertexMarkedBoltzmannLaw r) := by
  exact rightVertexMarkedBoltzmannLaw_isProbabilityMeasure r hr
    (fun ℓ n _ => kmswPeanoPrefixExistsFinal_all ℓ r n)

end DirectedDistances.KMSW
