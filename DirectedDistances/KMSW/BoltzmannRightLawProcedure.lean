/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.BoltzmannRightLaw
public import DirectedDistances.KMSW.KMSWPeanoPrefixInvariantRotate
public import DirectedDistances.KMSW.KMSWPeanoPrefixInvariantClimb
public import DirectedDistances.KMSW.KMSWPeanoPrefixInduction

/-! # Procedure-reading Boltzmann law bridge -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PaperProofs.Section3
open DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Every map class has the final Peano prefix, by the proved rotate and climb
preservation steps. Procedure reading of `lem-kmsw-boltzmann` -/
theorem kmswPeanoPrefixExistsFinal_all (ℓ r n : ℕ) :
    KMSWPeanoPrefixExistsFinal ℓ r n := by
  exact kmswPeanoPrefixExistsFinal_of_steps
    (fun R => kmswPeanoRotatePreserves R.B (kmswRepInverseWalkClass R))
    (fun R => kmswPeanoClimbPreserves R.B (kmswRepInverseWalkClass R))

/-- The full right-boundary partition is nonzero and finite. Procedure reading
not yet the paper result. -/
theorem rightBoltzmannPartition_pos_lt_top (r : ℕ) (hr : 1 ≤ r) :
    rightBoltzmannPartition r ≠ 0 ∧ rightBoltzmannPartition r ≠ ⊤ := by
  have h := rightBoltzmannPartition_normalizer r hr
    (fun ℓ n _ => kmswPeanoPrefixExistsFinal_all ℓ r n)
  exact ⟨ne_of_gt h.1, ne_of_lt h.2⟩

/-- The stopped-map conditional law equals the full right-boundary Boltzmann
law under the procedure reading. Procedure reading of `lem-kmsw-boltzmann` -/
theorem lem_kmsw_boltzmann_procedureReading (r : ℕ) (hr : 1 ≤ r) :
    (iidCodeMeasure[|boltzmannEvent r]).map (stoppedMap r hr) =
      (rightBoltzmannLaw r
        (rightBoltzmannPartition_pos_lt_top r hr).1
        (rightBoltzmannPartition_pos_lt_top r hr).2).map some := by
  exact iidCodeMeasure_cond_map_eq_rightBoltzmannLaw_map_some r hr
    (fun ℓ n _ => kmswPeanoPrefixExistsFinal_all ℓ r n)
    (rightBoltzmannPartition_pos_lt_top r hr).1
    (rightBoltzmannPartition_pos_lt_top r hr).2

/-- The stopped-walk map has exactly the positive-total-edge part of the
right-boundary carrier as its range. Procedure reading of
not yet the paper result. -/
theorem stoppedWalkMap_range_eq_positive_procedureReading (r : ℕ) :
    Set.range (@stoppedWalkMap r) = {q | 1 ≤ q.2.1} := by
  exact stoppedWalkMap_range_eq_positive r
    (fun ℓ n _ => kmswPeanoPrefixExistsFinal_all ℓ r n)

/-- The full right-boundary partition equals the probability of the stopping
event. Procedure reading of `lem-kmsw-boltzmann` -/
theorem rightBoltzmannPartition_eq_eventProbability_procedureReading
    (r : ℕ) (hr : 1 ≤ r) :
    rightBoltzmannPartition r = iidCodeMeasure (boltzmannEvent r) := by
  exact rightBoltzmannPartition_eq_eventProbability r hr
    (fun ℓ n _ => kmswPeanoPrefixExistsFinal_all ℓ r n)

/-- The normalized full right-boundary Boltzmann measure is a probability
measure. Procedure reading of `lem-kmsw-boltzmann` -/
theorem rightBoltzmannLaw_isProbabilityMeasure_procedureReading
    (r : ℕ) (hr : 1 ≤ r) :
    IsProbabilityMeasure
      (rightBoltzmannLaw r
        (rightBoltzmannPartition_pos_lt_top r hr).1
        (rightBoltzmannPartition_pos_lt_top r hr).2) := by
  exact rightBoltzmannLaw_isProbabilityMeasure r
    (rightBoltzmannPartition_pos_lt_top r hr).1
    (rightBoltzmannPartition_pos_lt_top r hr).2

end DirectedDistances.KMSW
