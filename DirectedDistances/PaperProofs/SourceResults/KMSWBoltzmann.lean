/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.BoltzmannRightLawProcedure

/-! Supporting lemmas for paper labels `lem-kmsw-boltzmann` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.PaperProofs.SourceResults

open DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Isolated source-domain proof provider for Lemma 3.11 (lem-kmsw-boltzmann). -/
theorem kmsw_boltzmann (r : ℕ) (hr : 1 ≤ r) :
    (iidCodeMeasure[|boltzmannEvent r]).map (stoppedMap r hr) =
      (rightBoltzmannLaw r
        (rightBoltzmannPartition_pos_lt_top r hr).1
        (rightBoltzmannPartition_pos_lt_top r hr).2).map some :=
by exact DirectedDistances.KMSW.lem_kmsw_boltzmann_procedureReading r hr

end DirectedDistances.PaperProofs.SourceResults
