 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.KMSWBoltzmann

/-!
# Lemma 3.11 (`lem-kmsw-boltzmann`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/



































public section
namespace DirectedDistances.Paper.Section3

open DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal



theorem kmsw_boltzmann (r : ℕ) (hr : 1 ≤ r) :
    (iidCodeMeasure[|boltzmannEvent r]).map (stoppedMap r hr) =
      (rightBoltzmannLaw r
        (rightBoltzmannPartition_pos_lt_top r hr).1
        (rightBoltzmannPartition_pos_lt_top r hr).2).map some :=
 
by exact DirectedDistances.PaperProofs.SourceResults.kmsw_boltzmann r hr
 
 

end DirectedDistances.Paper.Section3
 
