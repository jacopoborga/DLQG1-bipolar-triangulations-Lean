 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.FutureMapLaw

/-!
# Proposition 5.1 (`prop-future-map-law`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/























public section
namespace DirectedDistances.Paper.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section5



theorem future_map_law :
    (∀ n : ℤ,
      (hatLawCodes ∘ futureMapShiftedCodePath n) ⟂ᵢ[wholePlaneIIDCodeMeasure]
        (hatLawPrimedCodes ∘ futureMapShiftedCodePath n)) ∧
    (∀ n : ℤ,
      wholePlaneIIDCodeMeasure.map (hatLawCodes ∘ futureMapShiftedCodePath n) =
        iidCodeMeasure.map (fun w => pitmanCode (fun i => w (i + 1)))) ∧
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ n : ℤ,
      let u := fun i => futureMapShiftedCodePath n W (i + 1)
      u = shiftedStream (fun k => W (k + n)) 0 ∧
        ∃ (h : HasFlowLineHits u) (hfin_hat : hatLimitFiniteIncidence u)
          (hfin_primed : primedLimitFiniteIncidence u) (hb : BoundaryHitWitnesses u),
          hatLawCodes (futureMapShiftedCodePath n W) = hatCodes u h ∧
          hatLawPrimedCodes (futureMapShiftedCodePath n W) =
            primedCode (primedSimInput u) h ∧
          hatRootedMapClause u h hfin_hat ∧
          primedRootedMapClause u h hfin_primed hb) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.future_map_law_provider
 
 

end DirectedDistances.Paper.Section5
 
