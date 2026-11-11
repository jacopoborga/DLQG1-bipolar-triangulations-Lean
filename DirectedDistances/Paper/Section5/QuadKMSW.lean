 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.QuadKMSW

/-!
# Lemma 5.13 (`lem-quad-kmsw`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/





















public section
namespace DirectedDistances.Paper.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section5



theorem quad_kmsw :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ (h : HasFlowLineHits w) (hfin_hat : hatLimitFiniteIncidence w)
        (hfin_primed : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w),
        sourceQuadrantHatWalk w h = integrateCodes (hatCodes w h) ∧
        sourceQuadrantPrimedWalk w h = integrateCodes (primedCode (primedSimInput w) h) ∧
        hatRootedMapClause w h hfin_hat ∧
        primedRootedMapClause w h hfin_primed hb :=
 
by exact DirectedDistances.PaperProofs.SourceResults.quad_kmsw_provider
 
 

end DirectedDistances.Paper.Section5
 
