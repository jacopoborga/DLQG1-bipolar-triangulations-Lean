 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.ThinIndependence

/-!
# Proposition 4.7 (`prop-thin-ind`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/
















public section
namespace DirectedDistances.Paper.Section4

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4

 
theorem thin_ind (x : XDP) :
    IndepFun
        (thinSideCode x renewalTime renewalTime_positiveSuccessTime .left)
        (thinSideCode x renewalTime renewalTime_positiveSuccessTime .right)
        (conditionedVectorPathLaw 0 0) ∧
      ThinSideCodeGeometricFidelity x renewalTime renewalTime_positiveSuccessTime ∧
      MeasurableSet
        (selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime) ∧
      conditionedVectorPathLaw 0 0
        (selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)ᶜ = 0 :=
 
by exact DirectedDistances.PaperProofs.SourceResults.thin_ind x
 
 

end DirectedDistances.Paper.Section4
 
