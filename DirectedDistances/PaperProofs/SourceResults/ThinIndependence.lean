/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.ThinMapPosHalfSeamArg

/- # Isolated proof provider for Proposition 4.7 (`prop-thin-ind`)

forwards to proved helpers; installation, sealing and counting are separate gates. No
conclusion or source hypothesis is added.

The two random side maps are their measurable side codes `thinSideCode x renewalTime _ a`
(`a = .left/.right`, closed sides of the leftmost `x`-geodesic, the geodesic included on both
sides). The second conjunct is the code fidelity: on the coherent domain, two outcomes have equal
codes iff their whole geometric sides are isomorphic compatibly with every finite level. The last
two conjuncts show that the domain on which the code is defined by the geometry is measurable and
of full measure, so the off-domain value is confined to a null set. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk DirectedDistances.PlanarMap DirectedDistances.Paper.Section4
open DirectedDistances.PaperProofs.Section4

/-- Proposition 4.7 isolated provider (`prop-thin-ind`, -/
theorem thin_ind (x : XDP) :
    IndepFun
        (thinSideCode x renewalTime renewalTime_positiveSuccessTime .left)
        (thinSideCode x renewalTime renewalTime_positiveSuccessTime .right)
        (conditionedVectorPathLaw 0 0) ∧
      ThinSideCodeGeometricFidelity x renewalTime renewalTime_positiveSuccessTime ∧
      MeasurableSet
        (selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime) ∧
      conditionedVectorPathLaw 0 0
        (selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)ᶜ = 0 := by
  exact ⟨thin_side_codes_indep_renewal x, thinSideCodeGeometricFidelity_renewal x,
    selectedCutCoherentDomain_measurable_conull x renewalTime renewalTime_positiveSuccessTime⟩

end DirectedDistances.PaperProofs.SourceResults
