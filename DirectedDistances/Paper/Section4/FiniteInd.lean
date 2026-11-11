 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.FiniteInd

/-!
# Lemma 4.14 (`lem-finite-ind`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/


















public section
namespace DirectedDistances.Paper.Section4

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4

 
theorem finite_ind (x : XDP) :
    (MeasurableSet
        (selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime) ∧
      conditionedVectorPathLaw 0 0
        (selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)ᶜ = 0) ∧
    (∀ k : ℕ, 1 ≤ k →
      CondIndepFun (sourceCutFiltration x k) (sourceCutFiltration_le_ambient x k)
        (fun p => (selectedCutPastSides x renewalTime renewalTime_positiveSuccessTime k p).1)
        (fun p => (selectedCutPastSides x renewalTime renewalTime_positiveSuccessTime k p).2)
        (conditionedVectorPathLaw 0 0)) ∧
    (∀ k : ℕ, 1 ≤ k →
      (∀ᵐ p ∂conditionedVectorPathLaw 0 0, selectedCutTime renewalTime k p = 0 →
        selectedCutPastMapFull renewalTime k p = Sum.inl zeroEdgeMarkedPast ∧
          selectedCutPastSides x renewalTime renewalTime_positiveSuccessTime k p =
            (Sum.inl zeroEdgeMarkedPast, Sum.inl zeroEdgeMarkedPast)) ∧
      (∀ᵐ p ∂conditionedVectorPathLaw 0 0, 0 < selectedCutTime renewalTime k p →
        ∃ hq : p ∈ selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime,
          SelectedCutPastClosedHalves x renewalTime renewalTime_positiveSuccessTime k
            ⟨p, hq⟩)) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.finite_ind x
 
 

end DirectedDistances.Paper.Section4
 
