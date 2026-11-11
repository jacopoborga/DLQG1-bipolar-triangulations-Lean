/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.Lemma414FullLaw
public import DirectedDistances.PaperProofs.Section4.Lemma414GeodesicPrefix
import all DirectedDistances.PaperProofs.Section4.Lemma414FullSigmaAssembly

/- # Isolated proof provider for Lemma 4.14 (`lem-finite-ind`)

forwards to proved helpers; installation, sealing and counting are separate gates. No
conclusion or source hypothesis is added.

For each `x : XDP` and `k ≥ 1`, the two components of `selectedCutPastSides` (left, right) are
conditionally independent given `sourceCutFiltration x k` (`F_k` of eqn-cut-filtration) under the
full conditioned law. The remaining conjuncts identify the components with the source halves:
the coherent domain is measurable and conull; at selected time zero the past map is the one-vertex
zero-edge marked past and both sides are that point; at positive selected time the sides are the
classes of the closed left/right halves of a representative of the past map, cut along the selected
geodesic, with a directed-map isomorphism to the actual stage map carrying that geodesic onto the
prefix of the leftmost `x`-geodesic `sourceAncestorPath`. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk DirectedDistances.PlanarMap DirectedDistances.Paper.Section4
open DirectedDistances.PaperProofs.Section4

/-- Lemma 4.14 isolated provider (`lem-finite-ind`, -/
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
            ⟨p, hq⟩)) := by
  refine ⟨selectedCutCoherentDomain_measurable_conull x renewalTime
      renewalTime_positiveSuccessTime, ?_,
    fun k hk => ⟨?_, selectedCutPastClosedHalves_ae x k hk⟩⟩
  · intro k hk
    have key : lemma414_full_sigma_assembly_obligation := lemma414_full_sigma_assembly_holds
    revert key
    unfold lemma414_full_sigma_assembly_obligation
    intro key
    exact key x k hk
  filter_upwards [selectedCutPastMapFull_zero_ae k] with p hp hzero
  exact ⟨hp hzero,
    selectedCutPastSides_zero x renewalTime renewalTime_positiveSuccessTime k p hzero⟩

end DirectedDistances.PaperProofs.SourceResults
