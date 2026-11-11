 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.PastMap

/-!
# Lemma 4.13 (`lem-past-map`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/






















public section
namespace DirectedDistances.Paper.Section4

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open scoped ENNReal



theorem past_map :
  (∀ k : ℕ, 1 ≤ k →
    let μ := conditionedVectorPathLaw 0 0
    let Y := selectedCutFuture renewalTime k
    let W := selectedCutWalkPrefix renewalTime k
    let M := selectedCutPastMapFull renewalTime k
    condDistrib W Y μ =ᵐ[μ.map Y] selectedCutWalkKernel ∧
    condDistrib M Y μ =ᵐ[μ.map Y] selectedCutMapKernel ∧
    (∀ᵐ p ∂μ, selectedCutTime renewalTime k p = 0 →
      W p = (⟨0, fun _ => (0, 0)⟩ : SelectedCutWalkPrefix) ∧
      M p = (Sum.inl zeroEdgeMarkedPast : SelectedCutPastMap)) ∧
    (∀ y : ℕ → ℤ × ℤ, y 0 = (0, 0) →
      selectedCutWalkKernel y =
        Measure.dirac (⟨0, fun _ => (0, 0)⟩ : SelectedCutWalkPrefix) ∧
      selectedCutMapKernel y =
        Measure.dirac (Sum.inl zeroEdgeMarkedPast : SelectedCutPastMap))) ∧
  (∀ (ell r : ℕ) (hell : 1 ≤ ell) (hr : 1 ≤ r)
    (y : ℕ → ℤ × ℤ),
    y 0 = ((ell : ℤ), -(r : ℤ)) →
    selectedCutWalkKernel y = selectedCutFirstHitWalkLaw ell r ∧
    selectedCutMapKernel y =
      ((boltzmannLaw ell r
          (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
          (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2).map
        (fun m : BoltzmannSpace ell r =>
          (Sum.inr
            (⟨⟨ell, hell⟩, ⟨⟨r, hr⟩, m⟩⟩ :
              PositiveSelectedCutPastMap) : SelectedCutPastMap)))) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.past_map
 
 

end DirectedDistances.Paper.Section4
 
