module

public import DirectedDistances.PaperProofs.Section4.PastMapAnchorProvider

/- # Isolated proof provider for Lemma 4.13 (`lem-past-map`)

and the proof forwards to the candidate provider; installation, sealing and counting are
separate gates. No conclusion or source hypothesis is added. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped ENNReal

/-- Lemma 4.13 isolated provider (`lem-past-map`); packaging only. -/
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
              PositiveSelectedCutPastMap) : SelectedCutPastMap)))) := by
  exact DirectedDistances.PaperProofs.Section4.lemma_4_13_provider

end DirectedDistances.PaperProofs.SourceResults
