module

public import DirectedDistances.PaperProofs.Section4.SelectedCutPositiveBranchLaw
public import DirectedDistances.PaperProofs.Section4.SelectedCutPastKernel
public import DirectedDistances.KMSW.StoppedMarkedBoltzmannLawFull

/-! Full-scope kernel statement toward Lemma 4.13. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Helper toward Lemma 4.13 (lem-past-map); not a paper result.
The full-scope conditional walk and map laws, their positive-endpoint kernels,
and the degenerate zero-time point case. Source: -/
@[expose] def Lemma413FullScopeStatement : Prop :=
  (∀ k : ℕ, 1 ≤ k →
    let μ := conditionedVectorPathLaw 0 0
    let Y := selectedCutFuture Paper.Section4.renewalTime k
    let W := selectedCutWalkPrefix Paper.Section4.renewalTime k
    let M := selectedCutPastMapFull Paper.Section4.renewalTime k
    condDistrib W Y μ =ᵐ[μ.map Y] selectedCutWalkKernel ∧
    condDistrib M Y μ =ᵐ[μ.map Y] selectedCutMapKernel ∧
    (∀ᵐ p ∂μ, selectedCutTime Paper.Section4.renewalTime k p = 0 →
      W p = (⟨0, fun _ => (0, 0)⟩ : SelectedCutWalkPrefix) ∧
      M p = (Sum.inl zeroEdgeMarkedPast : SelectedCutPastMap)) ∧
    (∀ y, y 0 = (0, 0) →
      selectedCutWalkKernel y = Measure.dirac
        (⟨0, fun _ => (0, 0)⟩ : SelectedCutWalkPrefix) ∧
      selectedCutMapKernel y = Measure.dirac
        (Sum.inl zeroEdgeMarkedPast : SelectedCutPastMap))) ∧
  (∀ (ell r : ℕ) (_hell : 1 ≤ ell) (hr : 1 ≤ r)
    (y : ℕ → ℤ × ℤ), y 0 = ((ell : ℤ), -(r : ℤ)) →
    selectedCutWalkKernel y = selectedCutFirstHitWalkLaw ell r ∧
    selectedCutMapKernel y =
      (firstHitPastMapKernel r hr y).map
        (selectedCutFixedLevelToCarrier r hr))

/-- Helper toward Lemma 4.13 (lem-past-map); not a paper result.
Assembles the conditional laws for the entire uncentered shifted future, the
positive first-hit and pushed-forward Boltzmann kernels, and the zero point. -/
theorem lemma413_full_scope : Lemma413FullScopeStatement := by
  unfold Lemma413FullScopeStatement
  constructor
  · intro k hk
    dsimp only
    refine ⟨selectedCutWalkPrefix_condDistrib k hk,
      selectedCutPastMapFull_condDistrib k hk, ?_, ?_⟩
    · filter_upwards [selectedCutWalkPrefix_zero_ae
          Paper.Section4.renewalTime k,
        selectedCutPastMapFull_zero_ae k] with p hW hM
      intro hzero
      exact ⟨hW hzero, hM hzero⟩
    · intro y hy
      exact ⟨selectedCutWalkKernel_zero y hy,
        selectedCutMapKernel_zero y hy⟩
  · intro ell r hell hr y hy
    refine ⟨?_, selectedCutMapKernel_positive ell r hr y hy⟩
    have hmass : 0 < conditionedVectorPathLaw 0 0
        ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
          {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 =
            (ell : ℤ)}) := by
      rw [stoppedMarked_endpoint_mass_raw r ell hr]
      exact ENNReal.mul_pos (by positivity)
        (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
    rw [selectedCutWalkKernel_positive ell r hell hr y hy]
    exact dite_eq_left hmass

end DirectedDistances.PaperProofs.Section4
