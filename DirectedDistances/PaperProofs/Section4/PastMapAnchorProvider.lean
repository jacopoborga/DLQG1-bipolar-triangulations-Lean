module

public import DirectedDistances.PaperProofs.Section4.Lemma413FullScope

/-! Candidate provider for Lemma 4.13 (`lem-past-map`), -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.Paper.Section4
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- not yet a counted paper result. -/
theorem lemma_4_13_provider :
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
  classical
  have hfull := lemma413_full_scope
  refine ⟨hfull.1, ?_⟩
  intro ell r hell hr y hy
  obtain ⟨hwalk, hmap⟩ := hfull.2 ell r hell hr y hy
  refine ⟨hwalk, hmap.trans ?_⟩
  have hleft : (1 : ℤ) ≤ (ell : ℤ) := by omega
  have hkernel : firstHitPastMapKernel r hr y =
      firstHitBoltzmannMapLaw r ell hr hell := by
    simp only [firstHitPastMapKernel, Kernel.coe_mk, hy, hleft,
      dite_true, Int.toNat_natCast]
  rw [hkernel, firstHitBoltzmannMapLaw]
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rw [Measure.map_map
    (f := fun m : BoltzmannSpace ell r => (⟨ell, m⟩ : AllBoltzmannSpace r))
    (g := selectedCutFixedLevelToCarrier r hr ∘ some)
    (measurable_of_countable _) (measurable_of_countable _)]
  congr 1
  funext m
  change (if h : 1 ≤ ell then
    (Sum.inr (⟨⟨ell, h⟩, ⟨⟨r, hr⟩, m⟩⟩ : PositiveSelectedCutPastMap) :
      SelectedCutPastMap)
    else Sum.inl zeroEdgeMarkedPast) = _
  rw [dite_eq_left hell]

end DirectedDistances.PaperProofs.Section4
