/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.BoltzmannMarkedRightLawProcedure
public import DirectedDistances.KMSW.BoltzmannEndpointFiberLaw

/-! Supporting lemmas for paper labels `def-boltzmann-lr`, `def-boltzmann-right` (see CORRESPONDENCE.md). -/













public section
namespace DirectedDistances.PaperProofs.Section1

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open MeasureTheory
open scoped ENNReal BigOperators ProbabilityTheory

/-- The marked atom formula in Definition 1.10 (`def-boltzmann-right`, -/
theorem rightVertexMarkedBoltzmannLaw_singleton (r : ℕ)
    (p : RightVertexMarkedBoltzmannSpace r) :
    rightVertexMarkedBoltzmannLaw r {p} =
      (1 / 3 : ℝ≥0∞) ^ p.1.2.1 / rightVertexMarkedPartition r := by
  classical
  rw [rightVertexMarkedBoltzmannLaw, Measure.smul_apply, smul_eq_mul,
    Measure.sum_smul_dirac_singleton]
  change (rightVertexMarkedPartition r)⁻¹ * (1 / 3 : ℝ≥0∞) ^ p.1.2.1 = _
  exact ENNReal.div_eq_inv_mul.symm

/-- Forgetting the left-boundary vertex weights each map by its left length -/
theorem rightVertexMarkedBoltzmannLaw_map_fst_singleton (r : ℕ)
    (q : AllBoltzmannSpace r) :
    (rightVertexMarkedBoltzmannLaw r).map
        (fun p : RightVertexMarkedBoltzmannSpace r => p.1) {q} =
      ((q.1 + 1 : ℕ) : ℝ≥0∞) * (1 / 3 : ℝ≥0∞) ^ q.2.1 /
        rightVertexMarkedPartition r := by
  classical
  rw [Measure.map_apply (measurable_of_countable _)
      (measurableSet_singleton q),
    rightVertexMarkedBoltzmannLaw, Measure.smul_apply, smul_eq_mul,
    Measure.sum_apply _ (by trivial)]
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (show MeasurableSet
      ((fun p : RightVertexMarkedBoltzmannSpace r => p.1) ⁻¹' {q}) from trivial),
    Set.mem_preimage, Set.mem_singleton_iff, Set.indicator_apply,
    Pi.one_apply]
  change (rightVertexMarkedPartition r)⁻¹ *
      (∑' p : (Σ q' : AllBoltzmannSpace r, Fin (q'.1 + 1)),
        allBoltzmannWeight p.1 * if p.1 = q then 1 else 0) = _
  rw [tsum_sigma']
  have hsum : (∑' q' : AllBoltzmannSpace r,
      ∑' _j : Fin (q'.1 + 1),
        allBoltzmannWeight q' * if q' = q then 1 else 0) =
      ((q.1 + 1 : ℕ) : ℝ≥0∞) * (1 / 3 : ℝ≥0∞) ^ q.2.1 := by
    rw [tsum_eq_single q]
    · rw [tsum_fintype]
      simp [allBoltzmannWeight, boltzmannWeight, Finset.sum_const, nsmul_eq_mul]
    · intro q' hq'
      simp [hq']
  rw [hsum]
  exact ENNReal.div_eq_inv_mul.symm

/-- Full characterization of Definition 1.10 (`def-boltzmann-right`,
second is `C̃_r`. Both are positive finite normalizers, each marked atom has
the underlying map's weight, and forgetting the mark gives the `ℓ + 1`
weighting. The final two clauses give uniqueness of the respective laws. -/
theorem def_1_10_boltzmann_right_provider (r : ℕ) (hr : 1 ≤ r) :
    (rightBoltzmannPartition r =
      ∑' q : AllBoltzmannSpace r, (1 / 3 : ℝ≥0∞) ^ q.2.1) ∧
    (rightVertexMarkedPartition r =
      ∑' q : AllBoltzmannSpace r,
        ((q.1 + 1 : ℕ) : ℝ≥0∞) * (1 / 3 : ℝ≥0∞) ^ q.2.1) ∧
    (0 < rightBoltzmannPartition r ∧ rightBoltzmannPartition r < ⊤) ∧
    (0 < rightVertexMarkedPartition r ∧ rightVertexMarkedPartition r < ⊤) ∧
    IsProbabilityMeasure (rightBoltzmannLaw r
      (rightBoltzmannPartition_pos_lt_top r hr).1
      (rightBoltzmannPartition_pos_lt_top r hr).2) ∧
    IsProbabilityMeasure (rightVertexMarkedBoltzmannLaw r) ∧
    (∀ q : AllBoltzmannSpace r,
      rightBoltzmannLaw r
        (rightBoltzmannPartition_pos_lt_top r hr).1
        (rightBoltzmannPartition_pos_lt_top r hr).2 {q} =
        (1 / 3 : ℝ≥0∞) ^ q.2.1 / rightBoltzmannPartition r) ∧
    (∀ p : RightVertexMarkedBoltzmannSpace r,
      rightVertexMarkedBoltzmannLaw r {p} =
        (1 / 3 : ℝ≥0∞) ^ p.1.2.1 / rightVertexMarkedPartition r) ∧
    (∀ q : AllBoltzmannSpace r,
      (rightVertexMarkedBoltzmannLaw r).map
          (fun p : RightVertexMarkedBoltzmannSpace r => p.1) {q} =
        ((q.1 + 1 : ℕ) : ℝ≥0∞) * (1 / 3 : ℝ≥0∞) ^ q.2.1 /
          rightVertexMarkedPartition r) ∧
    (∀ μ : Measure (AllBoltzmannSpace r),
      (∀ q, μ {q} = (1 / 3 : ℝ≥0∞) ^ q.2.1 / rightBoltzmannPartition r) →
      μ = rightBoltzmannLaw r
        (rightBoltzmannPartition_pos_lt_top r hr).1
        (rightBoltzmannPartition_pos_lt_top r hr).2) ∧
    (∀ μ : Measure (RightVertexMarkedBoltzmannSpace r),
      (∀ p, μ {p} = (1 / 3 : ℝ≥0∞) ^ p.1.2.1 / rightVertexMarkedPartition r) →
      μ = rightVertexMarkedBoltzmannLaw r) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact rightVertexMarkedPartition_eq_tsum r
  · exact ⟨pos_iff_ne_zero.mpr (rightBoltzmannPartition_pos_lt_top r hr).1,
      lt_top_iff_ne_top.mpr (rightBoltzmannPartition_pos_lt_top r hr).2⟩
  · exact rightVertexMarkedPartition_normalizer_procedureReading r hr
  · exact rightBoltzmannLaw_isProbabilityMeasure_procedureReading r hr
  · exact rightVertexMarkedBoltzmannLaw_isProbabilityMeasure_procedureReading r hr
  · intro q
    exact rightBoltzmannLaw_singleton r _ _ q
  · exact rightVertexMarkedBoltzmannLaw_singleton r
  · exact rightVertexMarkedBoltzmannLaw_map_fst_singleton r
  · intro μ hμ
    apply Measure.ext_of_singleton
    intro q
    exact (hμ q).trans (rightBoltzmannLaw_singleton r _ _ q).symm
  · intro μ hμ
    apply Measure.ext_of_singleton
    intro p
    exact (hμ p).trans (rightVertexMarkedBoltzmannLaw_singleton r p).symm

/-- Full characterization of Definition 3.14 (`def-boltzmann-lr`,
weights, a positive finite partition, and is the right-boundary law
conditioned on its left boundary length. The atom formula uniquely determines
this law. -/
theorem def_3_14_boltzmann_lr_provider (ell r : ℕ)
    (hell : 1 ≤ ell) (hr : 1 ≤ r) :
    (boltzmannPartition ell r =
      ∑' m : BoltzmannSpace ell r, (1 / 3 : ℝ≥0∞) ^ m.1) ∧
    (0 < boltzmannPartition ell r ∧ boltzmannPartition ell r < ⊤) ∧
    IsProbabilityMeasure (boltzmannLaw ell r
      (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
      (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2) ∧
    (∀ m : BoltzmannSpace ell r,
      boltzmannLaw ell r
        (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
        (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2 {m} =
        (1 / 3 : ℝ≥0∞) ^ m.1 / boltzmannPartition ell r) ∧
    (rightBoltzmannLaw r
      (rightBoltzmannPartition_pos_lt_top r hr).1
      (rightBoltzmannPartition_pos_lt_top r hr).2)[|
        {q : AllBoltzmannSpace r | q.1 = ell}] =
      (boltzmannLaw ell r
        (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
        (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2).map
        (β := AllBoltzmannSpace r)
        (fun m => (⟨ell, m⟩ : AllBoltzmannSpace r)) ∧
    (∀ μ : Measure (BoltzmannSpace ell r),
      (∀ m, μ {m} = (1 / 3 : ℝ≥0∞) ^ m.1 / boltzmannPartition ell r) →
      μ = boltzmannLaw ell r
        (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
        (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2) := by
  refine ⟨rfl, ?_, inferInstance, ?_, ?_, ?_⟩
  · exact ⟨pos_iff_ne_zero.mpr
      (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1,
      lt_top_iff_ne_top.mpr
        (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2⟩
  · intro m
    exact boltzmannLaw_singleton ell r _ _ m
  · exact rightBoltzmannLaw_cond_leftLength_of_pos r ell hell hr
  · intro μ hμ
    apply Measure.ext_of_singleton
    intro m
    exact (hμ m).trans (boltzmannLaw_singleton ell r _ _ m).symm

end DirectedDistances.PaperProofs.Section1
