/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.RenewalCylinderMass
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-! Supporting lemmas for paper labels `lem-walk-bdy-sum` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The future barrier above the actual endpoint cancels the source RN
weight on the entire finite-prefix measure. The right side retains exactly
all surviving unconditioned words; neither side is normalized. -/
theorem conditionedSource_restrict_endpoint_barrier_map_prefix
    (ν : Measure (ℕ → ℤ × ℤ)) [IsProbabilityMeasure ν]
    (hRN : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0))
    (n : ℕ) :
    (ν.restrict {p | ∀ k, (p n).1 ≤ (p (n + k)).1}).map
        (fun p => fun j : Fin (n + 1) => p j.val) =
      (((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
        (lazyTwoDimensionalPrefix 0 0)).restrict {q | ∀ j, 0 ≤ (q j).1}) := by
  classical
  let B : Set (ℕ → ℤ × ℤ) := {p | ∀ k, (p n).1 ≤ (p (n + k)).1}
  let π : (ℕ → ℤ × ℤ) → (Fin (n + 1) → ℤ × ℤ) := fun p j => p j.val
  let S : Set (Fin (n + 1) → ℤ × ℤ) := {q | ∀ j, 0 ≤ (q j).1}
  let μ : Measure (Fin (n + 1) → ℤ × ℤ) :=
    (Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
      (lazyTwoDimensionalPrefix 0 0)
  have hπ : Measurable π := by fun_prop
  have : IsProbabilityMeasure
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))) := by
    refine ⟨?_⟩
    rw [Measure.uniformOfFinset_apply]
    simp only [Set.mem_univ, Finset.filter_true, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    exact ENNReal.div_self (by positivity) (by norm_num)
  have : IsFiniteMeasure μ := Measure.isFiniteMeasure_map _ _
  change (ν.restrict B).map π = μ.restrict S
  apply Measure.ext_of_measureReal_singleton
  intro q
  rw [Measure.real, Measure.map_apply hπ (measurableSet_singleton q),
    Measure.restrict_apply ((measurableSet_singleton q).preimage hπ)]
  rw [Measure.real, Measure.restrict_apply (measurableSet_singleton q)]
  by_cases hq : q ∈ Set.range (@lazyTwoDimensionalPrefix n 0 0)
  · obtain ⟨w, rfl⟩ := hq
    have hjoint := conditionedSource_prefix_inter_endpoint_barrier_mass ν hRN n w
    change (ν ({p | π p = lazyTwoDimensionalPrefix 0 0 w} ∩ B)).toReal = _ at hjoint
    change (ν ({p | π p = lazyTwoDimensionalPrefix 0 0 w} ∩ B)).toReal = _
    rw [hjoint]
    by_cases hw : ∀ j, 0 ≤ (lazyTwoDimensionalPrefix 0 0 w j).1
    · rw [ite_eq_left hw]
      have he : {lazyTwoDimensionalPrefix 0 0 w} ∩ S =
          {lazyTwoDimensionalPrefix 0 0 w} := by
        exact Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hw)
      rw [he]
      change _ = (μ {lazyTwoDimensionalPrefix 0 0 w}).toReal
      rw [show μ {lazyTwoDimensionalPrefix 0 0 w} = ((3 : ℝ≥0∞)^n)⁻¹ from
        lazyTwoDimensionalPrefix_atom 0 0 w]
      simp only [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    · rw [ite_eq_right hw]
      have he : {lazyTwoDimensionalPrefix 0 0 w} ∩ S = ∅ := by
        exact Set.disjoint_iff_inter_eq_empty.mp (Set.disjoint_singleton_left.mpr hw)
      rw [he, measure_empty, ENNReal.toReal_zero]
  · have hRN0 : ∀ k : ℕ,
        ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
          ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
            (lazyTwoDimensionalPrefix ((0 : ℕ) : ℤ) 0)).withDensity
            (fun q => if ∀ j, 0 ≤ (q j).1 then
              ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) /
                (((0 : ℕ) : ℝ) + 1)) else 0) := by
      simpa only [Nat.cast_zero] using hRN
    have hzero : ν (π ⁻¹' {q} ∩ B) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [conditionedSource_ae_prefix_mem_range 0 0 ν hRN0 n] with p hp
      rintro ⟨he, _⟩
      apply hq
      exact (Set.mem_singleton_iff.mp he) ▸ hp
    have hbasezero : μ {q} = 0 := by
      dsimp only [μ]
      rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
      have he : lazyTwoDimensionalPrefix 0 0 ⁻¹' {q} = ∅ := by
        ext w
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false]
        intro hw
        exact hq ⟨w, hw⟩
      rw [he, measure_empty]
    rw [hzero, measure_mono_null Set.inter_subset_left hbasezero]

end DirectedDistances.RandomWalk
