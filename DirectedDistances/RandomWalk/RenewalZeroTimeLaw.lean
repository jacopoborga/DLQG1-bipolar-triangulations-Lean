/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ConditionedVectorPrefixSupport

/-! # The actual source-law zero-time renewal case

Internal support for Lemma 4.9 (`lem-renewal`, unchanged
of the positive-success ranks. The RN law at horizon zero proves that the
whole zero-time history is almost surely the origin and that the shifted
whole future is the original path. No renewal time is defined here. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The source's full RN characterization produces the actual zero start;
it is a conclusion, not an added assumption about the source path. -/
theorem conditionedSource_ae_zero_start
    (ν : Measure (ℕ → ℤ × ℤ))
    (hRN : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0)) :
    ∀ᵐ p ∂ν, p 0 = (0, 0) := by
  have hs := conditionedSource_ae_prefix_mem_range 0 0 ν (fun k => by simpa only [Nat.cast_zero] using hRN k) 0
  filter_upwards [hs] with p hp
  obtain ⟨w, hw⟩ := hp
  have h := congrFun hw (0 : Fin 1)
  simpa only [lazyTwoDimensionalPrefix_zero, Fin.val_zero, Nat.cast_zero] using h.symm

/-- The zero-time history test is almost surely trivial under the actual
source law, including zero-mass tests. The whole-carrier event is used,
rather than identifying it pathwise with the future barrier at zero. -/
theorem conditionedSource_zero_time_history_restrict
    (ν : Measure (ℕ → ℤ × ℤ)) [IsProbabilityMeasure ν]
    (hRN : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0))
    (A : Set (ℕ → ℤ × ℤ))
    (hA : MeasurableSet[MeasurableSpace.comap
      (fun p : ℕ → ℤ × ℤ => fun j : Fin (0 + 1) => p j.val) inferInstance] A) :
    (ν.restrict A).map (fun p => fun k => p (0 + k) - p 0) = ν A • ν := by
  classical
  have hzero := conditionedSource_ae_zero_start ν hRN
  have hshift : (fun p : ℕ → ℤ × ℤ => fun k => p (0 + k) - p 0) =ᵐ[ν] id := by
    filter_upwards [hzero] with p hp
    funext k
    simp only [Nat.zero_add, hp, ← Prod.zero_eq_mk, sub_zero, id_eq]
  rw [Measure.map_congr (ae_restrict_of_ae hshift), Measure.map_id]
  obtain ⟨S, _, hS⟩ := MeasurableSpace.measurableSet_comap.mp hA
  have hprefix : ∀ᵐ p ∂ν, (fun j : Fin 1 => p j.val) = (fun _ => (0, 0)) := by
    filter_upwards [hzero] with p hp
    funext j
    have hj : j.val = 0 := Nat.lt_one_iff.mp j.isLt
    simpa only [hj] using hp
  by_cases hc : (fun _ : Fin 1 => ((0 : ℤ), (0 : ℤ))) ∈ S
  · have hAu : A =ᵐ[ν] Set.univ := by
      filter_upwards [hprefix] with p hp
      have hmem : p ∈ A := by
        rw [← hS]
        change (fun j : Fin 1 => p j.val) ∈ S
        rw [hp]
        exact hc
      exact propext (iff_of_true hmem (Set.mem_univ p))
    rw [Measure.restrict_congr_set hAu, measure_congr hAu,
      Measure.restrict_univ, measure_univ, one_smul]
  · have hAe : A =ᵐ[ν] ∅ := by
      filter_upwards [hprefix] with p hp
      have hmem : p ∉ A := by
        rw [← hS]
        change (fun j : Fin 1 => p j.val) ∉ S
        rw [hp]
        exact hc
      exact propext (iff_of_false hmem (Set.notMem_empty p))
    rw [Measure.restrict_congr_set hAe, measure_congr hAe,
      Measure.restrict_empty, measure_empty, zero_smul]

end DirectedDistances.RandomWalk
