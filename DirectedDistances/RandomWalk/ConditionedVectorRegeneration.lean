/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ConditionedVectorReconditioning
public import DirectedDistances.RandomWalk.ConditionedVectorLawUniqueness
public import DirectedDistances.Probability.ConditionalMap

/-! # Actual deterministic-cylinder regeneration of the source vector law

Internal producer for Lemma 4.9 (`lem-renewal`,
actual endpoint and both endpoint coordinates are subtracted. The result is
an equality of whole path measures. No random-time statement is claimed. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- On a genuine nonnegative source-word cylinder, additionally conditioning
the future above its actual endpoint regenerates the entire zero-start path
law after subtracting that endpoint. The joint conditioning event is proved
positive inside the proof, not assumed as a Markov or regeneration premise. -/
theorem conditionedSource_cylinder_regeneration
    (ν : Measure (ℕ → ℤ × ℤ)) [IsProbabilityMeasure ν]
    (hRN : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0))
    (n X : ℕ) (w : Fin n → Fin 3)
    (hw : ∀ j, 0 ≤ (lazyTwoDimensionalPrefix 0 0 w j).1)
    (hX : (lazyTwoDimensionalPrefix 0 0 w (Fin.last n)).1 = (X : ℤ)) :
    let Y : ℤ := (lazyTwoDimensionalPrefix 0 0 w (Fin.last n)).2
    let C : Set (ℕ → ℤ × ℤ) :=
      {p | (fun j : Fin (n + 1) => p j.val) = lazyTwoDimensionalPrefix 0 0 w}
    let F : Set (ℕ → ℤ × ℤ) := {p | ∀ k, (X : ℤ) ≤ (p (n + k)).1}
    (ProbabilityTheory.cond ν (C ∩ F)).map
      (fun p => fun k => p (n + k) - ((X : ℤ), Y)) = ν := by
  let Y : ℤ := (lazyTwoDimensionalPrefix 0 0 w (Fin.last n)).2
  let C : Set (ℕ → ℤ × ℤ) :=
    {p | (fun j : Fin (n + 1) => p j.val) = lazyTwoDimensionalPrefix 0 0 w}
  let T : (ℕ → ℤ × ℤ) → (ℕ → ℤ × ℤ) := fun p k => p (n + k)
  let B : Set (ℕ → ℤ × ℤ) := {p | ∀ k, (X : ℤ) ≤ (p k).1}
  let g : (ℕ → ℤ × ℤ) → (ℕ → ℤ × ℤ) := fun p k => p k - ((X : ℤ), Y)
  have hC : MeasurableSet C := (measurableSet_singleton _).preimage (by fun_prop)
  have hT : Measurable T := by fun_prop
  have hB : MeasurableSet B := by
    change MeasurableSet {p : ℕ → ℤ × ℤ | ∀ k, (X : ℤ) ≤ (p k).1}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun k =>
      measurableSet_le measurable_const (measurable_pi_apply k).fst
  have hg : Measurable g := by fun_prop
  have hRN0 : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix ((0 : ℕ) : ℤ) 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) /
              (((0 : ℕ) : ℝ) + 1)) else 0) := by
    simpa only [Nat.cast_zero] using hRN
  have hCpos : 0 < ν C :=
    (conditionedSource_prefix_atom_pos_iff 0 0 ν hRN0 n w).mpr hw
  have hCne : ν C ≠ 0 := ne_of_gt hCpos
  have hJpos : 0 < ν.real (C ∩ T ⁻¹' B) := by
    have hj := conditionedSource_prefix_inter_future_barrier 0 0 ν hRN0 n X X w hw le_rfl hX
    change ν.real (C ∩ T ⁻¹' B) = _ at hj
    rw [hj]
    simp only [Nat.sub_self, Nat.cast_zero, zero_add, mul_one]
    exact div_pos (ENNReal.toReal_pos hCne (measure_ne_top _ _)) (by positivity)
  have hJne : ν (C ∩ T ⁻¹' B) ≠ 0 := by
    intro hz
    rw [Measure.real, hz, ENNReal.toReal_zero] at hJpos
    exact (lt_irrefl 0) hJpos
  let : IsProbabilityMeasure (ProbabilityTheory.cond ν C) := cond_isProbabilityMeasure hCne
  let η : Measure (ℕ → ℤ × ℤ) := (ProbabilityTheory.cond ν C).map T
  have hηprob : IsProbabilityMeasure η := by dsimp only [η]; infer_instance
  let := hηprob
  have hηeq : η = (ν C)⁻¹ • (ν.restrict C).map T := by
    dsimp only [η, ProbabilityTheory.cond]
    exact Measure.map_smul _ hT.aemeasurable
  have hηRN : ∀ k : ℕ,
      η.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix (X : ℤ) Y)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((X : ℝ) + 1)) else 0) := by
    intro k
    rw [hηeq]
    exact conditionedSource_normalized_tail_RN 0 0 ν hRN0 n X w hw hX k
  let ρ : Measure (ℕ → ℤ × ℤ) := (ProbabilityTheory.cond η B).map g
  have hρeq : ρ = (ProbabilityTheory.cond ν (C ∩ T ⁻¹' B)).map (g ∘ T) :=
    DirectedDistances.Probability.cond_map_cond_eq_map_cond_inter ν C hC T hT B hB g hg
  let : IsProbabilityMeasure (ProbabilityTheory.cond ν (C ∩ T ⁻¹' B)) :=
    cond_isProbabilityMeasure hJne
  have hρprob : IsProbabilityMeasure ρ := by rw [hρeq]; infer_instance
  let := hρprob
  have hρν : ρ = ν := by
    apply measure_eq_of_fin_prefix_map_eq ρ ν
    intro k
    have hh := conditionedSource_above_start_shift_RN X Y η hηRN k
    change ρ.map (fun p => fun j : Fin (k + 1) => p j.val) = _ at hh
    exact hh.trans (hRN k).symm
  change (ProbabilityTheory.cond ν (C ∩ T ⁻¹' B)).map (g ∘ T) = ν
  exact hρeq.symm.trans hρν

end DirectedDistances.RandomWalk
