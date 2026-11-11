/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ConditionedVectorTail
public import DirectedDistances.RandomWalk.ConditionedSourceBarrier
import Mathlib.Tactic.FieldSimp

/-! Supporting lemmas for paper labels `lem-renewal` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A genuine surviving source-word prefix factors from its actual all-time
future lower barrier with the source's endpoint-dependent probability. -/
theorem conditionedSource_prefix_inter_future_barrier
    (x : ℕ) (y : ℤ) (ν : Measure (ℕ → ℤ × ℤ)) [IsProbabilityMeasure ν]
    (hRN : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0))
    (n X a : ℕ) (w : Fin n → Fin 3)
    (hw : ∀ j, 0 ≤ (lazyTwoDimensionalPrefix (x : ℤ) y w j).1)
    (haX : a ≤ X)
    (hX : (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1 = (X : ℤ)) :
    let C : Set (ℕ → ℤ × ℤ) :=
      {p | (fun j : Fin (n + 1) => p j.val) = lazyTwoDimensionalPrefix (x : ℤ) y w}
    ν.real (C ∩ {p | ∀ j, (a : ℤ) ≤ (p (n + j)).1}) =
      ν.real C * (((X - a : ℕ) : ℝ) + 1) / ((X : ℝ) + 1) := by
  let C : Set (ℕ → ℤ × ℤ) :=
    {p | (fun j : Fin (n + 1) => p j.val) = lazyTwoDimensionalPrefix (x : ℤ) y w}
  let T : (ℕ → ℤ × ℤ) → (ℕ → ℤ × ℤ) := fun p k => p (n + k)
  let E : Set (ℕ → ℤ × ℤ) := {p | ∀ j, (a : ℤ) ≤ (p j).1}
  have hpos : 0 < ν C :=
    (conditionedSource_prefix_atom_pos_iff x y ν hRN n w).mpr hw
  have hne : ν C ≠ 0 := ne_of_gt hpos
  have hT : Measurable T := by fun_prop
  have hE : MeasurableSet E := by
    change MeasurableSet {p : ℕ → ℤ × ℤ | ∀ j, (a : ℤ) ≤ (p j).1}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j =>
      measurableSet_le measurable_const (measurable_pi_apply j).fst
  let : IsProbabilityMeasure (ProbabilityTheory.cond ν C) := cond_isProbabilityMeasure hne
  let η : Measure (ℕ → ℤ × ℤ) := (ProbabilityTheory.cond ν C).map T
  have hηprob : IsProbabilityMeasure η := by dsimp only [η]; infer_instance
  let := hηprob
  have hηeq : η = (ν C)⁻¹ • (ν.restrict C).map T := by
    dsimp only [η, ProbabilityTheory.cond]
    exact Measure.map_smul _ hT.aemeasurable
  have hηRN : ∀ k : ℕ,
      η.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix (X : ℤ)
            (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).2)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((X : ℝ) + 1)) else 0) := by
    intro k
    rw [hηeq]
    exact conditionedSource_normalized_tail_RN x y ν hRN n X w hw hX k
  have hb := conditionedSource_barrier_probability X
    (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).2 η hηRN
    (X - a) (Nat.sub_le X a)
  have hlevel : (X : ℤ) - ((X - a : ℕ) : ℤ) = (a : ℤ) := by
    rw [Nat.cast_sub haX]
    omega
  change η.real {p | ∀ j, (X : ℤ) - ((X - a : ℕ) : ℤ) ≤ (p j).1} = _ at hb
  rw [hlevel] at hb
  have hmass : η.real E = (ν C).toReal⁻¹ * ν.real (C ∩ T ⁻¹' E) := by
    dsimp only [η]
    rw [Measure.real, Measure.map_apply hT hE]
    dsimp only [ProbabilityTheory.cond]
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (hE.preimage hT),
      Set.inter_comm, ENNReal.toReal_mul, ENNReal.toReal_inv]
    rfl
  have hrealne : (ν C).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos hne (measure_ne_top _ _))
  change ν.real (C ∩ T ⁻¹' E) = _
  change η.real E = _ at hb
  have hrecover : ν.real (C ∩ T ⁻¹' E) = ν.real C * η.real E := by
    rw [hmass]
    simp only [Measure.real]
    field_simp [hrealne]
  rw [hrecover, hb, mul_div_assoc]

/-- If the prescribed past also stays above the same threshold, its joint
probability with the global all-time barrier has the identical source factor. -/
theorem conditionedSource_prefix_inter_barrier
    (x : ℕ) (y : ℤ) (ν : Measure (ℕ → ℤ × ℤ)) [IsProbabilityMeasure ν]
    (hRN : ∀ k : ℕ,
      ν.map (fun q => fun j : Fin (k + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin k → Fin 3))).map
          (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last k)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0))
    (n X a : ℕ) (w : Fin n → Fin 3)
    (ha : ∀ j, (a : ℤ) ≤ (lazyTwoDimensionalPrefix (x : ℤ) y w j).1)
    (hX : (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1 = (X : ℤ)) :
    let C : Set (ℕ → ℤ × ℤ) :=
      {p | (fun j : Fin (n + 1) => p j.val) = lazyTwoDimensionalPrefix (x : ℤ) y w}
    ν.real (C ∩ {p | ∀ j, (a : ℤ) ≤ (p j).1}) =
      ν.real C * (((X - a : ℕ) : ℝ) + 1) / ((X : ℝ) + 1) := by
  let C : Set (ℕ → ℤ × ℤ) :=
    {p | (fun j : Fin (n + 1) => p j.val) = lazyTwoDimensionalPrefix (x : ℤ) y w}
  have hw : ∀ j, 0 ≤ (lazyTwoDimensionalPrefix (x : ℤ) y w j).1 :=
    fun j => le_trans (by positivity) (ha j)
  have haX : a ≤ X := by
    have h := ha (Fin.last n)
    rw [hX] at h
    exact_mod_cast h
  have h := conditionedSource_prefix_inter_future_barrier x y ν hRN n X a w hw haX hX
  change ν.real (C ∩ {p | ∀ j, (a : ℤ) ≤ (p (n + j)).1}) = _ at h
  have he : C ∩ {p | ∀ j, (a : ℤ) ≤ (p (n + j)).1} =
      C ∩ {p | ∀ j, (a : ℤ) ≤ (p j).1} := by
    ext p
    constructor
    · rintro ⟨hp, ht⟩
      refine ⟨hp, ?_⟩
      intro j
      by_cases hj : j ≤ n
      · have hjp := congrFun hp (⟨j, by omega⟩ : Fin (n + 1))
        exact hjp ▸ ha ⟨j, by omega⟩
      · have hi : n + (j - n) = j := by omega
        simpa only [hi] using ht (j - n)
    · rintro ⟨hp, he⟩
      exact ⟨hp, fun j => he (n + j)⟩
  rw [he] at h
  exact h

end DirectedDistances.RandomWalk
