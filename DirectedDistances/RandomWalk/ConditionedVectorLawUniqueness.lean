/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.LazyTwoDimensionalPrefix
public import Mathlib.MeasureTheory.Constructions.Projective









public section
namespace DirectedDistances.RandomWalk
open MeasureTheory
open scoped ENNReal

/-- Agreement of all initial finite-prefix laws determines the entire finite
measure on a natural-indexed product space. No countability or discrete-space
assumption is needed for the state carrier. -/
theorem measure_eq_of_fin_prefix_map_eq {α : Type*} [MeasurableSpace α]
    (μ ν : Measure (ℕ → α)) [IsFiniteMeasure μ]
    (h : ∀ n : ℕ,
      μ.map (fun p => fun j : Fin (n + 1) => p j.val) =
        ν.map (fun p => fun j : Fin (n + 1) => p j.val)) :
    μ = ν := by
  apply IsProjectiveLimit.unique
    (P := fun J : Finset ℕ => μ.map J.restrict)
  · intro J
    rfl
  · intro J
    let n : ℕ := J.sup id
    let f : (Fin (n + 1) → α) → ((j : J) → α) :=
      fun q j => q ⟨j.val, Nat.lt_succ_of_le (Finset.le_sup (f := id) j.property)⟩
    have hf : Measurable f := .of_eval fun _ => measurable_pi_apply _
    have hp : Measurable (fun p : ℕ → α => fun j : Fin (n + 1) => p j.val) :=
      .of_eval fun _ => measurable_pi_apply _
    have he := congrArg (fun ρ : Measure (Fin (n + 1) → α) => ρ.map f) (h n)
    rw [Measure.map_map hf hp, Measure.map_map hf hp] at he
    exact he.symm

/-- The complete source RN defining data determine a unique actual
two-dimensional conditioned path law. The RN premises are precisely the
standing source formula at every horizon, with both coordinates retained. -/
theorem conditioned_vector_law_unique (x : ℕ) (y : ℤ)
    (μ ν : Measure (ℕ → ℤ × ℤ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμRN : ∀ n : ℕ,
      μ.map (fun q => fun j : Fin (n + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0))
    (hνRN : ∀ n : ℕ,
      ν.map (fun q => fun j : Fin (n + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0)) :
    μ = ν := by
  apply measure_eq_of_fin_prefix_map_eq μ ν
  intro n
  exact (hμRN n).trans (hνRN n).symm

end DirectedDistances.RandomWalk
