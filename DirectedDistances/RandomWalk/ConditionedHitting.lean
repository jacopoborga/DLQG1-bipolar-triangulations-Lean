/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ConditionedLazyStep
public import Mathlib.Probability.Kernel.Defs

/-! # All-start conditioned lazy kernels and barrier-event continuity

Infrastructure for Lemma 4.10 (`lem-walk-pos-prob`, original
normalized literal scalar Doob weights from `eqn-cond-walk-rn`.
The kernel is normalized before construction on its whole natural-state carrier.
The decreasing barrier-event measure limit is proved independently of any
survival formula. This module does not construct the infinite conditioned
trajectory or claim the survival formula of Lemma 4.10. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open Finset MeasurableEquiv
open scoped ENNReal

/-- The actual all-start conditioned scalar transition, as a Markov kernel. -/
@[expose] noncomputable def conditionedLazyKernel : Kernel ℕ ℕ where
  toFun x := (conditionedLazyStep x).toMeasure
  measurable' := measurable_of_countable _

instance : IsMarkovKernel conditionedLazyKernel where
  isProbabilityMeasure x := by
    change IsProbabilityMeasure (conditionedLazyStep x).toMeasure
    infer_instance

/-- The whole-carrier singleton masses of the transition are the exact PMF weights. -/
theorem conditionedLazyKernel_singleton (x y : ℕ) :
    conditionedLazyKernel x {y} = ENNReal.ofReal
      (if |(y : ℤ) - (x : ℤ)| ≤ 1 then
        ((y : ℝ) + 1) / (3 * ((x : ℝ) + 1)) else 0) := by
  change (conditionedLazyStep x).toMeasure {y} = _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y)]
  exact conditionedLazyStep_apply x y

/-- At each time the history kernel uses the actual last coordinate. -/
@[expose] noncomputable def conditionedLazyHistoryKernel (n : ℕ) :
    Kernel ((i : Finset.Iic n) → ℕ) ℕ where
  toFun p := conditionedLazyKernel (p ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
  measurable' := measurable_of_countable _

instance (n : ℕ) : IsMarkovKernel (conditionedLazyHistoryKernel n) where
  isProbabilityMeasure p := by
    change IsProbabilityMeasure
      (conditionedLazyKernel (p ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
    infer_instance

/-- The all-time barrier event is the actual decreasing-prefix limit.
This measure-continuity step is needed after the finite probabilities in
Lemma 4.10 have been evaluated; it assumes no survival formula. -/
theorem tendsto_measure_lazy_barrier_prefix (μ : Measure (ℕ → ℕ))
    [IsFiniteMeasure μ] (a : ℕ) :
    Filter.Tendsto (fun n : ℕ => μ {p | ∀ j ≤ n, a ≤ p j}) Filter.atTop
      (nhds (μ {p | ∀ j, a ≤ p j})) := by
  let E (n : ℕ) : Set (ℕ → ℕ) := {p | ∀ j ≤ n, a ≤ p j}
  have hmeas (n : ℕ) : MeasurableSet (E n) := by
    change MeasurableSet {p : ℕ → ℕ | ∀ j, ∀ _ : j ≤ n, a ≤ p j}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le measurable_const (measurable_pi_apply j)
  have hanti : Antitone E := by
    intro n m hnm p hp j hj
    exact hp j (hj.trans hnm)
  have hinter : (⋂ n, E n) = {p | ∀ j, a ≤ p j} := by
    ext p
    simp only [Set.mem_iInter, E, Set.mem_ofPred_eq]
    constructor
    · intro h j
      exact h j j le_rfl
    · intro h n j _
      exact h j
  have h := tendsto_measure_iInter_atTop (μ := μ)
    (fun n => (hmeas n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  simpa only [hinter, Function.comp_def, E] using h

end DirectedDistances.RandomWalk
