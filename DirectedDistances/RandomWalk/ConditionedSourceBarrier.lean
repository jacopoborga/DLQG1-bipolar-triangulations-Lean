/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.LazyTwoDimensionalPrefix
public import DirectedDistances.RandomWalk.LazyScalarPrefixBarrier

/-! Supporting lemmas for paper labels `lem-walk-pos-prob` (see CORRESPONDENCE.md). -/









public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

private theorem tendsto_measureReal_firstCoordinate_barrier
    (ν : Measure (ℕ → ℤ × ℤ)) [IsFiniteMeasure ν] (a : ℤ) :
    Tendsto (fun n : ℕ => ν.real {p | ∀ j ≤ n, a ≤ (p j).1}) atTop
      (𝓝 (ν.real {p | ∀ j, a ≤ (p j).1})) := by
  let E (n : ℕ) : Set (ℕ → ℤ × ℤ) := {p | ∀ j ≤ n, a ≤ (p j).1}
  have hmeas (n : ℕ) : MeasurableSet (E n) := by
    change MeasurableSet {p : ℕ → ℤ × ℤ | ∀ j, ∀ _ : j ≤ n, a ≤ (p j).1}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le measurable_const (measurable_pi_apply j).fst
  have hanti : Antitone E := by
    intro n m hnm p hp j hj
    exact hp j (hj.trans hnm)
  have hinter : (⋂ n, E n) = {p | ∀ j, a ≤ (p j).1} := by
    ext p
    simp only [Set.mem_iInter, E, Set.mem_ofPred_eq]
    constructor
    · intro h j
      exact h j j le_rfl
    · intro h n j _
      exact h j
  have h := tendsto_measure_iInter_atTop (μ := ν)
    (fun n => (hmeas n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have hr := (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp h
  simpa only [hinter, Function.comp_def, Measure.real, E] using hr

private theorem measureReal_firstCoordinate_prefix (ν : Measure (ℕ → ℤ × ℤ))
    (n : ℕ) (a : ℤ) :
    ν.real {p | ∀ j ≤ n, a ≤ (p j).1} =
      (ν.map (fun p => fun j : Fin (n + 1) => (p j.val).1)).real
        {q | ∀ j, a ≤ q j} := by
  have hevent : (fun p : ℕ → ℤ × ℤ => fun j : Fin (n + 1) => (p j.val).1) ⁻¹'
      {q | ∀ j, a ≤ q j} = {p | ∀ j ≤ n, a ≤ (p j).1} := by
    ext p
    constructor
    · intro hp j hj
      exact hp ⟨j, by omega⟩
    · intro hp j
      exact hp j.val (by omega)
  rw [Measure.real, Measure.real, Measure.map_apply (by fun_prop)
    ((Set.to_countable _).measurableSet), hevent]

/-- Source Lemma 4.10 for an actual two-dimensional probability path law
satisfying the source's full defining RN identity at every horizon. This
identity is standing defining data, not a derived scalar or barrier premise. -/
theorem conditionedSource_barrier_probability
    (x : ℕ) (y : ℤ) (ν : Measure (ℕ → ℤ × ℤ)) [IsProbabilityMeasure ν]
    (hRN : ∀ n : ℕ,
      ν.map (fun q => fun j : Fin (n + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0))
    (s : ℕ) (hs : s ≤ x) :
    ν.real {p | ∀ j, (x : ℤ) - (s : ℤ) ≤ (p j).1} =
      ((s : ℝ) + 1) / ((x : ℝ) + 1) := by
  let a : ℕ := x - s
  have hsa : s + a = x := Nat.add_sub_of_le hs
  have hscalar := firstCoordinate_of_twoDimensional_process_RN x y ν hRN
  have hpref (n : ℕ) :
      ν.real {p | ∀ j ≤ n, (a : ℤ) ≤ (p j).1} =
        lazyWordKilledAverage n (s : ℤ)
          (fun z => ((z : ℝ) + 1 + (a : ℝ)) / ((x : ℝ) + 1)) := by
    rw [measureReal_firstCoordinate_prefix, hscalar n]
    rw [← hsa]
    exact scalarLazyPrefix_barrier_real n s a
  have hfinite : Tendsto
      (fun n : ℕ => ν.real {p | ∀ j ≤ n, (a : ℤ) ≤ (p j).1}) atTop
      (𝓝 (((s : ℝ) + 1) / ((x : ℝ) + 1))) := by
    simpa only [hpref] using
      tendsto_lazyWordKilledAverage_endpoint_weight s x (a : ℝ)
  have hlimit := tendsto_nhds_unique
    (tendsto_measureReal_firstCoordinate_barrier ν (a : ℤ)) hfinite
  have ha : (a : ℤ) = (x : ℤ) - (s : ℤ) := by
    dsimp [a]
    exact Nat.cast_sub hs
  simpa only [ha] using hlimit

end DirectedDistances.RandomWalk
