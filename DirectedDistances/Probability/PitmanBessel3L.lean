/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.PitmanWholePath
import Mathlib.Data.Finset.Max

/-! Helper toward Lemma 4.11: finite-dimensional induction for nonnegative
processes with the same past-weighted sinc transition rule. This is a generic
uniqueness result. The radial Gaussian calculation is not assumed for the
Brownian radius, and the Pitman--Bessel identification is not asserted here. -/

public section

namespace DirectedDistances.Probability.WholePathSinc

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

/-- Helper toward Lemma 4.11: nonnegative processes with the same initial law
and the same past-weighted sinc transition multipliers have identical laws on
every finite set of times. The induction includes zero and repeated times,
and does not assume a Markov property or a transition density. -/
theorem identDistrib_finset_of_sinc_transition
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : Ω → ℝ≥0 → ℝ) (Y : Ω' → ℝ≥0 → ℝ)
    (hX : ∀ t, Measurable (fun ω => X ω t))
    (hY : ∀ t, Measurable (fun ω => Y ω t))
    (hXn : ∀ t, ∀ᵐ ω ∂P, 0 ≤ X ω t)
    (hYn : ∀ t, ∀ᵐ ω ∂Q, 0 ≤ Y ω t)
    (hzero : IdentDistrib (fun ω => X ω 0) (fun ω => Y ω 0) P Q)
    (c : ℝ≥0 → ℝ → ℝ)
    (hPX : ∀ (s u : ℝ≥0) (k : ℕ) (t : Fin k → ℝ≥0),
      (∀ i, t i ≤ s) → ∀ (F : BoundedContinuousFunction (Fin k → ℝ) ℝ) (a : ℝ),
      (∫ ω, F (fun i => X ω (t i)) * Real.sinc (a * X ω (s + u)) ∂P) =
        c u a * ∫ ω, F (fun i => X ω (t i)) * Real.sinc (a * X ω s) ∂P)
    (hQY : ∀ (s u : ℝ≥0) (k : ℕ) (t : Fin k → ℝ≥0),
      (∀ i, t i ≤ s) → ∀ (F : BoundedContinuousFunction (Fin k → ℝ) ℝ) (a : ℝ),
      (∫ ω, F (fun i => Y ω (t i)) * Real.sinc (a * Y ω (s + u)) ∂Q) =
        c u a * ∫ ω, F (fun i => Y ω (t i)) * Real.sinc (a * Y ω s) ∂Q)
    (I : Finset ℝ≥0) :
    IdentDistrib (fun ω (t : I) => X ω t) (fun ω (t : I) => Y ω t) P Q := by
  classical
  have aux (J : Finset ℝ≥0) :
      IdentDistrib (fun ω (t : ↥(insert 0 J)) => X ω t)
        (fun ω (t : ↥(insert 0 J)) => Y ω t) P Q := by
    induction J using Finset.induction_on_max with
    | empty =>
      have he := hzero.comp (measurable_pi_iff.mpr
        (fun _ : ↥(insert 0 (∅ : Finset ℝ≥0)) => measurable_id))
      convert he using 1 <;> funext ω t
      all_goals
        have ht : t.val = 0 := by simpa only [Finset.mem_insert, Finset.notMem_empty, or_false] using t.property
        simp only [Function.comp_apply, ht, id_eq]
    | insert b J hlt ih =>
      by_cases hb : b = 0
      · subst b
        rw [Finset.insert_idem]
        exact ih
      let K := insert 0 J
      have hK : K.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
      let s := K.max' hK
      have hsK : s ∈ K := K.max'_mem hK
      have hsb : s ≤ b := by
        apply Finset.max'_le
        intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact zero_le
        · exact (hlt t ht).le
      let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
      let t : Fin (Fintype.card K) → ℝ≥0 := fun i => (e.symm i).val
      have ht (i) : t i ≤ s := K.le_max' _ (e.symm i).property
      let j : Fin (Fintype.card K) := e ⟨s, hsK⟩
      have htj : t j = s := by simp only [t, j, Equiv.symm_apply_apply]
      have hfin : IdentDistrib (fun ω i => X ω (t i))
          (fun ω i => Y ω (t i)) P Q :=
        ih.comp (measurable_pi_iff.mpr (fun i => measurable_pi_apply (e.symm i)))
      have hpair : IdentDistrib (fun ω => ((fun i => X ω (t i)), X ω b))
          (fun ω => ((fun i => Y ω (t i)), Y ω b)) P Q := by
        apply identDistrib_prod_of_integral_mul_sinc_eq_of_nonneg
          ((measurable_pi_iff.mpr (fun i => hX (t i))).prodMk (hX b)).aemeasurable
          ((measurable_pi_iff.mpr (fun i => hY (t i))).prodMk (hY b)).aemeasurable
          (hXn b) (hYn b)
        intro F a
        have hxb := hPX s (b - s) _ t ht F a
        have hyb := hQY s (b - s) _ t ht F a
        rw [add_tsub_cancel_of_le hsb] at hxb hyb
        rw [hxb, hyb]
        congr 1
        have he := (hfin.comp
          (show Measurable (fun v : Fin (Fintype.card K) → ℝ =>
            F v * Real.sinc (a * v j)) by fun_prop)).integral_eq
        simpa only [Function.comp_apply, htj] using he
      let r : ((Fin (Fintype.card K) → ℝ) × ℝ) → ↥(insert b K) → ℝ :=
        fun v z => if hz : z.val = b then v.2 else
          v.1 (e ⟨z.val, (Finset.mem_insert.mp z.property).resolve_left hz⟩)
      have hr : Measurable r := by
        apply measurable_pi_iff.mpr
        intro z
        by_cases hz : z.val = b
        · simpa only [r, dite_eq_left hz] using measurable_snd
        · simpa only [r, dite_eq_right hz, Function.comp_def] using
            (measurable_pi_apply (e ⟨z.val,
              (Finset.mem_insert.mp z.property).resolve_left hz⟩)).comp measurable_fst
      rw [Finset.insert_comm]
      change IdentDistrib (fun ω (z : ↥(insert b K)) => X ω z)
        (fun ω (z : ↥(insert b K)) => Y ω z) P Q
      convert hpair.comp hr using 1 <;> funext ω z
      all_goals
        dsimp only [Function.comp_def, r]
        split_ifs with hz
        · rw [hz]
        · simp only [t, Equiv.symm_apply_apply]
  exact (aux I).comp (measurable_pi_iff.mpr (fun t : I => measurable_pi_apply
    (⟨t.val, Finset.mem_insert_of_mem t.property⟩ : ↥(insert 0 I))))

local instance pitman3LContinuousMapMeasurableSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    MeasurableSpace C(X, Y) := borel _
local instance pitman3LContinuousMapBorelSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    BorelSpace C(X, Y) := ⟨rfl⟩

/-- Helper toward Lemma 4.11: the same initial law and past-weighted sinc
transition rule determine the entire law of a nonnegative continuous process.
This upgrades the finite-set induction using the Borel structure of the
compact-open path space, rather than only asserting one-time uniqueness. -/
theorem identDistrib_continuousPath_of_sinc_transition
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : Ω → C(ℝ≥0, ℝ)) (Y : Ω' → C(ℝ≥0, ℝ))
    (hX : Measurable X) (hY : Measurable Y)
    (hXn : ∀ t, ∀ᵐ ω ∂P, 0 ≤ X ω t)
    (hYn : ∀ t, ∀ᵐ ω ∂Q, 0 ≤ Y ω t)
    (hzero : IdentDistrib (fun ω => X ω 0) (fun ω => Y ω 0) P Q)
    (c : ℝ≥0 → ℝ → ℝ)
    (hPX : ∀ (s u : ℝ≥0) (k : ℕ) (t : Fin k → ℝ≥0),
      (∀ i, t i ≤ s) → ∀ (F : BoundedContinuousFunction (Fin k → ℝ) ℝ) (a : ℝ),
      (∫ ω, F (fun i => X ω (t i)) * Real.sinc (a * X ω (s + u)) ∂P) =
        c u a * ∫ ω, F (fun i => X ω (t i)) * Real.sinc (a * X ω s) ∂P)
    (hQY : ∀ (s u : ℝ≥0) (k : ℕ) (t : Fin k → ℝ≥0),
      (∀ i, t i ≤ s) → ∀ (F : BoundedContinuousFunction (Fin k → ℝ) ℝ) (a : ℝ),
      (∫ ω, F (fun i => Y ω (t i)) * Real.sinc (a * Y ω (s + u)) ∂Q) =
        c u a * ∫ ω, F (fun i => Y ω (t i)) * Real.sinc (a * Y ω s) ∂Q) :
    IdentDistrib X Y P Q := by
  refine ⟨hX.aemeasurable, hY.aemeasurable, ?_⟩
  apply continuousScalarPath_measure_ext_of_finset
  intro I
  have hm : Measurable (fun f : C(ℝ≥0, ℝ) => I.restrict (fun t => f t)) :=
    (continuous_pi (fun t : I => continuous_eval_const t.val)).measurable
  rw [Measure.map_map hm hX, Measure.map_map hm hY]
  exact (identDistrib_finset_of_sinc_transition
    (fun ω t => X ω t) (fun ω t => Y ω t)
    (fun t => (continuous_eval_const t).measurable.comp hX)
    (fun t => (continuous_eval_const t).measurable.comp hY)
    hXn hYn hzero c hPX hQY I).map_eq

end DirectedDistances.Probability.WholePathSinc
