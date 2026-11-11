/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Paper.Section4.CondWalkRNLaw
public import DirectedDistances.RandomWalk.LazyVectorTranslation
import Mathlib.Tactic.Ring
import DirectedDistances.RandomWalk.ConditionedVectorPrefixSupport

/-! Supporting lemmas for paper labels `lem-boltzmann-ldp-lower` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.RandomWalk
open MeasureTheory
open scoped ENNReal
private theorem map_withDensity_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (e : α ≃ᵐ β) (μ : Measure α) (f : α → ℝ≥0∞)
    (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun b => f (e.symm b)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply f (hs.preimage e.measurable), withDensity_apply _ hs]
  calc
    ∫⁻ a in e ⁻¹' s, f a ∂μ =
        ∫⁻ a in e ⁻¹' s, f (e.symm (e a)) ∂μ := by simp
    _ = ∫⁻ b in s, f (e.symm b) ∂μ.map e := by
      simpa using
        (setLIntegral_map hs (hf.comp e.symm.measurable) e.measurable).symm
private def translatedPrefixEquiv (n : ℕ) (a : ℤ × ℤ) :
    (Fin (n + 1) → ℤ × ℤ) ≃ᵐ (Fin (n + 1) → ℤ × ℤ) := {
  toEquiv := {
    toFun := fun q j => q j - a,
    invFun := fun q j => q j + a,
    left_inv := by intro q; funext j; simp,
    right_inv := by intro q; funext j; simp }
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _ }
/-- The centered prefix law from `cond_walk_rn_law`, with its corrected shifted endpoint
weight. -/
theorem conditionedVectorPathLaw_centeredPrefix_law (x : ℕ) (y : ℤ) (n : ℕ) :
    (conditionedVectorPathLaw x y).map (fun q => fun j : Fin (n + 1) => q j.val - q 0) =
      ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
        (lazyTwoDimensionalPrefix 0 0)).withDensity
        (fun q => if ∀ j, -(x : ℤ) ≤ (q j).1 then
          ENNReal.ofReal ((((x : ℝ) + (q (Fin.last n)).1 + 1) / ((x : ℝ) + 1)))
          else 0) := by
  let a : ℤ × ℤ := (x, y)
  let e := translatedPrefixEquiv n a
  let μ := (Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
    (lazyTwoDimensionalPrefix (x : ℤ) y)
  let f := fun q : Fin (n + 1) → ℤ × ℤ => if ∀ j, 0 ≤ (q j).1 then
    ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0
  have hden (q : Fin (n + 1) → ℤ × ℤ) : f (e.symm q) =
      if ∀ j, -(x : ℤ) ≤ (q j).1 then
        ENNReal.ofReal ((((x : ℝ) + (q (Fin.last n)).1 + 1) / ((x : ℝ) + 1))) else 0 := by
    have hb : (∀ j, 0 ≤ (e.symm q j).1) ↔ ∀ j, -(x : ℤ) ≤ (q j).1 := by
      constructor <;> intro h j
      · have hh : 0 ≤ (q j).1 + (x : ℤ) := by
          simpa [e, translatedPrefixEquiv, a] using h j
        omega
      · have hh : 0 ≤ (q j).1 + (x : ℤ) := by have := h j; omega
        simpa [e, translatedPrefixEquiv, a] using hh
    by_cases hq : ∀ j, -(x : ℤ) ≤ (q j).1
    · have hs := hb.mpr hq
      have hw : ((((e.symm q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) =
          (((x : ℝ) + (q (Fin.last n)).1 + 1) / ((x : ℝ) + 1)) := by
        simp [e, translatedPrefixEquiv, a, Prod.fst_add, Int.cast_add,
          Int.cast_natCast]; ring
      dsimp only [f]
      rw [ite_eq_left hs, ite_eq_left hq]
      exact congrArg ENNReal.ofReal hw
    · have hs : ¬ (∀ j, 0 ≤ (e.symm q j).1) := fun h => hq (hb.mp h)
      dsimp only [f]
      rw [ite_eq_right hs, ite_eq_right hq]
  have hstart : ∀ᵐ q ∂conditionedVectorPathLaw x y, q 0 = ((x : ℤ), y) := by
    filter_upwards [conditionedSource_ae_prefix_mem_range x y
      (conditionedVectorPathLaw x y) (conditionedVectorPathLaw_map_prefix x y) 0] with q hq
    change (fun j : Fin 1 => q j.val) ∈ Set.range (@lazyTwoDimensionalPrefix 0 (x : ℤ) y) at hq
    obtain ⟨w, hw⟩ := hq
    simpa [lazyTwoDimensionalPrefix] using (congrFun hw ⟨0, by omega⟩).symm
  have hEq : (fun q => fun j : Fin (n + 1) => q j.val - q 0) =ᵐ[
      conditionedVectorPathLaw x y] (fun q => fun j => q j.val - ((x : ℤ), y)) := by
    filter_upwards [hstart] with q hq
    funext j; rw [hq]
  calc
    (conditionedVectorPathLaw x y).map
        (fun q => fun j : Fin (n + 1) => q j.val - q 0) =
      ((conditionedVectorPathLaw x y).map
        (fun q => fun j : Fin (n + 1) => q j.val)).map e := by
          rw [Measure.map_congr hEq]
          have he : (fun q : ℕ → ℤ × ℤ =>
              fun j : Fin (n + 1) => q j.val - a) =
              fun q => e (fun j : Fin (n + 1) => q j.val) := by
            funext q j
            simp [e, translatedPrefixEquiv]
          have hprefix : Measurable (fun q : ℕ → ℤ × ℤ =>
              fun j : Fin (n + 1) => q j.val) := by
            exact .of_eval fun j => measurable_pi_apply j.val
          rw [he, Measure.map_map e.measurable hprefix]
          rfl
    _ = (μ.withDensity f).map e := by rw [conditionedVectorPathLaw_map_prefix]
    _ = (μ.map e).withDensity (fun q => f (e.symm q)) :=
          map_withDensity_measurableEquiv e μ f (measurable_of_countable _)
    _ = ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity (fun q => if ∀ j,
            -(x : ℤ) ≤ (q j).1 then ENNReal.ofReal
              ((((x : ℝ) + (q (Fin.last n)).1 + 1) / ((x : ℝ) + 1))) else 0) := by
          rw [show μ.map e = _ from by
            simpa [μ, e, translatedPrefixEquiv, a] using
              map_uniform_lazyTwoDimensionalPrefix_sub_start n (x : ℤ) y]
          congr 1
          funext q
          exact hden q
end DirectedDistances.RandomWalk
