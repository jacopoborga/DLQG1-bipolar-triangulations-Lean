/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.QuadrantWalkTotal
public import DirectedDistances.RandomWalk.QuadrantPrimedIdentity

/-! # Unconditional totalized quadrant walk laws

associated with `lem-quadrant-walk`
these totalized walks with the manuscript's `S_m,S'_m` walks is not asserted -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW

/-- Almost surely the future code stream from time one has the flow-line-hit
property used to totalize the interval walks -/
theorem iidCodeMeasure_ae_hasFlowLineHits :
    ∀ᵐ ω ∂iidCodeMeasure, HasFlowLineHits (fun i => ω (i + 1)) := by
  filter_upwards [iidCodes_ae_hasFlowLineHits_all_future_times] with ω hhits
  simpa using hhits 0

/-- Almost surely the shifted totalized primed walk is the R-Pitman walk of
the second phase stream, at every horizon -/
theorem quadrantPrimedWalk_shift_identity_ae :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ m,
      quadrantPrimedWalk ω (m + 1) - quadrantPrimedWalk ω 1 =
        rPitmanCodeWalk ((phaseSplit ω).2) m := by
  filter_upwards [iidCodeMeasure_ae_hasFlowLineHits] with ω hhits
  intro m
  rw [quadrantPrimedWalk_eq_interval ω hhits]
  exact quadrantPrimedIntervalWalk_shift_eq_rPitmanCodeWalk ω hhits m

private theorem measurable_vectorPitmanMap_uncond {Ω : Type*}
    [MeasurableSpace Ω] (Z : Ω → ℕ → ℤ × ℤ) (hZ : Measurable Z) :
    Measurable (fun ω k => vectorPitman (Z ω) k) := by
  have hL : Measurable (fun ω k => (Z ω k).1) := by fun_prop
  apply Measurable.of_eval
  intro n
  exact (((measurable_pi_apply n).comp measurable_globalLazyPhi).comp hL).prodMk
    (((measurable_pi_apply n).comp hZ).snd.add
      ((measurable_globalLazyRunningMinimum n).comp hL))

private theorem measurable_rPitmanCodeWalk_uncond :
    Measurable rPitmanCodeWalk := by
  have hrot : Measurable (fun ω : ℕ → Fin 3 =>
      fun n => stepRotate (codeWalk ω n)) :=
    Measurable.of_eval fun n =>
      (measurable_of_countable stepRotate).comp
        ((measurable_pi_apply n).comp measurable_codeWalk)
  have hpit := measurable_vectorPitmanMap_uncond
    (fun ω n => stepRotate (codeWalk ω n)) hrot
  apply Measurable.of_eval
  intro n
  exact (measurable_of_countable stepRotateInv).comp
    ((measurable_pi_apply n).comp hpit)

private theorem measurableQuadrantPrimedReconstruct_uncond :
    Measurable quadrantPrimedReconstruct := by
  apply Measurable.of_eval
  intro n
  cases n with
  | zero => simp [quadrantPrimedReconstruct]
  | succ k =>
      change Measurable (fun p : ℕ → ℤ × ℤ => p k + (0, 1))
      exact (measurable_pi_apply k).add measurable_const

/-- The totalized primed path is almost surely measurable as a path-valued
This uses its proved initial values together with the shifted R-Pitman
identity. -/
theorem aemeasurable_quadrantPrimedWalk :
    AEMeasurable quadrantPrimedWalk iidCodeMeasure := by
  have hR : Measurable (fun ω : ℕ → Fin 3 =>
      rPitmanCodeWalk ((phaseSplit ω).2)) :=
    measurable_rPitmanCodeWalk_uncond.comp
      (measurable_snd.comp measurable_phaseSplit)
  have hproxy : Measurable (quadrantPrimedReconstruct ∘ fun ω =>
      rPitmanCodeWalk ((phaseSplit ω).2)) :=
    measurableQuadrantPrimedReconstruct_uncond.comp hR
  have hae : (quadrantPrimedReconstruct ∘ fun ω =>
      rPitmanCodeWalk ((phaseSplit ω).2)) =ᵐ[iidCodeMeasure]
      quadrantPrimedWalk := by
    filter_upwards [iidCodeMeasure_ae_quadrantPrimedWalk_initial,
      quadrantPrimedWalk_shift_identity_ae] with ω hinit hshift
    funext n
    cases n with
    | zero =>
        simpa [Function.comp, quadrantPrimedReconstruct] using hinit.1.symm
    | succ k =>
        change rPitmanCodeWalk ((phaseSplit ω).2) k + (0, 1) =
          quadrantPrimedWalk ω (k + 1)
        calc
          rPitmanCodeWalk ((phaseSplit ω).2) k + (0, 1) =
              (quadrantPrimedWalk ω (k + 1) - quadrantPrimedWalk ω 1) +
                quadrantPrimedWalk ω 1 := by rw [hshift k, hinit.2]
          _ = quadrantPrimedWalk ω (k + 1) := sub_add_cancel _ _
  exact hproxy.aemeasurable.congr hae

/-- The unconditional conjunction of the code-level clauses for the
prefix laws, the primed initial values, and almost-sure measurability of both
Identifying these totalized paths with the source-defined `S_m,S'_m` walks -/
theorem quadrant_walk_law_total :
    quadrantHatWalk ⟂ᵢ[iidCodeMeasure] quadrantPrimedWalk ∧
    (∀ n, iidCodeMeasure.map (fun ω =>
      fun j : Fin (n + 1) => quadrantHatWalk ω j.val) =
      ((Measure.uniformOfFinset
        (Finset.univ : Finset (Fin n → Fin 3))).map
        (lazyTwoDimensionalPrefix 0 0)).withDensity
        (fun q => if ∀ j, 0 ≤ (q j).1 then
          ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) /
            ((0 : ℝ) + 1)) else 0)) ∧
    (∀ᵐ ω ∂iidCodeMeasure,
      quadrantPrimedWalk ω 0 = (0, 0) ∧
        quadrantPrimedWalk ω 1 = (0, 1)) ∧
    (∀ n, iidCodeMeasure.map (fun ω => fun j : Fin (n + 1) =>
      quadrantPrimedWalk ω (j.val + 1) - quadrantPrimedWalk ω 1) =
        ((Measure.uniformOfFinset
          (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix 0 0)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).2 then
            ENNReal.ofReal ((((q (Fin.last n)).2 : ℝ) + 1) /
              ((0 : ℝ) + 1)) else 0)) ∧
    (AEMeasurable quadrantHatWalk iidCodeMeasure ∧
      AEMeasurable quadrantPrimedWalk iidCodeMeasure) := by
  have Hprimed := quadrantPrimedWalk_shift_identity_ae
  refine ⟨quadrantHatWalk_indep_quadrantPrimedWalk Hprimed, ?_,
    iidCodeMeasure_ae_quadrantPrimedWalk_initial, ?_,
    ⟨aemeasurable_quadrantHatWalk, aemeasurable_quadrantPrimedWalk⟩⟩
  · intro n
    exact quadrantHatWalk_prefix_law n
  · intro n
    exact quadrantPrimedShift_prefix_law Hprimed n

end DirectedDistances.RandomWalk
