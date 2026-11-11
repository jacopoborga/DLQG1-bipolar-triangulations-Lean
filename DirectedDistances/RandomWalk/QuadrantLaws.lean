/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.QuadrantSplit

/-! # Product law for the two split Pitman walks

The code streams obtained by `phaseSplit` generate independent conditioned
walks after applying the two Pitman maps. This formalizes the law assertion in
using its disputed printed first-step value for the primed walk. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

private theorem measurable_vectorPitman_map {Ω : Type*} [MeasurableSpace Ω]
    (Z : Ω → ℕ → ℤ × ℤ) (hZ : Measurable Z) :
    Measurable (fun ω k => vectorPitman (Z ω) k) := by
  have hL : Measurable (fun ω k => (Z ω k).1) := by fun_prop
  apply Measurable.of_eval
  intro n
  exact (((measurable_pi_apply n).comp measurable_globalLazyPhi).comp hL).prodMk
    (((measurable_pi_apply n).comp hZ).snd.add
      ((measurable_globalLazyRunningMinimum n).comp hL))

/-- The vector Pitman process of the iid code walk -/
@[expose] noncomputable def vectorPitmanCodeWalk (ω : ℕ → Fin 3) : ℕ → ℤ × ℤ :=
  fun k => vectorPitman (codeWalk ω) k

/-- The R-Pitman process of the iid code walk, using the rotation -/
@[expose] noncomputable def rPitmanCodeWalk (ω : ℕ → Fin 3) : ℕ → ℤ × ℤ :=
  fun k => stepRotateInv (vectorPitman (fun n => stepRotate (codeWalk ω n)) k)

private theorem measurable_vectorPitmanCodeWalk : Measurable vectorPitmanCodeWalk := by
  change Measurable (fun ω k => vectorPitman (codeWalk ω) k)
  exact measurable_vectorPitman_map codeWalk measurable_codeWalk

private theorem measurable_rPitmanCodeWalk : Measurable rPitmanCodeWalk := by
  have hrot : Measurable (fun ω : ℕ → Fin 3 => fun n => stepRotate (codeWalk ω n)) :=
    Measurable.of_eval fun n =>
      (measurable_of_countable stepRotate).comp
        ((measurable_pi_apply n).comp measurable_codeWalk)
  have hpit := measurable_vectorPitman_map
    (fun ω n => stepRotate (codeWalk ω n)) hrot
  apply Measurable.of_eval
  intro n
  exact (measurable_of_countable stepRotateInv).comp
    ((measurable_pi_apply n).comp hpit)

/-- The joint law of the two Pitman processes driven by the phase-split code
streams is the product of the L-conditioned and R-conditioned path laws -/
theorem map_phaseSplit_pitmanProcesses :
    iidCodeMeasure.map (fun ω =>
      (vectorPitmanCodeWalk ((phaseSplit ω).1), rPitmanCodeWalk ((phaseSplit ω).2))) =
      (conditionedVectorPathLaw 0 0).prod (rConditionedPathLaw 0 0) := by
  let pairMap : (ℕ → Fin 3) × (ℕ → Fin 3) →
      (ℕ → ℤ × ℤ) × (ℕ → ℤ × ℤ) :=
    fun ab => (vectorPitmanCodeWalk ab.1, rPitmanCodeWalk ab.2)
  have hpair : Measurable pairMap :=
    (measurable_vectorPitmanCodeWalk.comp measurable_fst).prodMk
      (measurable_rPitmanCodeWalk.comp measurable_snd)
  calc
    iidCodeMeasure.map (fun ω =>
        (vectorPitmanCodeWalk ((phaseSplit ω).1), rPitmanCodeWalk ((phaseSplit ω).2))) =
        (iidCodeMeasure.map phaseSplit).map pairMap := by
          rw [Measure.map_map hpair measurable_phaseSplit]
          rfl
    _ = (iidCodeMeasure.prod iidCodeMeasure).map pairMap := by
          exact congrArg (fun μ => μ.map pairMap) map_phaseSplit_iidCodeMeasure
    _ = (conditionedVectorPathLaw 0 0).prod (rConditionedPathLaw 0 0) := by
          change (iidCodeMeasure.prod iidCodeMeasure).map
            (Prod.map vectorPitmanCodeWalk rPitmanCodeWalk) = _
          rw [← Measure.map_prod_map iidCodeMeasure iidCodeMeasure
            measurable_vectorPitmanCodeWalk measurable_rPitmanCodeWalk]
          change (iidCodeMeasure.map
              (fun ω k => vectorPitman (codeWalk ω) k)).prod
            (iidCodeMeasure.map (fun ω k =>
              stepRotateInv (vectorPitman (fun n => stepRotate (codeWalk ω n)) k))) = _
          rw [map_vectorPitman_codeWalk, map_rPitman_codeWalk]

/-- The L-Pitman and R-Pitman processes produced by `phaseSplit` are -/
theorem indepFun_phaseSplit_pitmanProcesses :
    (fun ω => vectorPitmanCodeWalk ((phaseSplit ω).1)) ⟂ᵢ[iidCodeMeasure]
      (fun ω => rPitmanCodeWalk ((phaseSplit ω).2)) := by
  have hleftMeas : Measurable
      (fun ω => vectorPitmanCodeWalk ((phaseSplit ω).1)) :=
    measurable_vectorPitmanCodeWalk.comp (measurable_fst.comp measurable_phaseSplit)
  have hrightMeas : Measurable
      (fun ω => rPitmanCodeWalk ((phaseSplit ω).2)) :=
    measurable_rPitmanCodeWalk.comp (measurable_snd.comp measurable_phaseSplit)
  have hjointMeas : Measurable (fun ω =>
      (vectorPitmanCodeWalk ((phaseSplit ω).1), rPitmanCodeWalk ((phaseSplit ω).2))) :=
    hleftMeas.prodMk hrightMeas
  rw [indepFun_iff_map_prod_eq_prod_map_map hleftMeas.aemeasurable hrightMeas.aemeasurable]
  have hjoint := map_phaseSplit_pitmanProcesses
  have hleft :
      iidCodeMeasure.map (fun ω => vectorPitmanCodeWalk ((phaseSplit ω).1)) =
        conditionedVectorPathLaw 0 0 := by
    calc
      iidCodeMeasure.map (fun ω => vectorPitmanCodeWalk ((phaseSplit ω).1)) =
          (iidCodeMeasure.map (fun ω =>
            (vectorPitmanCodeWalk ((phaseSplit ω).1), rPitmanCodeWalk ((phaseSplit ω).2)))).map
              Prod.fst := by
                rw [Measure.map_map measurable_fst hjointMeas]
                rfl
      _ = ((conditionedVectorPathLaw 0 0).prod (rConditionedPathLaw 0 0)).map
            Prod.fst := congrArg (fun μ => μ.map Prod.fst) hjoint
      _ = conditionedVectorPathLaw 0 0 := by simp
  have hright :
      iidCodeMeasure.map (fun ω => rPitmanCodeWalk ((phaseSplit ω).2)) =
        rConditionedPathLaw 0 0 := by
    calc
      iidCodeMeasure.map (fun ω => rPitmanCodeWalk ((phaseSplit ω).2)) =
          (iidCodeMeasure.map (fun ω =>
            (vectorPitmanCodeWalk ((phaseSplit ω).1), rPitmanCodeWalk ((phaseSplit ω).2)))).map
              Prod.snd := by
                rw [Measure.map_map measurable_snd hjointMeas]
                rfl
      _ = ((conditionedVectorPathLaw 0 0).prod (rConditionedPathLaw 0 0)).map
            Prod.snd := congrArg (fun μ => μ.map Prod.snd) hjoint
      _ = rConditionedPathLaw 0 0 := by simp
  rw [hjoint, hleft, hright]

end DirectedDistances.RandomWalk
