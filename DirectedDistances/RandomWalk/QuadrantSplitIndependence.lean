/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.QuadrantSplit

/-! Supporting lemmas for paper labels `lem-quadrant-walk`, `prop-future-map-law` (see CORRESPONDENCE.md). -/









public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

/-- The joint law of arbitrary measurable functions of the two code streams
extracted by `phaseSplit` is the product of their individual iid-code laws.
This is a code-level interface toward `prop-future-map-law` and
It does not identify these outputs with the map encodings and is not counted
as either paper result. -/
theorem map_phaseSplit_comp_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {F : (ℕ → Fin 3) → α} {G : (ℕ → Fin 3) → β}
    (hF : Measurable F) (hG : Measurable G) :
    iidCodeMeasure.map (fun ω => (F ((phaseSplit ω).1), G ((phaseSplit ω).2))) =
      (iidCodeMeasure.map F).prod (iidCodeMeasure.map G) := by
  let pairMap : (ℕ → Fin 3) × (ℕ → Fin 3) → α × β :=
    fun ab => (F ab.1, G ab.2)
  have hpair : Measurable pairMap :=
    (hF.comp measurable_fst).prodMk (hG.comp measurable_snd)
  calc
    iidCodeMeasure.map (fun ω => (F ((phaseSplit ω).1), G ((phaseSplit ω).2))) =
        (iidCodeMeasure.map phaseSplit).map pairMap := by
          rw [Measure.map_map hpair measurable_phaseSplit]
          rfl
    _ = (iidCodeMeasure.prod iidCodeMeasure).map pairMap :=
      congrArg (fun μ : Measure ((ℕ → Fin 3) × (ℕ → Fin 3)) => μ.map pairMap)
        map_phaseSplit_iidCodeMeasure
    _ = (iidCodeMeasure.map F).prod (iidCodeMeasure.map G) := by
      change (iidCodeMeasure.prod iidCodeMeasure).map (Prod.map F G) = _
      rw [← Measure.map_prod_map iidCodeMeasure iidCodeMeasure hF hG]

/-- The first phase-split code stream retains the iid code law after any
measurable observation. This is part of the code-level interface toward
`prop-future-map-law` and `lem-quadrant-walk`
identify the observation with a map encoding and is not counted as a paper
result. -/
theorem map_phaseSplit_fst_comp {α : Type*} [MeasurableSpace α]
    {F : (ℕ → Fin 3) → α} (hF : Measurable F) :
    iidCodeMeasure.map (fun ω => F ((phaseSplit ω).1)) = iidCodeMeasure.map F := by
  have hcomp : Measurable (fun p : (ℕ → Fin 3) × (ℕ → Fin 3) => F p.1) :=
    hF.comp measurable_fst
  calc
    iidCodeMeasure.map (fun ω => F ((phaseSplit ω).1)) =
        (iidCodeMeasure.map phaseSplit).map (fun p => F p.1) := by
          rw [Measure.map_map hcomp measurable_phaseSplit]
          rfl
    _ = (iidCodeMeasure.prod iidCodeMeasure).map (fun p => F p.1) := by
      rw [map_phaseSplit_iidCodeMeasure]
    _ = iidCodeMeasure.map F := by
      change (iidCodeMeasure.prod iidCodeMeasure).map (F ∘ Prod.fst) = _
      calc
        (iidCodeMeasure.prod iidCodeMeasure).map (F ∘ Prod.fst) =
            ((iidCodeMeasure.prod iidCodeMeasure).map Prod.fst).map F := by
              rw [Measure.map_map hF measurable_fst]
        _ = iidCodeMeasure.map F := by simp

/-- The second phase-split code stream retains the iid code law after any
measurable observation. This is part of the code-level interface toward
`prop-future-map-law` and `lem-quadrant-walk`
identify the observation with a map encoding and is not counted as a paper
result. -/
theorem map_phaseSplit_snd_comp {α : Type*} [MeasurableSpace α]
    {F : (ℕ → Fin 3) → α} (hF : Measurable F) :
    iidCodeMeasure.map (fun ω => F ((phaseSplit ω).2)) = iidCodeMeasure.map F := by
  have hcomp : Measurable (fun p : (ℕ → Fin 3) × (ℕ → Fin 3) => F p.2) :=
    hF.comp measurable_snd
  calc
    iidCodeMeasure.map (fun ω => F ((phaseSplit ω).2)) =
        (iidCodeMeasure.map phaseSplit).map (fun p => F p.2) := by
          rw [Measure.map_map hcomp measurable_phaseSplit]
          rfl
    _ = (iidCodeMeasure.prod iidCodeMeasure).map (fun p => F p.2) := by
      rw [map_phaseSplit_iidCodeMeasure]
    _ = iidCodeMeasure.map F := by
      change (iidCodeMeasure.prod iidCodeMeasure).map (F ∘ Prod.snd) = _
      calc
        (iidCodeMeasure.prod iidCodeMeasure).map (F ∘ Prod.snd) =
            ((iidCodeMeasure.prod iidCodeMeasure).map Prod.snd).map F := by
              rw [Measure.map_map hF measurable_snd]
        _ = iidCodeMeasure.map F := by simp

/-- The two arbitrary measurable observations of the phase-split code
streams are independent. This gives the code-level independence interface
toward `prop-future-map-law` and `lem-quadrant-walk`
identify the observations with the map encodings and is not counted as either
paper result. -/
theorem indepFun_phaseSplit_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {F : (ℕ → Fin 3) → α} {G : (ℕ → Fin 3) → β}
    (hF : Measurable F) (hG : Measurable G) :
    IndepFun (fun ω => F ((phaseSplit ω).1)) (fun ω => G ((phaseSplit ω).2)) iidCodeMeasure := by
  have hleft : Measurable (fun ω => F ((phaseSplit ω).1)) :=
    hF.comp (measurable_fst.comp measurable_phaseSplit)
  have hright : Measurable (fun ω => G ((phaseSplit ω).2)) :=
    hG.comp (measurable_snd.comp measurable_phaseSplit)
  rw [indepFun_iff_map_prod_eq_prod_map_map hleft.aemeasurable hright.aemeasurable]
  rw [map_phaseSplit_comp_prod hF hG,
    map_phaseSplit_fst_comp hF, map_phaseSplit_snd_comp hG]

end DirectedDistances.RandomWalk
