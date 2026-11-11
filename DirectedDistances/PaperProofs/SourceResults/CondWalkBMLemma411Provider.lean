/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.Lemma411StepTransfer

/-! Supporting lemmas for paper labels `lem-cond-walk-bm` (see CORRESPONDENCE.md). -/

/-! # Provider for Lemma 4.11 (`lem-cond-walk-bm`)

`{n^{-1/2} Ẑ(⌊tn⌋)}_{t ≥ 0}` of the conditioned walk started at `(0,0)` converges in law,
uniformly on compacts, to `√(2/3)(A, (√3/2)B - A/2)`, with `A` a zero-start BES(3) process and
`B` an independent standard Brownian motion.

Encoding:
- `diffusiveStep n z t = n^{-1/2} z(⌊n t⌋)` is the literal floor process
  (`DirectedDistances/RandomWalk/ConditionedFunctionalInterpolation.lean:84`). It is not asserted
  to be continuous in time.
- The common carrier is `UniformOnFun ℝ≥0 (ℝ × ℝ) {K | IsCompact K}` (uniform convergence on
  compacts), with its Borel structure.
  (`DirectedDistances/Paper/Section4/CondWalkRNLaw.lean`).
- `conditionedBrownianPath` under any `W₄` of four independent standard Brownian coordinates is
  the source limit (binder justification at
  `DirectedDistances/RandomWalk/ConditionedLimitPathLaw.lean:281-303`).

The proof is `Lemma411StepTransfer.lemma411_conditioned_step_functional_limit`. It transfers the
interpolation theorem (`Lemma411Final.lean:239`) to the floor process. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.Probability DirectedDistances.RandomWalk
open scoped NNReal

-- The canonical Borel structures on the common path space and on continuous path spaces.
local instance instMeasurableU_CondWalkBMLemma411Provider :
    MeasurableSpace (UniformOnFun ℝ≥0 (ℝ × ℝ) {K | IsCompact K}) := borel _
local instance instBorelU_CondWalkBMLemma411Provider :
    BorelSpace (UniformOnFun ℝ≥0 (ℝ × ℝ) {K | IsCompact K}) := ⟨rfl⟩
local instance instMeasurableC_CondWalkBMLemma411Provider
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] :
    MeasurableSpace C(A, B) := borel _
local instance instBorelC_CondWalkBMLemma411Provider
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] :
    BorelSpace C(A, B) := ⟨rfl⟩




theorem lem_cond_walk_bm_source_provider
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄) :
    TendstoInDistribution
      (fun n z => (UniformOnFun.ofFun {K | IsCompact K} (diffusiveStep n z) :
        UniformOnFun ℝ≥0 (ℝ × ℝ) {K | IsCompact K})) atTop
      (fun p => UniformOnFun.ofFun {K | IsCompact K} (conditionedBrownianPath p))
      (fun _ => conditionedVectorPathLaw 0 0) W₄ :=
  Lemma411StepTransfer.lemma411_conditioned_step_functional_limit W₄ hB hI

end DirectedDistances.PaperProofs.SourceResults
