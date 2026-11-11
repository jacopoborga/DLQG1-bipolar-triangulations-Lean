 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.CondWalkBMLemma411Provider

/-!
# Lemma 4.11 (`lem-cond-walk-bm`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/


















public section
namespace DirectedDistances.Paper.Section4

open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.Probability DirectedDistances.RandomWalk
open scoped NNReal

 
local instance instMeasurableU_PaperCondWalkBM :
    MeasurableSpace (UniformOnFun ℝ≥0 (ℝ × ℝ) {K | IsCompact K}) := borel _
local instance instBorelU_PaperCondWalkBM :
    BorelSpace (UniformOnFun ℝ≥0 (ℝ × ℝ) {K | IsCompact K}) := ⟨rfl⟩
local instance instMeasurableC_PaperCondWalkBM
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] :
    MeasurableSpace C(A, B) := borel _
local instance instBorelC_PaperCondWalkBM
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] :
    BorelSpace C(A, B) := ⟨rfl⟩

 
theorem lem_cond_walk_bm
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄) :
    TendstoInDistribution
      (fun n z => (UniformOnFun.ofFun {K | IsCompact K} (diffusiveStep n z) :
        UniformOnFun ℝ≥0 (ℝ × ℝ) {K | IsCompact K})) atTop
      (fun p => UniformOnFun.ofFun {K | IsCompact K} (conditionedBrownianPath p))
      (fun _ => conditionedVectorPathLaw 0 0) W₄ :=
 
by exact DirectedDistances.PaperProofs.SourceResults.lem_cond_walk_bm_source_provider W₄ hB hI
 
 

end DirectedDistances.Paper.Section4
 
