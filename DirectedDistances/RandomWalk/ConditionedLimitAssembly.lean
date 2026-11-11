/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.ConditionedLimitPathLaw2

/-! Helper toward Lemma 4.11: conditional assembly of the iid path limit,
whole-path Pitman identification, and the deterministic interpolation error. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory Filter
open DirectedDistances.Probability
open scoped Topology NNReal

-- These are the canonical locally uniform Borel structures used in
-- `ConditionedLimitPathLaw.lean`.
local instance : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance : MeasurableSpace C(ℝ≥0, ℝ × ℝ) := borel _
local instance : BorelSpace C(ℝ≥0, ℝ × ℝ) := ⟨rfl⟩
local instance : MeasurableSpace C(ℝ≥0, Fin 4 → ℝ) := borel _
local instance : BorelSpace C(ℝ≥0, Fin 4 → ℝ) := ⟨rfl⟩
local instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [LocallyCompactSpace X] [SecondCountableTopology Y] :
    SecondCountableTopology C(X, Y) := continuousPath_secondCountable

/-- Helper toward Lemma 4.11: conditional on the iid functional limit (H1),
continuous mapping gives convergence after applying the whole-path vector Pitman map. -/
theorem lemma411_iid_limit_after_continuousVectorPitman
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (H1 : TendstoInDistribution
      (fun n ω => diffusiveInterpolation n (codeWalk ω)) atTop
      iidBrownianPath (fun _ => iidCodeMeasure) W₄) :
    TendstoInDistribution
      (fun n ω => continuousVectorPitman (diffusiveInterpolation n (codeWalk ω))) atTop
      (fun p => continuousVectorPitman (iidBrownianPath p))
      (fun _ => iidCodeMeasure) W₄ := by
  exact TendstoInDistribution.continuous_comp continuous_continuousVectorPitman H1

/-- Helper toward Lemma 4.11: the coupled discrete Pitman step path is uniformly
within the recorded coordinate errors of the continuous Pitman transform of the
interpolated code walk on every compact time interval. -/
theorem lemma411_coupled_step_perturbation_bound (n : ℕ) (hn : 0 < n)
    (ω : ℕ → Fin 3) (T : ℝ≥0) :
    sSup ((fun t => |(diffusiveStep n (vectorPitman (codeWalk ω)) t).1 -
      (continuousVectorPitman (diffusiveInterpolation n (codeWalk ω)) t).1|) ''
      Set.Icc 0 T) ≤ 3 / Real.sqrt n ∧
    sSup ((fun t => |(diffusiveStep n (vectorPitman (codeWalk ω)) t).2 -
      (continuousVectorPitman (diffusiveInterpolation n (codeWalk ω)) t).2|) ''
      Set.Icc 0 T) ≤ 2 / Real.sqrt n :=
  codeWalk_vectorPitman_interpolation_sup_le n hn ω T

/-- Helper toward Lemma 4.11: conditional on the whole-path identification (H2),
the continuous-mapping limit law is the manuscript's conditioned Brownian path law. -/
theorem lemma411_limit_law_rewrite
    (W₄ : Measure C(ℝ≥0, Fin 4 → ℝ)) [IsProbabilityMeasure W₄]
    (hB : ∀ i : Fin 4,
      IsBrownianReal (fun t (p : C(ℝ≥0, Fin 4 → ℝ)) => p t i) W₄)
    (hI : iIndepFun
      (fun i (p : C(ℝ≥0, Fin 4 → ℝ)) => pathCoordinate p i) W₄)
    (H2 : (iidBrownianPathLaw W₄).map continuousVectorPitman =
      conditionedBrownianPathLaw W₄) :
    W₄.map (fun p => continuousVectorPitman (iidBrownianPath p)) =
      conditionedBrownianPathLaw W₄ := by
  have hmap : (iidBrownianPathLaw W₄).map continuousVectorPitman =
      W₄.map (fun p => continuousVectorPitman (iidBrownianPath p)) := by
    unfold iidBrownianPathLaw
    rw [Measure.map_map continuous_continuousVectorPitman.measurable
      continuous_iidBrownianPath.measurable]
    rfl
  exact hmap.symm.trans H2

/-- Helper toward Lemma 4.11: the conditioned polygonal path law is exactly
the image of the iid code law under the discrete Pitman transform and interpolation. -/
theorem lemma411_conditioned_interpolation_coupling (n : ℕ) :
    conditionedInterpolationPathLaw n =
      iidCodeMeasure.map (fun ω => diffusiveInterpolation n (vectorPitman (codeWalk ω))) :=
  conditionedInterpolationPathLaw_eq_map n
















end DirectedDistances.RandomWalk
