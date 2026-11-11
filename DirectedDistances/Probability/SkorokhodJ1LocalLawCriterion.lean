/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodJ1LocalPositive
public import DirectedDistances.Probability.SkorokhodJ1WindowPolishInstance
public import DirectedDistances.Probability.SkorokhodJ1WindowConvergence

import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/

/-! # Helpers toward a local J1 law convergence criterion

Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/

@[expose] public section
namespace DirectedDistances.Probability

open Filter
open MeasureTheory
open scoped Topology

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The finite tuple of cutoff-window coordinates through index `N`. -/
abbrev LocalCutoffTuple (N : ℕ) :=
  (i : Fin (N + 1)) → J1WindowD ((i.val : ℝ) + 1) (by positivity)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The map listing the first `N + 1` cutoff-window coordinates. -/
noncomputable def finiteCutoffWindows (N : ℕ) (x : CadlagLocal) : LocalCutoffTuple N :=
  fun i => toJ1WindowD (cutoffWindow i.val x)




theorem cutoffWindow_continuous (n : ℕ) :
    @Continuous CadlagLocal (CadlagWindow ((n : ℝ) + 1))
      j1LocalMetricSpace.toUniformSpace.toTopologicalSpace
      (j1WindowMetricSpace (by positivity)).toUniformSpace.toTopologicalSpace
      (cutoffWindow n) := by
  apply (@continuous_iff_continuousAt CadlagLocal
    (CadlagWindow ((n : ℝ) + 1))
    j1LocalMetricSpace.toUniformSpace.toTopologicalSpace
    (j1WindowMetricSpace (by positivity)).toUniformSpace.toTopologicalSpace).2
  intro x
  apply (@Metric.continuousAt_iff CadlagLocal (CadlagWindow ((n : ℝ) + 1))
    j1LocalMetricSpace.toPseudoMetricSpace
    (j1WindowMetricSpace (by positivity)).toPseudoMetricSpace).2
  intro ε hε
  let w : ℝ := (1 / 2 : ℝ) ^ (n + 1)
  have hw : 0 < w := by positivity
  have hε' : 0 < min ε 1 := lt_min hε (by norm_num)
  have hδ : 0 < w * min ε 1 := mul_pos hw hε'
  refine ⟨w * min ε 1, hδ, ?_⟩
  intro y hxy
  have hxy' : j1LocalDist x y < w * min ε 1 := by
    change j1LocalDist y x < w * min ε 1 at hxy
    rw [j1LocalDist_symm] at hxy
    exact hxy
  have hterm : w * min 1
      (j1WindowDist (by positivity) (cutoffWindow n x) (cutoffWindow n y)) ≤
      j1LocalDist x y := by
    change localJ1Term n x y ≤ j1LocalDist x y
    simpa only [j1LocalDist, localJ1Term, w] using
      (localJ1Term_summable x y).le_tsum n
        (fun i _ => by
          unfold localJ1Term
          apply mul_nonneg (by positivity)
          exact le_min (by norm_num) (j1WindowDist_nonneg _ _ _))
  have hstrict : w * min 1
      (j1WindowDist (by positivity) (cutoffWindow n x) (cutoffWindow n y)) <
      w * min ε 1 := hterm.trans_lt hxy'
  have hmin : min 1
      (j1WindowDist (by positivity) (cutoffWindow n x) (cutoffWindow n y)) <
      min ε 1 := by
    by_contra h
    have hle : min ε 1 ≤ min 1
        (j1WindowDist (by positivity) (cutoffWindow n x) (cutoffWindow n y)) :=
      le_of_not_gt h
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_left hle hw.le)) hstrict
  have hdist : j1WindowDist (by positivity)
      (cutoffWindow n x) (cutoffWindow n y) < ε := by
    have hone : j1WindowDist (by positivity)
        (cutoffWindow n x) (cutoffWindow n y) < 1 := by
      by_contra h
      rw [min_eq_left (le_of_not_gt h)] at hmin
      exact (not_lt_of_ge (min_le_right ε 1)) hmin
    rw [min_eq_right hone.le] at hmin
    exact hmin.trans_le (min_le_left ε 1)
  change j1WindowDist (by positivity) (cutoffWindow n y)
    (cutoffWindow n x) < ε
  rw [j1WindowDist_symm]
  exact hdist

noncomputable local instance : TopologicalSpace CadlagLocal :=
  j1LocalMetricSpace.toUniformSpace.toTopologicalSpace

noncomputable local instance {N : ℕ} (i : Fin (N + 1)) :
    MetricSpace (CadlagWindow ((i.val : ℝ) + 1)) :=
  j1WindowMetricSpace (by positivity)

noncomputable local instance {N : ℕ} (i : Fin (N + 1) ) :
    TopologicalSpace (CadlagWindow ((i.val : ℝ) + 1)) :=
  (j1WindowMetricSpace (by positivity)).toUniformSpace.toTopologicalSpace

noncomputable local instance {T : ℝ} (hT : 0 < T) :
    TopologicalSpace (J1WindowD T hT) :=
  (j1WindowDMetricSpace hT).toUniformSpace.toTopologicalSpace

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
Every finite tuple of cutoff-window coordinates is globally continuous. -/
theorem finiteCutoffWindows_continuous (N : ℕ) :
    @Continuous CadlagLocal (LocalCutoffTuple N)
      j1LocalMetricSpace.toUniformSpace.toTopologicalSpace
      (@Pi.topologicalSpace (Fin (N + 1))
        (fun i => J1WindowD ((i.val : ℝ) + 1) (by positivity))
        (fun i => (j1WindowDMetricSpace (by positivity)).toUniformSpace.toTopologicalSpace))
      (finiteCutoffWindows N) := by
  apply continuous_pi
  intro i
  have hTo : Continuous (toJ1WindowD :
      CadlagWindow ((i.val : ℝ) + 1) →
        J1WindowD ((i.val : ℝ) + 1) (by positivity)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro z hdist
    have heq : dist (toJ1WindowD z) (toJ1WindowD y) = dist z y := rfl
    rw [heq]
    exact hdist
  exact hTo.comp (cutoffWindow_continuous i.val)

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
Finite cutoff-window laws converge when they factor through a larger window by
a measurable map that is continuous almost everywhere under the limiting law. -/
theorem tendsto_map_finiteCutoffWindows_of_factor
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (μn : ℕ → ProbabilityMeasure CadlagLocal) (μ : ProbabilityMeasure CadlagLocal)
    (N : ℕ)
    (large : CadlagLocal → X) (factor : X → LocalCutoffTuple N)
    (hlarge : Measurable large) (hfactor : Measurable factor)
    (hlimit : Tendsto (fun k => (μn k).map large) atTop
      (𝓝 ((μ.map large))))
    (hfactorCont : ∀ᵐ x ∂(μ.map large : Measure X), ContinuousAt factor x)
    (hfact : ∀ x, finiteCutoffWindows N x = factor (large x)) :
    Tendsto (fun k => (μn k).map (finiteCutoffWindows N)) atTop
      (𝓝 (μ.map (finiteCutoffWindows N))) := by
  have hmap := tendsto_map_of_ae_continuousAt
    (fun k => (μn k).map large) (μ.map large) hlimit factor hfactor hfactorCont
  have hcomp (p : ProbabilityMeasure CadlagLocal) :
      (p.map large).map factor = p.map (finiteCutoffWindows N) := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
      Measure.map_map hfactor hlarge]
    congr 1
    funext x
    exact (hfact x).symm
  simpa only [hcomp] using hmap

end DirectedDistances.Probability
