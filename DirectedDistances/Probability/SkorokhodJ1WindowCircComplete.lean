/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodJ1WindowCircMetric
public import DirectedDistances.Probability.SkorokhodJ1WindowCompleteSeq
public import DirectedDistances.Probability.SkorokhodJ1WindowCompleteSubseqLimit

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Cauchy

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/

@[expose] public section
namespace DirectedDistances.Probability

open Filter
open scoped ENNReal Topology

private theorem j1WindowCirc_cauchy_to_dCirc {T : ℝ} (hT : 0 < T)
    (x : ℕ → J1WindowCirc T hT) (hC : CauchySeq x) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      j1WindowDCirc hT (ofJ1WindowCirc hT (x m))
        (ofJ1WindowCirc hT (x n)) < ENNReal.ofReal ε := by
  rw [Metric.cauchySeq_iff] at hC
  intro ε hε
  obtain ⟨N, hN⟩ := hC ε hε
  refine ⟨N, fun m n hm hn => ?_⟩
  have hdist := hN m hm n hn
  have hreal :
      (j1WindowDCirc hT (ofJ1WindowCirc hT (x m))
        (ofJ1WindowCirc hT (x n))).toReal < ε := by
    simpa only [j1WindowCirc_dist_eq] using hdist
  have hfinite :
      j1WindowDCirc hT (ofJ1WindowCirc hT (x m))
        (ofJ1WindowCirc hT (x n)) < ⊤ :=
    j1WindowDCirc_lt_top hT _ _
  by_contra hnot
  have hle : ENNReal.ofReal ε ≤
      j1WindowDCirc hT (ofJ1WindowCirc hT (x m))
        (ofJ1WindowCirc hT (x n)) := le_of_not_gt hnot
  have hreal' := ENNReal.toReal_mono hfinite.ne hle
  rw [ENNReal.toReal_ofReal hε.le] at hreal'
  linarith





theorem j1WindowCirc_cauchySeq_subseqLimit {T : ℝ} (hT : 0 < T)
    (x : ℕ → J1WindowCirc T hT) (hC : CauchySeq x) :
    ∃ y : J1WindowCirc T hT, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ k, dist (x (φ k)) y ≤ 2 * (1 / 2 : ℝ) ^ k) ∧
      Tendsto (fun k => x (φ k)) atTop (𝓝 y) := by
  let xCad : ℕ → CadlagWindow T := fun k => ofJ1WindowCirc hT (x k)
  have hC' := j1WindowCirc_cauchy_to_dCirc hT x hC
  obtain ⟨φ, μ, hφ, hstepCirc, hμstrict, hxstrict, hsum, htail⟩ :=
    exists_dCirc_cauchy_subseq_timeChanges hT xCad hC'
  let xSub : ℕ → CadlagWindow T := fun k => xCad (φ k)
  have hμ (k : ℕ) :
      j1TimeChangeSlopeNorm (μ k) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) :=
    le_of_lt (hμstrict k)
  have hx (k : ℕ) (t : J1Window T) :
      |(xSub (k + 1)).1 (μ k t) - (xSub k).1 t| ≤ (1 / 2 : ℝ) ^ k :=
    le_of_lt (hxstrict k t)
  let yCad := subseqAlignedLimitWindow hT xSub μ hμ hx
  let y := toJ1WindowCirc hT yCad
  have hdist (k : ℕ) : dist (x (φ k)) y ≤ 2 * (1 / 2 : ℝ) ^ k := by
    rw [j1WindowCirc_dist_eq]
    have hbound :
        j1WindowDCirc hT (ofJ1WindowCirc hT (x (φ k)))
          (ofJ1WindowCirc hT y) ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ k) := by
      simpa [xCad, xSub, y, yCad] using
        (subseqAlignedLimit_dCirc hT xSub μ hμ hx k)
    calc
      _ ≤ (ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ k)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_lt_top.ne hbound
      _ = 2 * (1 / 2 : ℝ) ^ k :=
        ENNReal.toReal_ofReal (by positivity)
  have hgeo : Tendsto (fun k : ℕ => 2 * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (2 : ℝ)
  have hconv : Tendsto (fun k => x (φ k)) atTop (𝓝 y) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := (eventually_atTop.1
      ((tendsto_order.1 hgeo).2 ε hε))
    filter_upwards [eventually_atTop.2 ⟨N, hN⟩] with k hk
    exact (hdist k).trans_lt hk
  exact ⟨y, φ, hφ, hdist, hconv⟩





noncomputable instance j1WindowCircCompleteSpace
    {T : ℝ} (hT : 0 < T) : CompleteSpace (J1WindowCirc T hT) :=
  Metric.complete_of_cauchySeq_tendsto fun x hC => by
    obtain ⟨y, φ, hφ, _, hsub⟩ := j1WindowCirc_cauchySeq_subseqLimit hT x hC
    exact ⟨y, tendsto_nhds_of_cauchySeq_of_subseq hC hφ.tendsto_atTop hsub⟩

end DirectedDistances.Probability
