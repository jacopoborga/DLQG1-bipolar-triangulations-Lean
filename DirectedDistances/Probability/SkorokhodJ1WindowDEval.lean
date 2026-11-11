module

public import DirectedDistances.Probability.SkorokhodJ1WindowEvaluation
public import DirectedDistances.Probability.SkorokhodJ1WindowPolish

import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Evaluation maps on the J1 metric window carrier

This transfers evaluation continuity to `J1WindowD`, whose metric is
`j1WindowDist` on the underlying `CadlagWindow` paths. -/

@[expose] public section
namespace DirectedDistances.Probability

private theorem j1WindowD_dist_lt_exists_timeChange {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T) (δ : ℝ) (hδ : j1WindowDist hT f g < δ) :
    ∃ φ : J1TimeChange T,
      (∀ t, |(φ t : ℝ) - (t : ℝ)| < δ) ∧
      (∀ t, |f.1 (φ t) - g.1 t| < δ) := by
  change (⨅ φ : J1TimeChange T,
    max (⨆ t : J1Window T, |((φ t : ℝ) - (t : ℝ))|)
      (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|)) < δ at hδ
  obtain ⟨φ, hcost⟩ := exists_lt_of_ciInf_lt hδ
  refine ⟨φ, ?_, ?_⟩
  · intro t
    calc
      |(φ t : ℝ) - (t : ℝ)| ≤
          ⨆ s : J1Window T, |((φ s : ℝ) - (s : ℝ))| :=
        le_ciSup_of_le (j1WindowTimeChangeDistortion_bddAbove φ) t le_rfl
      _ ≤ max (⨆ s : J1Window T, |((φ s : ℝ) - (s : ℝ))|)
          (⨆ s : J1Window T, |f.1 (φ s) - g.1 s|) := le_max_left _ _
      _ < δ := hcost
  · intro t
    calc
      |f.1 (φ t) - g.1 t| ≤ ⨆ s : J1Window T, |f.1 (φ s) - g.1 s| :=
        le_ciSup_of_le (j1WindowValueError_bddAbove f g φ) t le_rfl
      _ ≤ max (⨆ s : J1Window T, |((φ s : ℝ) - (s : ℝ))|)
          (⨆ s : J1Window T, |f.1 (φ s) - g.1 s|) := le_max_right _ _
      _ < δ := hcost




theorem j1WindowD_eval_continuousAt {T : ℝ} (hT : 0 < T)
    (x : J1WindowD T hT) (t : J1Window T)
    (h : ContinuousAt x.path.1 t) :
    ContinuousAt (fun y : J1WindowD T hT => y.path.1 t) x := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨r, hr, hfr⟩ := (Metric.continuousAt_iff.mp h) (ε / 3) hthird
  refine ⟨min r (ε / 3), lt_min hr hthird, ?_⟩
  intro y hdist
  have hdist' : j1WindowDist hT x.path y.path < min r (ε / 3) := by
    change j1WindowDist hT y.path x.path < min r (ε / 3) at hdist
    rw [j1WindowDist_symm hT]
    exact hdist
  obtain ⟨φ, hdisp, hvalue⟩ :=
    j1WindowD_dist_lt_exists_timeChange hT x.path y.path _ hdist'
  have hφt : dist (φ t) t < r := by
    rw [Subtype.dist_eq, Real.dist_eq]
    exact (hdisp t).trans_le (min_le_left _ _)
  have hft : dist (x.path.1 (φ t)) (x.path.1 t) < ε / 3 := hfr hφt
  have hyt : dist (y.path.1 t) (x.path.1 (φ t)) < ε / 3 := by
    simpa [Real.dist_eq, abs_sub_comm] using
      (hvalue t).trans_le (min_le_right _ _)
  have hsmall : ε / 3 + ε / 3 < ε := by linarith
  exact (dist_triangle (y.path.1 t) (x.path.1 (φ t)) (x.path.1 t)).trans_lt
    ((add_lt_add hyt hft).trans hsmall)




theorem j1WindowD_eval_zero_continuousAt {T : ℝ} (hT : 0 < T)
    (x : J1WindowD T hT) :
    ContinuousAt
      (fun y : J1WindowD T hT => y.path.1 ⟨0, ⟨le_rfl, hT.le⟩⟩) x := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro y hy
  have hbound :
      |y.path.1 ⟨0, ⟨le_rfl, hT.le⟩⟩ - x.path.1 ⟨0, ⟨le_rfl, hT.le⟩⟩|
        ≤ dist y x := by
    change |y.path.1 ⟨0, ⟨le_rfl, hT.le⟩⟩ - x.path.1 ⟨0, ⟨le_rfl, hT.le⟩⟩|
      ≤ j1WindowDist hT y.path x.path
    exact j1WindowDist_eval_zero_le hT y.path x.path
  rw [Real.dist_eq]
  exact hbound.trans_lt hy




theorem j1WindowD_eval_endpoint_continuousAt {T : ℝ} (hT : 0 < T)
    (x : J1WindowD T hT) :
    ContinuousAt
      (fun y : J1WindowD T hT => y.path.1 ⟨T, ⟨hT.le, le_rfl⟩⟩) x := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro y hy
  have hbound :
      |y.path.1 ⟨T, ⟨hT.le, le_rfl⟩⟩ - x.path.1 ⟨T, ⟨hT.le, le_rfl⟩⟩|
        ≤ dist y x := by
    change |y.path.1 ⟨T, ⟨hT.le, le_rfl⟩⟩ - x.path.1 ⟨T, ⟨hT.le, le_rfl⟩⟩|
      ≤ j1WindowDist hT y.path x.path
    exact j1WindowDist_eval_endpoint_le hT y.path x.path
  rw [Real.dist_eq]
  exact hbound.trans_lt hy

end DirectedDistances.Probability
