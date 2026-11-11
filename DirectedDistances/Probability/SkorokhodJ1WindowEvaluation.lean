module

public import DirectedDistances.Probability.SkorokhodJ1WindowMetric

import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity









@[expose] public section
namespace DirectedDistances.Probability

private theorem j1WindowTimeChange_fixes_start {T : ℝ} (hT : 0 < T)
    (φ : J1TimeChange T) :
    φ ⟨0, ⟨le_rfl, hT.le⟩⟩ = ⟨0, ⟨le_rfl, hT.le⟩⟩ := by
  let z : J1Window T := ⟨0, ⟨le_rfl, hT.le⟩⟩
  apply Subtype.ext
  apply le_antisymm
  · obtain ⟨x, hx⟩ := φ.surjective z
    have hzx : z ≤ x := by
      change (0 : ℝ) ≤ (x : ℝ)
      exact x.property.1
    have hmono := φ.monotone hzx
    rw [hx] at hmono
    change (φ z : ℝ) ≤ (z : ℝ) at hmono
    simpa [z] using hmono
  · exact (φ z).property.1

private theorem j1WindowTimeChange_fixes_endpoint {T : ℝ} (hT : 0 < T)
    (φ : J1TimeChange T) :
    φ ⟨T, ⟨hT.le, le_rfl⟩⟩ = ⟨T, ⟨hT.le, le_rfl⟩⟩ := by
  apply Subtype.ext
  apply le_antisymm
  · exact (φ ⟨T, ⟨hT.le, le_rfl⟩⟩).property.2
  · obtain ⟨x, hx⟩ := φ.surjective ⟨T, ⟨hT.le, le_rfl⟩⟩
    have hxe : x ≤ (⟨T, ⟨hT.le, le_rfl⟩⟩ : J1Window T) := x.property.2
    have hmono := φ.monotone hxe
    rw [hx] at hmono
    exact hmono

private theorem j1Window_eval_dist_le {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T) (t : J1Window T)
    (hfix : ∀ φ : J1TimeChange T, φ t = t) :
    |f.1 t - g.1 t| ≤ j1WindowDist hT f g := by
  change |f.1 t - g.1 t| ≤ ⨅ φ : J1TimeChange T,
    max (⨆ s : J1Window T, |((φ s : ℝ) - (s : ℝ))|)
      (⨆ s : J1Window T, |f.1 (φ s) - g.1 s|)
  apply le_ciInf
  intro φ
  have hvalue : |f.1 t - g.1 t| ≤
      ⨆ s : J1Window T, |f.1 (φ s) - g.1 s| := by
    rw [← congrArg f.1 (hfix φ)]
    exact le_ciSup_of_le (j1WindowValueError_bddAbove f g φ) t le_rfl
  exact hvalue.trans (le_max_right _ _)

/-- Evaluation at zero is one-Lipschitz for the J1 window metric. -/
theorem j1WindowDist_eval_zero_le {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T) :
    |f.1 ⟨0, ⟨le_rfl, hT.le⟩⟩ - g.1 ⟨0, ⟨le_rfl, hT.le⟩⟩| ≤
      j1WindowDist hT f g := by
  apply j1Window_eval_dist_le hT f g _
  intro φ
  exact j1WindowTimeChange_fixes_start hT φ

/-- Evaluation at the right endpoint is one-Lipschitz for the J1 window metric.
This is the endpoint bound used for càdlàg paths, which may jump at `T`. -/
theorem j1WindowDist_eval_endpoint_le {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T) :
    |f.1 ⟨T, ⟨hT.le, le_rfl⟩⟩ - g.1 ⟨T, ⟨hT.le, le_rfl⟩⟩| ≤
      j1WindowDist hT f g := by
  apply j1Window_eval_dist_le hT f g _
  intro φ
  exact j1WindowTimeChange_fixes_endpoint hT φ

/-- The left endpoint evaluation is continuous in the J1 window topology. -/
private theorem j1Window_eval_lipschitz {T : ℝ} (hT : 0 < T)
    (t : J1Window T) (hfix : ∀ φ : J1TimeChange T, φ t = t) :
    @LipschitzWith (CadlagWindow T) ℝ
      (@PseudoMetricSpace.toPseudoEMetricSpace (CadlagWindow T)
        (j1WindowMetricSpace hT).toPseudoMetricSpace)
      inferInstance 1 (fun f => f.1 t) := by
  apply @LipschitzWith.of_dist_le_mul (CadlagWindow T) ℝ
    (j1WindowMetricSpace hT).toPseudoMetricSpace inferInstance 1 _
  intro f g
  have hfg : @dist (CadlagWindow T)
      (j1WindowMetricSpace hT).toPseudoMetricSpace.toDist f g =
        j1WindowDist hT f g := rfl
  rw [Real.dist_eq, hfg]
  simpa only [NNReal.coe_one, one_mul] using
    j1Window_eval_dist_le hT f g t hfix

theorem continuous_j1Window_eval_zero {T : ℝ} (hT : 0 < T) :
    @Continuous (CadlagWindow T) ℝ
      (j1WindowMetricSpace hT).toUniformSpace.toTopologicalSpace _
      (fun f => f.1 ⟨0, ⟨le_rfl, hT.le⟩⟩) := by
  exact @LipschitzWith.continuous (CadlagWindow T) ℝ
    (@PseudoMetricSpace.toPseudoEMetricSpace (CadlagWindow T)
      (j1WindowMetricSpace hT).toPseudoMetricSpace)
    inferInstance 1 _
    (j1Window_eval_lipschitz hT _ fun φ => j1WindowTimeChange_fixes_start hT φ)

/-- The right endpoint evaluation is continuous, including paths that jump at `T`. -/
theorem continuous_j1Window_eval_endpoint {T : ℝ} (hT : 0 < T) :
    @Continuous (CadlagWindow T) ℝ
      (j1WindowMetricSpace hT).toUniformSpace.toTopologicalSpace _
      (fun f => f.1 ⟨T, ⟨hT.le, le_rfl⟩⟩) := by
  exact @LipschitzWith.continuous (CadlagWindow T) ℝ
    (@PseudoMetricSpace.toPseudoEMetricSpace (CadlagWindow T)
      (j1WindowMetricSpace hT).toPseudoMetricSpace)
    inferInstance 1 _
    (j1Window_eval_lipschitz hT _ fun φ =>
      j1WindowTimeChange_fixes_endpoint hT φ)

private theorem j1WindowDist_lt_exists_timeChange {T : ℝ} (hT : 0 < T)
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

/-- Evaluation is continuous at a path whenever that path is continuous at the
chosen time. -/
theorem j1Window_eval_continuousAt {T : ℝ} (hT : 0 < T)
    (f : CadlagWindow T) (t : J1Window T)
    (hf : ContinuousAt f.1 t) :
    @ContinuousAt (CadlagWindow T) ℝ
      (j1WindowMetricSpace hT).toUniformSpace.toTopologicalSpace _
      (fun g => g.1 t) f := by
  rw [@Metric.continuousAt_iff (CadlagWindow T) ℝ
    (j1WindowMetricSpace hT).toPseudoMetricSpace inferInstance]
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨r, hr, hfr⟩ := (Metric.continuousAt_iff.mp hf) (ε / 3) hthird
  refine ⟨min r (ε / 3), lt_min hr hthird, ?_⟩
  intro g hdist
  have hdist' : j1WindowDist hT f g < min r (ε / 3) := by
    change j1WindowDist hT g f < min r (ε / 3) at hdist
    rw [j1WindowDist_symm hT]
    exact hdist
  obtain ⟨φ, hdisp, hvalue⟩ :=
    j1WindowDist_lt_exists_timeChange hT f g _ hdist'
  have hφt : dist (φ t) t < r := by
    rw [Subtype.dist_eq, Real.dist_eq]
    exact (hdisp t).trans_le (min_le_left _ _)
  have hft : dist (f.1 (φ t)) (f.1 t) < ε / 3 := hfr hφt
  have hgt : dist (g.1 t) (f.1 (φ t)) < ε / 3 := by
    simpa [Real.dist_eq, abs_sub_comm] using
      (hvalue t).trans_le (min_le_right _ _)
  have hsmall : ε / 3 + ε / 3 < ε := by linarith
  exact (dist_triangle (g.1 t) (f.1 (φ t)) (f.1 t)).trans_lt
    ((add_lt_add hgt hft).trans hsmall)

end DirectedDistances.Probability
