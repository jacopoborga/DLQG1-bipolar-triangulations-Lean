module

public import DirectedDistances.Probability.SkorokhodJ1WindowEvaluation
public import DirectedDistances.Probability.SkorokhodJ1WindowPolish
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable






@[expose] public section
namespace DirectedDistances.Probability




theorem continuous_j1WindowD_eval_zero {T : ℝ} (hT : 0 < T) :
    Continuous (fun x : J1WindowD T hT =>
      x.path.1 ⟨0, ⟨le_rfl, hT.le⟩⟩) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  refine ⟨ε, hε, ?_⟩
  intro y hy
  change j1WindowDist hT y.path x.path < ε at hy
  simpa only [Real.dist_eq] using
    (j1WindowDist_eval_zero_le hT y.path x.path).trans_lt hy




theorem continuous_j1WindowD_eval_endpoint {T : ℝ} (hT : 0 < T) :
    Continuous (fun x : J1WindowD T hT =>
      x.path.1 ⟨T, ⟨hT.le, le_rfl⟩⟩) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  refine ⟨ε, hε, ?_⟩
  intro y hy
  change j1WindowDist hT y.path x.path < ε at hy
  simpa only [Real.dist_eq] using
    (j1WindowDist_eval_endpoint_le hT y.path x.path).trans_lt hy




theorem j1WindowD_path_norm_bddAbove {T : ℝ} (hT : 0 < T)
    (x : J1WindowD T hT) :
    BddAbove (Set.range fun t : J1Window T => |x.path.1 t|) := by
  have hcompact : IsCompact (Set.univ : Set (J1Window T)) :=
    isCompact_iff_isCompact_univ.mp isCompact_Icc
  have hbounded := isBounded_image_of_isCadlag_of_isCompact x.path.2 hcompact
  obtain ⟨C, hC⟩ :=
    (Metric.isBounded_iff_subset_closedBall 0).mp hbounded
  refine ⟨C, ?_⟩
  rintro _ ⟨t, rfl⟩
  have ht : x.path.1 t ∈ Metric.closedBall 0 C :=
    hC ⟨t, Set.mem_univ t, rfl⟩
  simpa [Metric.mem_closedBall, Real.dist_eq] using ht





theorem measurable_j1WindowD_eval_zero {T : ℝ} (hT : 0 < T)
    [MeasurableSpace (J1WindowD T hT)] [BorelSpace (J1WindowD T hT)] :
    Measurable (fun x : J1WindowD T hT =>
      x.path.1 ⟨0, ⟨le_rfl, hT.le⟩⟩) := by
  exact (continuous_j1WindowD_eval_zero hT).measurable





theorem measurable_j1WindowD_eval_endpoint {T : ℝ} (hT : 0 < T)
    [MeasurableSpace (J1WindowD T hT)] [BorelSpace (J1WindowD T hT)] :
    Measurable (fun x : J1WindowD T hT =>
      x.path.1 ⟨T, ⟨hT.le, le_rfl⟩⟩) := by
  exact (continuous_j1WindowD_eval_endpoint hT).measurable

end DirectedDistances.Probability
