module

public import DirectedDistances.Probability.SkorokhodJ1LocalLawCriterionFinal
public import DirectedDistances.Probability.ProductLawConvergence

public section
namespace DirectedDistances.Probability

open Filter MeasureTheory Metric TopologicalSpace
open scoped Topology

/-- Helper toward Theorem 1.6; not a paper result.
The local J1 space is separable by finite cutoff approximation; -/
instance : SeparableSpace CadlagLocal := by
  classical
  have himage (N : ℕ) : IsSeparable (Set.range (finiteCutoffWindows N)) := by
    exact IsSeparable.of_separableSpace (Set.range (finiteCutoffWindows N))
  have hdense (N : ℕ) :
      ∃ t : Set (LocalCutoffTuple N),
        t ⊆ Set.range (finiteCutoffWindows N) ∧ t.Countable ∧
          Set.range (finiteCutoffWindows N) ⊆ closure t := by
    exact (himage N).exists_countable_dense_subset
  choose t htSub htCount htDense using hdense
  let pre : (N : ℕ) → {y : LocalCutoffTuple N // y ∈ t N} → CadlagLocal :=
    fun N y => Classical.choose (htSub N y.property)
  have hpre (N : ℕ) (y : {z : LocalCutoffTuple N // z ∈ t N}) :
      finiteCutoffWindows N (pre N y) = y.val :=
    Classical.choose_spec (htSub N y.property)
  let s : Set CadlagLocal := ⋃ N, Set.range (pre N)
  have hsCount : s.Countable := by
    change (⋃ N, Set.range (pre N)).Countable
    exact Set.countable_iUnion fun N => by
      have : Countable {y : LocalCutoffTuple N // y ∈ t N} :=
        (htCount N).to_subtype
      exact Set.countable_range (pre N)
  refine ⟨⟨s, hsCount, ?_⟩⟩
  rw [Metric.dense_iff]
  intro x r hr
  have htail : ∀ᶠ N : ℕ in atTop, localJ1TailBound N < r / 2 :=
    (tendsto_order.1 tendsto_localJ1TailBound).2 (r / 2) (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 htail
  have hNtail : localJ1TailBound N < r / 2 := hN N le_rfl
  have hxImage : finiteCutoffWindows N x ∈ Set.range (finiteCutoffWindows N) :=
    Set.mem_range_self _
  obtain ⟨z, hz, hdist⟩ :=
    Metric.mem_closure_iff.1 (htDense N hxImage) (r / 2) (by linarith)
  let y : {w : LocalCutoffTuple N // w ∈ t N} := ⟨z, hz⟩
  let x' := pre N y
  have hdist' : dist x x' < r := by
    calc
      dist x x' ≤ finiteCutoffWindowTruncDist
          (finiteCutoffWindows N x) (finiteCutoffWindows N x') + localJ1TailBound N :=
        dist_le_finiteCutoffWindowTruncDist_add_bound N x x'
      _ ≤ dist (finiteCutoffWindows N x) (finiteCutoffWindows N x') +
          localJ1TailBound N :=
        by gcongr; exact finiteCutoffWindowTruncDist_le_dist _ _
      _ < r := by rw [hpre]; linarith
  refine ⟨x', ?_, ?_⟩
  · simpa only [Metric.mem_ball, dist_comm] using hdist'
  · change pre N y ∈ ⋃ n, Set.range (pre n)
    exact Set.mem_iUnion.2 ⟨N, Set.mem_range_self y⟩

/-- Helper toward Theorem 1.6; not a paper result.
The local J1 metric topology is second countable; -/
instance cadlagLocalSecondCountableTopology : SecondCountableTopology CadlagLocal := by
  let : UniformSpace CadlagLocal := j1LocalMetricSpace.toUniformSpace
  exact UniformSpace.secondCountable_of_separable CadlagLocal

/-- Helper toward Theorem 1.6; not a paper result.
Convergence of two local J1 marginals implies convergence of their product laws; -/
theorem tendsto_probabilityProduct_cadlagLocal
    {μn νn : ℕ → ProbabilityMeasure CadlagLocal}
    {μ ν : ProbabilityMeasure CadlagLocal}
    (hμ : Tendsto μn atTop (𝓝 μ)) (hν : Tendsto νn atTop (𝓝 ν)) :
    Tendsto (fun n => probabilityProduct (μn n) (νn n)) atTop
      (𝓝 (probabilityProduct μ ν)) := by
  exact tendsto_prod_of_tendsto hμ hν

end DirectedDistances.Probability
