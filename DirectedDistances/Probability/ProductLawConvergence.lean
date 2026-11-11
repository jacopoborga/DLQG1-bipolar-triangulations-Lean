module

public import Mathlib.MeasureTheory.Measure.Portmanteau

public section
namespace DirectedDistances.Probability

open Filter MeasureTheory Metric Set Topology TopologicalSpace

/-- Helper toward Theorem 1.6; not a paper result.
The product probability measure defined using the measure product; -/
@[expose] noncomputable def probabilityProduct {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    ProbabilityMeasure (X × Y) :=
  ⟨(μ : Measure X).prod (ν : Measure Y), inferInstance⟩

/-- Helper toward Theorem 1.6; not a paper result.
Convergence of both marginals implies convergence of their product laws; -/
theorem tendsto_prod_of_tendsto
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    {μn : ℕ → ProbabilityMeasure X} {νn : ℕ → ProbabilityMeasure Y}
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (hμ : Tendsto μn atTop (𝓝 μ)) (hν : Tendsto νn atTop (𝓝 ν)) :
    Tendsto (fun n => probabilityProduct (μn n) (νn n)) atTop
      (𝓝 (probabilityProduct μ ν)) := by
  let S : Set (Set (X × Y)) := {t | ∃ a b, MeasurableSet a ∧ μ (frontier a) = 0 ∧
    MeasurableSet b ∧ ν (frontier b) = 0 ∧ t = a ×ˢ b}
  have hS : IsPiSystem S := by
    rintro _ ⟨a, b, ha, hμa, hb, hνb, rfl⟩ _ ⟨a', b', ha', hμa', hb', hνb', rfl⟩ _
    refine ⟨a ∩ a', b ∩ b', ha.inter ha', ?_, hb.inter hb', ?_, prod_inter_prod⟩
    · rw [ProbabilityMeasure.null_iff_toMeasure_null] at hμa hμa' ⊢
      exact null_frontier_inter hμa hμa'
    · rw [ProbabilityMeasure.null_iff_toMeasure_null] at hνb hνb' ⊢
      exact null_frontier_inter hνb hνb'
  apply hS.tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro s ⟨a, b, ha, -, hb, -, rfl⟩
    exact ha.prod hb
  · let _ : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
    let _ : PseudoMetricSpace Y := TopologicalSpace.pseudoMetrizableSpacePseudoMetric Y
    intro u hu x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu x hx
    rcases exists_null_frontier_thickening (μ : Measure X) {x.1} hε with
      ⟨r, hr, hμr⟩
    rcases exists_null_frontier_thickening (ν : Measure Y) {x.2} hε with
      ⟨r', hr', hνr'⟩
    simp only [thickening_singleton] at hμr hνr'
    refine ⟨ball x.1 r ×ˢ ball x.2 r', ?_, ?_, ?_⟩
    · refine ⟨ball x.1 r, ball x.2 r', measurableSet_ball, ?_,
        measurableSet_ball, ?_, rfl⟩
      · exact (ProbabilityMeasure.null_iff_toMeasure_null μ _).2 hμr
      · exact (ProbabilityMeasure.null_iff_toMeasure_null ν _).2 hνr'
    · exact (isOpen_ball.prod isOpen_ball).mem_nhds (by simp [hr.1, hr'.1])
    · calc
        ball x.1 r ×ˢ ball x.2 r' ⊆ ball x.1 ε ×ˢ ball x.2 ε := by
          gcongr
          · exact hr.2.le
          · exact hr'.2.le
        _ ⊆ u := by rwa [ball_prod_same]
  · rintro s ⟨a, b, ha, hμa, hb, hνb, rfl⟩
    have hμa' : Tendsto (fun n => μn n a) atTop (𝓝 (μ a)) :=
      ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hμ hμa
    have hνb' : Tendsto (fun n => νn n b) atTop (𝓝 (ν b)) :=
      ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hν hνb
    simpa [probabilityProduct, ProbabilityMeasure.coeFn_def] using hμa'.mul hνb'

end DirectedDistances.Probability
