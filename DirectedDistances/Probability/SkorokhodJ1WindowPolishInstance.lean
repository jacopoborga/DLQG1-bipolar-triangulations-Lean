module

public import DirectedDistances.Probability.SkorokhodJ1WindowSeparableSpace
public import DirectedDistances.Probability.SkorokhodJ1WindowBorel
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section
namespace DirectedDistances.Probability

open MeasureTheory TopologicalSpace

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
Rational step paths give a countable dense family in the J1 window -/
theorem j1WindowD_exists_countable_dense_rational_steps {T : ℝ}
    (hT : 0 < T) :
    ∃ S : Set (J1WindowD T hT), S.Countable ∧ Dense S :=
  exists_countable_dense_j1WindowD hT

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem j1WindowD_separable {T : ℝ} (hT : 0 < T) :
    TopologicalSpace.SeparableSpace (J1WindowD T hT) :=
  inferInstance

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem j1WindowD_secondCountable {T : ℝ} (hT : 0 < T) :
    SecondCountableTopology (J1WindowD T hT) :=
  inferInstance

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The J1 window is completely metrizable by transport from the complete -/
theorem j1WindowD_completelyMetrizable {T : ℝ} (hT : 0 < T) :
    IsCompletelyMetrizableSpace (J1WindowD T hT) :=
  inferInstance

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result. -/
theorem j1WindowD_polish {T : ℝ} (hT : 0 < T) :
    PolishSpace (J1WindowD T hT) :=
  inferInstance

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The measurable space on the J1 window is its Borel σ-algebra -/
theorem j1WindowD_measurableSpace_eq_borel {T : ℝ} (hT : 0 < T) :
    (inferInstance : MeasurableSpace (J1WindowD T hT)) = borel (J1WindowD T hT) :=
  rfl

/-- Helper toward Theorem 1.6 (thm-busemann-conv); not a paper result.
The J1 window with its Borel σ-algebra is standard Borel -/
theorem j1WindowD_standardBorel {T : ℝ} (hT : 0 < T) :
    StandardBorelSpace (J1WindowD T hT) :=
  inferInstance

end DirectedDistances.Probability
