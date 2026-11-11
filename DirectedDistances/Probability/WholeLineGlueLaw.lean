module

public import DirectedDistances.Probability.SkorokhodJ1GlueContinuity
public import DirectedDistances.Probability.CadlagLocalSeparable
import Mathlib.Topology.Sequences

/-! # Probability laws of left-limit whole-line gluing

The half-path laws below live on the zero-at-zero subspace, so the origin conditions
hold for every path in their carrier. -/

public section
namespace DirectedDistances.Probability

open Filter MeasureTheory TopologicalSpace
open scoped Topology

/-- Helper toward Theorem 1.6; not a paper result. -/
@[instance_reducible] noncomputable instance wholeLineLocalMetricSpace :
    MetricSpace WholeLineCadlag where
  dist := wholeLineLocalJ1Distance
  dist_self := wholeLineLocalJ1Distance_self
  dist_comm := wholeLineLocalJ1Distance_symm
  dist_triangle := wholeLineLocalJ1Distance_triangle
  eq_of_dist_eq_zero := fun h => (wholeLineLocalJ1Distance_eq_zero_iff _ _).mp h

/-- Helper toward Theorem 1.6; not a paper result. -/
@[instance_reducible] noncomputable instance wholeLineLocalTopologicalSpace :
    TopologicalSpace WholeLineCadlag :=
  wholeLineLocalMetricSpace.toUniformSpace.toTopologicalSpace

/-- Helper toward Theorem 1.6; not a paper result. -/
@[instance_reducible] noncomputable instance wholeLineLocalMeasurableSpace :
    MeasurableSpace WholeLineCadlag := borel WholeLineCadlag

/-- Helper toward Theorem 1.6; not a paper result. -/
instance wholeLineLocalBorelSpace : BorelSpace WholeLineCadlag := ⟨rfl⟩

/-- Helper toward Theorem 1.6; not a paper result. -/
abbrev CadlagLocalZero := {x : CadlagLocal // x.1 ⟨0, le_rfl⟩ = 0}

/-- Helper toward Theorem 1.6; not a paper result.
The second coordinate supplies the independent negative half when the input law is a product. -/
@[expose] noncomputable def wholeLineGlueZero
    (p : CadlagLocalZero × CadlagLocalZero) : WholeLineCadlag :=
  wholeLineGlueCadlag p.1.val p.2.val p.1.property p.2.property

/-- Helper toward Theorem 1.6; not a paper result. -/
theorem continuous_wholeLineGlueZero : Continuous wholeLineGlueZero := by
  apply continuous_iff_seqContinuous.mpr
  intro p q hp
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hx : Tendsto (fun k => (p k).1.val) atTop (𝓝 q.1.val) :=
    (continuous_subtype_val.tendsto q.1).comp ((continuous_fst.tendsto q).comp hp)
  have hy : Tendsto (fun k => (p k).2.val) atTop (𝓝 q.2.val) :=
    (continuous_subtype_val.tendsto q.2).comp ((continuous_snd.tendsto q).comp hp)
  exact wholeLineGlue_tendsto_of_local_tendsto
    (fun k => (p k).1.val) (fun k => (p k).2.val) q.1.val q.2.val
    (fun k => (p k).1.property) (fun k => (p k).2.property)
    q.1.property q.2.property
    (tendsto_iff_dist_tendsto_zero.mp hx) (tendsto_iff_dist_tendsto_zero.mp hy)

/-- Helper toward Theorem 1.6; not a paper result. -/
instance cadlagLocalZeroSecondCountableTopology : SecondCountableTopology CadlagLocalZero := by
  let : UniformSpace CadlagLocal :=
    TopologicalSpace.pseudoMetrizableSpaceUniformity CadlagLocal
  have : (uniformity CadlagLocal).IsCountablyGenerated :=
    TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated CadlagLocal
  have : SecondCountableTopology CadlagLocal :=
    UniformSpace.secondCountable_of_separable CadlagLocal
  infer_instance

/-- Helper toward Theorem 1.6; not a paper result. -/
theorem measurable_wholeLineGlueZero : Measurable wholeLineGlueZero :=
  continuous_wholeLineGlueZero.measurable

/-- Helper toward Theorem 1.6; not a paper result.
Convergent independent zero-at-zero half-path laws give convergent glued whole-line laws; -/
theorem tendsto_probabilityProduct_map_wholeLineGlueZero
    {μn νn : ℕ → ProbabilityMeasure CadlagLocalZero}
    {μ ν : ProbabilityMeasure CadlagLocalZero}
    (hμ : Tendsto μn atTop (𝓝 μ)) (hν : Tendsto νn atTop (𝓝 ν)) :
    Tendsto (fun n => (probabilityProduct (μn n) (νn n)).map wholeLineGlueZero) atTop
      (𝓝 ((probabilityProduct μ ν).map wholeLineGlueZero)) := by
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_prod_of_tendsto hμ hν) continuous_wholeLineGlueZero

end DirectedDistances.Probability
