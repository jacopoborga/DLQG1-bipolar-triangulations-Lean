module

public import DirectedDistances.PaperProofs.Section5.Prop516RootedLawConvergence
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Helpers toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not paper results. -/

public section
namespace DirectedDistances.Probability

open Filter MeasureTheory TopologicalSpace
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open DirectedDistances.PlanarMap
open scoped Topology

noncomputable section

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The helper faced-ball topology used by the conditional law statement. Source: -/
local instance rootedPlanarMapLawTopology : TopologicalSpace RootedLocallyFinitePlanarMap :=
  bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The Borel measurable structure paired with the helper faced-ball topology. Source: -/
local instance rootedPlanarMapLawMeasurableSpace :
    MeasurableSpace RootedLocallyFinitePlanarMap := borel RootedLocallyFinitePlanarMap

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
The helper faced-ball topology with its Borel measurable structure. Source: -/
local instance rootedPlanarMapLawBorelSpace : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
If a convergent sequence of laws is invariant under a continuous map, its limit law -/
theorem map_eq_of_tendsto_of_map_eq
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {m : X → X} (hm : Continuous m)
    (hT2 : T2Space (ProbabilityMeasure X))
    {μs : ℕ → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hlim : Tendsto μs atTop (𝓝 μ))
    (hinv : ∀ n, (μs n).map m = μs n) :
    μ.map m = μ := by
  have hpush : Tendsto (fun n => (μs n).map m) atTop (𝓝 (μ.map m)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μs μ hlim hm
  have hlim' : Tendsto μs atTop (𝓝 (μ.map m)) :=
    Tendsto.congr' (Filter.Eventually.of_forall hinv) hpush
  exact @tendsto_nhds_unique (ProbabilityMeasure X) _ hT2
    (Y := ℕ) (f := μs) (l := atTop) (a := μ.map m) (b := μ)
    (inferInstance : NeBot (atTop : Filter ℕ)) hlim' hlim

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Eventual invariance of a convergent sequence also passes to its limit. Source: -/
theorem map_eq_of_tendsto_of_eventually_map_eq
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {m : X → X} (hm : Continuous m)
    (hT2 : T2Space (ProbabilityMeasure X))
    {μs : ℕ → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hlim : Tendsto μs atTop (𝓝 μ))
    (hinv : ∀ᶠ n in atTop, (μs n).map m = μs n) :
    μ.map m = μ := by
  have hpush : Tendsto (fun n => (μs n).map m) atTop (𝓝 (μ.map m)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μs μ hlim hm
  have hlim' : Tendsto μs atTop (𝓝 (μ.map m)) :=
    Tendsto.congr' hinv hpush
  exact @tendsto_nhds_unique (ProbabilityMeasure X) _ hT2
    (Y := ℕ) (f := μs) (l := atTop) (a := μ.map m) (b := μ)
    (inferInstance : NeBot (atTop : Filter ℕ)) hlim' hlim

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
Under `HasOuterApproxClosed` for the helper faced-ball topology, invariance of every
finite disk law passes to the UIBHBOT law. That topological property is an explicit
conditional premise because no instance is present for this topology. Source: -/
theorem uibhbotRootedPlanarMapLaw_map_eq_of_disk_map_eq
    (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ))
    (hclosed : @HasOuterApproxClosed RootedLocallyFinitePlanarMap
      rootedPlanarMapLawTopology)
    (m : RootedLocallyFinitePlanarMap → RootedLocallyFinitePlanarMap)
    (hm : Continuous m)
    (hinv : ∀ k,
      (diskRootedPlanarMapLaw (k + 1) (ell k)
        (hadm k).1 (hadm k).2.1 (hadm k).2.2).map m =
        diskRootedPlanarMapLaw (k + 1) (ell k)
          (hadm k).1 (hadm k).2.1 (hadm k).2.2) :
    (uibhbotRootedPlanarMapLaw : ProbabilityMeasure RootedLocallyFinitePlanarMap).map
      m = uibhbotRootedPlanarMapLaw := by
  have hT2 : T2Space (ProbabilityMeasure RootedLocallyFinitePlanarMap) :=
    @ProbabilityMeasure.t2Space RootedLocallyFinitePlanarMap _ _ hclosed _
  apply map_eq_of_tendsto_of_map_eq hm hT2
  · exact diskRootedPlanarMapLaw_tendsto_uibhbot A hA ell hadm hlo hhi
  · exact hinv

end
end DirectedDistances.Probability
