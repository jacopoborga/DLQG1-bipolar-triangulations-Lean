/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.D39SourceTopologyMetric
public import DirectedDistances.PaperProofs.Section3.BSTopologyGenericMetrizable
public import DirectedDistances.PaperProofs.Section5.Prop516D39Transport
public import DirectedDistances.PlanarMap.D39RootedPlanarBallGenusZero
public import DirectedDistances.PaperProofs.Section5.Prop516RootedLawConvergence

/-! Supporting lemmas for paper labels `prop-disk-bs-conv` (see CORRESPONDENCE.md). -/

/-! # Class-distance topology and Proposition 5.16 transport

Helpers toward Definition 3.8 and Proposition 5.16. Sources: -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open DirectedDistances.Probability
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

/-- Helper toward Definition 3.8 and Proposition 5.16 (prop-disk-bs-conv).
The descended rooted-ball distance gives the quotient of planar rooted maps a
pseudo extended metric. -/
@[expose, instance_reducible, instance] noncomputable def
    d39PlanarRootedMapClass_pseudoEMetricSpace :
    PseudoEMetricSpace (Quotient D39PlanarRootedMap.setoid) :=
  PseudoEMetricSpace.ofEDist
    d39PlanarRootedMapClassDistance
    d39PlanarRootedMapClassDistance_self
    d39PlanarRootedMapClassDistance_symm
    (by
      intro M N P
      exact (d39PlanarRootedMapClassDistance_ultrametric M N P).trans
        (max_le_iff.mpr ⟨le_add_right le_rfl, le_add_left le_rfl⟩))

/-- Helper toward Definition 3.8 and Proposition 5.16 (prop-disk-bs-conv).
Separation of the class distance strengthens the pseudo extended metric to an
extended metric. -/
@[expose, instance_reducible, instance] noncomputable def
    d39PlanarRootedMapClass_emetricSpace :
    EMetricSpace (Quotient D39PlanarRootedMap.setoid) where
  toPseudoEMetricSpace := d39PlanarRootedMapClass_pseudoEMetricSpace
  eq_of_edist_eq_zero := by
    intro M N h
    exact (d39PlanarRootedMapClassDistance_eq_zero_iff M N).mp h

/-- Helper toward Definition 3.8 and Proposition 5.16 (prop-disk-bs-conv). The
topology on the quotient is the topology induced by its extended metric. -/
@[expose, instance_reducible, instance] noncomputable def
    d39PlanarRootedMapClass_topologicalSpace :
    TopologicalSpace D39PlanarRootedMapClass :=
  d39PlanarRootedMapClass_emetricSpace.toPseudoEMetricSpace.toUniformSpace.toTopologicalSpace

/-- Helper toward Definition 3.8. The class distance between two locally
finite planar maps is bounded by their generic faced-ball distance, since
equality of faced balls transports to equality of local topology balls. -/
theorem d39PlanarRootedMapClassDistance_le_facedDistance
    (M N : RootedLocallyFinitePlanarMap) :
    d39PlanarRootedMapClassDistance
        (Quotient.mk D39PlanarRootedMap.setoid M.toD39PlanarRootedMap)
        (Quotient.mk D39PlanarRootedMap.setoid N.toD39PlanarRootedMap) ≤
      bsLocalDistanceGeneric rootedLocallyFiniteFacedBallSystem M N := by
  rw [d39PlanarRootedMapClassDistance_mk_mk_eq_source_formula]
  unfold bsLocalDistanceGeneric
  apply le_iInf
  intro r
  apply le_iInf
  intro hface
  have hd39 :
      d39BallClass M.toD39PlanarRootedMap.toD39RootedMap
          (r + 1) (Nat.succ_pos r) =
        d39BallClass N.toD39PlanarRootedMap.toD39RootedMap
          (r + 1) (Nat.succ_pos r) := by
    rw [d39PlanarRootedMap_ballClass_eq_facedFramedBallClassToD39BallClass M r,
      d39PlanarRootedMap_ballClass_eq_facedFramedBallClassToD39BallClass N r]
    exact congrArg facedFramedBallClassToD39BallClass (by
      change rootedLocallyFiniteFacedBallClass r M =
        rootedLocallyFiniteFacedBallClass r N at hface
      exact hface)
  exact iInf_le_of_le r (iInf_le_of_le hd39 le_rfl)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv). The class map is
1-Lipschitz from the generic faced-ball distance. -/
theorem d39PlanarRootedMapClassMap_lipschitz :
    letI : PseudoEMetricSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistancePseudoEMetricSpaceGeneric rootedLocallyFiniteFacedBallSystem
    LipschitzWith 1 (fun M : RootedLocallyFinitePlanarMap =>
      Quotient.mk D39PlanarRootedMap.setoid M.toD39PlanarRootedMap) := by
  letI : PseudoEMetricSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistancePseudoEMetricSpaceGeneric rootedLocallyFiniteFacedBallSystem
  intro M N
  change d39PlanarRootedMapClassDistance
      (Quotient.mk D39PlanarRootedMap.setoid M.toD39PlanarRootedMap)
      (Quotient.mk D39PlanarRootedMap.setoid N.toD39PlanarRootedMap) ≤
    (1 : ℝ≥0∞) * bsLocalDistanceGeneric rootedLocallyFiniteFacedBallSystem M N
  rw [one_mul]
  exact d39PlanarRootedMapClassDistance_le_facedDistance M N

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv). The class map from
locally finite planar maps is continuous for the generic faced-ball topology. -/
theorem continuous_d39PlanarRootedMapClassMap :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    Continuous (fun M : RootedLocallyFinitePlanarMap =>
      Quotient.mk D39PlanarRootedMap.setoid M.toD39PlanarRootedMap) := by
  letI : PseudoEMetricSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistancePseudoEMetricSpaceGeneric rootedLocallyFiniteFacedBallSystem
  change @Continuous RootedLocallyFinitePlanarMap D39PlanarRootedMapClass
    (bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem) _ _
  rw [bsLocalDistanceTopology_eq_pseudoEMetricTopologyGeneric
    rootedLocallyFiniteFacedBallSystem]
  exact d39PlanarRootedMapClassMap_lipschitz.continuous

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv). Equip the quotient
class with the Borel measurable structure generated by its class-distance
topology. -/
@[expose, instance_reducible, instance] noncomputable def
    d39PlanarRootedMapClass_measurableSpace :
    MeasurableSpace (Quotient D39PlanarRootedMap.setoid) :=
      borel (Quotient D39PlanarRootedMap.setoid)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv). The quotient class is
a Borel space for its class-distance topology. -/
@[instance] theorem
    d39PlanarRootedMapClass_borelSpace :
    BorelSpace (Quotient D39PlanarRootedMap.setoid) := ⟨rfl⟩




theorem diskRootedPlanarMapLaw_d39Class_tendsto_uibhbot
    (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ)) :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    letI : TopologicalSpace D39PlanarRootedMapClass := inferInstance
    letI : MeasurableSpace D39PlanarRootedMapClass :=
      borel D39PlanarRootedMapClass
    letI : BorelSpace D39PlanarRootedMapClass := ⟨rfl⟩
    Tendsto (fun k =>
      (diskRootedPlanarMapLaw (k + 1) (ell k)
        (hadm k).1 (hadm k).2.1 (hadm k).2.2).map
          (fun M : RootedLocallyFinitePlanarMap =>
            Quotient.mk D39PlanarRootedMap.setoid M.toD39PlanarRootedMap))
      atTop
      (𝓝 ((uibhbotRootedPlanarMapLaw).map
        (fun M : RootedLocallyFinitePlanarMap =>
          Quotient.mk D39PlanarRootedMap.setoid M.toD39PlanarRootedMap))) := by
  letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  letI : TopologicalSpace D39PlanarRootedMapClass := inferInstance
  letI : MeasurableSpace D39PlanarRootedMapClass :=
    borel D39PlanarRootedMapClass
  letI : BorelSpace D39PlanarRootedMapClass := ⟨rfl⟩
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun k => diskRootedPlanarMapLaw (k + 1) (ell k)
      (hadm k).1 (hadm k).2.1 (hadm k).2.2)
    uibhbotRootedPlanarMapLaw
    (diskRootedPlanarMapLaw_tendsto_uibhbot A hA ell hadm hlo hhi)
    continuous_d39PlanarRootedMapClassMap

end DirectedDistances.PaperProofs.Section5
