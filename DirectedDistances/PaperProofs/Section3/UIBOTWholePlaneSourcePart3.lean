/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTWholePlaneSourcePart2
public import DirectedDistances.PaperProofs.Section3.UIBOTFiniteSourceCarrier

/- # Actual-edge finite source laws and the whole-plane limit

The finite source law below uses the separately proved finite source carrier
and samples individual edges, including boundary and parallel edges. The
finite-law identification is proved, rather than supplied as a premise.
All convergence here is in the installed geometric class topology. Transport
to the source topology, item 3 of `UIBOTLocalLimitFinal`, remains separate. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open MeasureTheory Filter
open scoped Topology ENNReal

local instance uibotWholePlaneSourcePart3GeomMeasurable :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance uibotWholePlaneSourcePart3GeomBorel :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩
local instance uibotWholePlaneSourcePart3EdgeMeasurable (ℓ ρ n : ℕ) :
    MeasurableSpace (UIBOTFiniteSourceEdgeSample ℓ ρ n) := ⊤

/-- Helper toward Proposition 3.9: the finite source class law obtained
from uniform counting on map classes with one actual edge selected. Its
probability normalization follows from the proved finite-carrier law identity. -/
@[expose] def uibotFiniteSourceEdgeProbabilityLaw
    (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hne : Nonempty (KMSWMapIsoClass ℓ ρ n)) :
    ProbabilityMeasure D39GeomRootedMapClass.{0} := by
  letI uibotWholePlaneSourcePart3EdgeFintype :=
    uibotFiniteSourceEdgeSampleFintype ℓ ρ n hn
  refine ⟨(uniformCountingMeasure (UIBOTFiniteSourceEdgeSample ℓ ρ n)).map
    (uibotFiniteSourceEdgeGeometricClassMap ℓ ρ n hℓ hρ hn hne), ?_⟩
  rw [← uibotFiniteUniformSampleLaw_geometric_eq_source_edge ℓ ρ n hℓ hρ hn hne]
  exact (uibotFiniteGeometricProbabilityLaw ℓ ρ n hℓ hρ hn hne).property

/-- Helper toward Proposition 3.9: the actual-edge source probability
law equals the geometric approximant, with no finite-law identification premise. -/
theorem uibotFiniteSourceEdgeProbabilityLaw_eq_geometric
    (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hne : Nonempty (KMSWMapIsoClass ℓ ρ n)) :
    uibotFiniteSourceEdgeProbabilityLaw ℓ ρ n hℓ hρ hn hne =
      uibotFiniteGeometricProbabilityLaw ℓ ρ n hℓ hρ hn hne := by
  apply ProbabilityMeasure.toMeasure_injective
  exact (uibotFiniteUniformSampleLaw_geometric_eq_source_edge ℓ ρ n hℓ hρ hn hne).symm

/-- Helper toward Proposition 3.9: the actual-edge finite source laws
converge to the iid KMSW geometric law for every diverging admissible size
sequence and every fixed pair of positive boundary lengths. -/
theorem uibotFiniteSourceEdgeProbabilityLaw_tendsto
    (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (hsize : ∀ k, 1 ≤ ns k)
    (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k))) :
    Tendsto (fun k => uibotFiniteSourceEdgeProbabilityLaw ℓ ρ (ns k)
      hℓ hρ (hsize k) (hne k)) atTop
      (𝓝 (uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved)) := by
  simp only [uibotFiniteSourceEdgeProbabilityLaw_eq_geometric]
  exact uibotFiniteGeometricProbabilityLaw_tendsto ℓ ρ hℓ hρ ns hns hsize hne

/-- Helper toward Proposition 3.9: any local limit of the actual-edge
source laws in the geometric class topology has exactly the iid KMSW law.
The remaining limit premise is the source's defining limit after topology
transport; neither a finite-law premise nor a conclusion-equivalent input occurs. -/
theorem uibotFiniteSourceEdgeLocalLimit_eq_iidLaw
    (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (hsize : ∀ k, 1 ≤ ns k)
    (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k)))
    (sourceLimit : ProbabilityMeasure D39GeomRootedMapClass.{0})
    (sourceLocalLimit : Tendsto (fun k =>
      uibotFiniteSourceEdgeProbabilityLaw ℓ ρ (ns k) hℓ hρ (hsize k) (hne k))
      atTop (𝓝 sourceLimit)) :
    (sourceLimit : Measure D39GeomRootedMapClass.{0}) =
      wholePlaneIIDCodeMeasure.map
        (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved) := by
  have h := tendsto_nhds_unique sourceLocalLimit
    (uibotFiniteSourceEdgeProbabilityLaw_tendsto ℓ ρ hℓ hρ ns hns hsize hne)
  exact congrArg ProbabilityMeasure.toMeasure h

/-- Helper toward Proposition 3.9: the actual-edge finite source sequence
has a limit, whose measure is the iid KMSW pushforward. No limit-existence
or finite-law identification hypothesis is used. -/
theorem uibotFiniteSourceEdgeLimit_eq_iidLaw
    (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (hsize : ∀ k, 1 ≤ ns k)
    (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k))) :
    letI _uibotWholePlaneSourcePart3LimitNonempty :
        Nonempty (ProbabilityMeasure D39GeomRootedMapClass.{0}) :=
      ⟨uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved⟩
    ((limUnder atTop (fun k => uibotFiniteSourceEdgeProbabilityLaw ℓ ρ (ns k)
      hℓ hρ (hsize k) (hne k)) : ProbabilityMeasure D39GeomRootedMapClass.{0}) :
        Measure D39GeomRootedMapClass.{0}) =
      wholePlaneIIDCodeMeasure.map
        (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved) := by
  simp only [uibotFiniteSourceEdgeProbabilityLaw_eq_geometric]
  exact uibotGeometricLocalLimit_eq_iidPushforward ℓ ρ hℓ hρ ns hns hsize hne

end DirectedDistances.PaperProofs.Section3
end
