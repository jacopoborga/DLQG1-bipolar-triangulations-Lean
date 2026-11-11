/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59D39Law
public import DirectedDistances.PaperProofs.Section5.Prop516D39ClassTransport

/-! Supporting lemmas for paper labels `prop-uihbot-sym` (see CORRESPONDENCE.md). -/









public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap MeasureTheory
open DirectedDistances.PaperProofs.Section3.RootedBallSystem

/-- Helper toward Proposition 5.9. The push-forward of the code-built UIBHBOT law to local topology planar
classes is invariant under reflection, for the Borel structure of the class-distance topology. -/
theorem uibhbotRootedPlanarMapLaw_d39Class_mirror_invariant :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    (uibhbotRootedPlanarMapLaw.map
      (fun M : RootedLocallyFinitePlanarMap =>
        Quotient.mk D39PlanarRootedMap.setoid
          ((mirrorRootedLocallyFinitePlanarMap M).toD39PlanarRootedMap))) =
    (uibhbotRootedPlanarMapLaw.map
      (fun M : RootedLocallyFinitePlanarMap =>
        Quotient.mk D39PlanarRootedMap.setoid M.toD39PlanarRootedMap)) := by
  letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  let f : RootedLocallyFinitePlanarMap → Quotient D39PlanarRootedMap.setoid :=
    fun M => Quotient.mk D39PlanarRootedMap.setoid M.toD39PlanarRootedMap
  have hc : Continuous f := continuous_d39PlanarRootedMapClassMap
  have hf : Measurable f := hc.measurable
  have hmirror : Measurable mirrorRootedLocallyFinitePlanarMap := by
    exact measurable_mirrorRootedLocallyFinitePlanarMap
  apply Subtype.ext
  change (uibhbotRootedPlanarMapLaw : ProbabilityMeasure
    RootedLocallyFinitePlanarMap).toMeasure.map (f ∘
      mirrorRootedLocallyFinitePlanarMap) =
    (uibhbotRootedPlanarMapLaw : ProbabilityMeasure
      RootedLocallyFinitePlanarMap).toMeasure.map f
  rw [← Measure.map_map hf hmirror,
    uibhbotRootedPlanarMapLaw_mirror_invariant]

end DirectedDistances.PaperProofs.Section5
