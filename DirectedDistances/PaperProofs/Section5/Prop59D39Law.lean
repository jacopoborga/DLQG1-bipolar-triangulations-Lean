module

public import DirectedDistances.PaperProofs.Section5.Prop59CodeLawMirror
public import DirectedDistances.PaperProofs.Section5.Prop516D39Transport

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap MeasureTheory
open DirectedDistances.PaperProofs.Section3.RootedBallSystem

/-! Helpers toward Proposition 5.9 (prop-uihbot-sym). -/

/-- Helper toward Proposition 5.9. The local topology image of the code-law mirror symmetry
is invariant under reflection. This statement concerns the local topology image and does
not assert that the local topology representation is faithful. -/
theorem uibhbotRootedPlanarMapLaw_d39_mirror_invariant :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    letI : TopologicalSpace D39RootedMap :=
      bsLocalDistanceTopologyGeneric d39RootedBallSystem
    letI : MeasurableSpace D39RootedMap := borel D39RootedMap
    letI : BorelSpace D39RootedMap := ⟨rfl⟩
    (uibhbotRootedPlanarMapLaw.map
      (fun M => (mirrorRootedLocallyFinitePlanarMap M).toRootedLocallyFiniteMap.toD39RootedMap)) =
    (uibhbotRootedPlanarMapLaw.map
      (fun M => M.toRootedLocallyFiniteMap.toD39RootedMap)) := by
  letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  letI : TopologicalSpace D39RootedMap :=
    bsLocalDistanceTopologyGeneric d39RootedBallSystem
  letI : MeasurableSpace D39RootedMap := borel D39RootedMap
  letI : BorelSpace D39RootedMap := ⟨rfl⟩
  let f : RootedLocallyFinitePlanarMap → D39RootedMap :=
    fun M => M.toRootedLocallyFiniteMap.toD39RootedMap
  have hf : Measurable f := by
    exact measurable_toD39RootedMap
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
