/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.D39GeomMirror2
public import DirectedDistances.PaperProofs.Section5.Prop59D39ClassLaw
public import DirectedDistances.PaperProofs.Section5.Prop59FiniteInvariance

/-! Helper toward Proposition 5.9 (`prop-uihbot-sym`), source
ordered mark `(x₀,x₁)` to `(h(x₁),h(x₀))`, preserves present-edge directions,
and keeps missing edges unoriented.

The proved result below is a conditional push-forward transfer from the
combinatorial local topology class law to the measurable missing-root geometric class
space. It does not construct the canonical geometric realization required
to discharge its explicit compatibility hypothesis. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap MeasureTheory
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section3.RootedBallSystem

/-- Helper toward Proposition 5.9. If a measurable realization of
combinatorial local topology classes into the missing-root geometric class space
commutes with the ordered-root geometric mirror, then the push-forward of the
UIBHBOT local topology class law is invariant under that geometric mirror. The explicit
`hcompatibility` hypothesis supplies exactly the measurable realization and
mirror compatibility still needed for geometric identification (1); it is not
asserted by this theorem. The mirror is measurable by
`d39MissingClassMirror_borel_measurable`. -/
theorem uibhbotD39MissingClassLaw_geomMirror_invariant_of_compatibility
    (realize : D39PlanarRootedMapClass → D39MissingMapClass)
    (hcompatibility :
      @Measurable D39PlanarRootedMapClass D39MissingMapClass
        (borel D39PlanarRootedMapClass) (borel D39MissingMapClass) realize ∧
      ∀ M : RootedLocallyFinitePlanarMap,
      realize (Quotient.mk D39PlanarRootedMap.setoid
        ((mirrorRootedLocallyFinitePlanarMap M).toD39PlanarRootedMap)) =
      d39MissingClassMirror
        (realize (Quotient.mk D39PlanarRootedMap.setoid
          M.toD39PlanarRootedMap))) :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    letI : MeasurableSpace D39MissingMapClass := borel D39MissingMapClass
    letI : BorelSpace D39MissingMapClass := ⟨rfl⟩
    (((uibhbotRootedPlanarMapLaw.map
      (fun M : RootedLocallyFinitePlanarMap =>
        Quotient.mk D39PlanarRootedMap.setoid M.toD39PlanarRootedMap)).map
          realize).map d39MissingClassMirror) =
      ((uibhbotRootedPlanarMapLaw.map
        (fun M : RootedLocallyFinitePlanarMap =>
          Quotient.mk D39PlanarRootedMap.setoid M.toD39PlanarRootedMap)).map
            realize) := by
  rcases hcompatibility with ⟨hrealize, hcompat⟩
  letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  letI : MeasurableSpace D39MissingMapClass := borel D39MissingMapClass
  letI : BorelSpace D39MissingMapClass := ⟨rfl⟩
  letI : TopologicalSpace D39PlanarRootedMapClass :=
    d39PlanarRootedMapClass_topologicalSpace
  letI : MeasurableSpace D39PlanarRootedMapClass :=
    d39PlanarRootedMapClass_measurableSpace
  letI : BorelSpace D39PlanarRootedMapClass := ⟨rfl⟩
  let f : RootedLocallyFinitePlanarMap → D39PlanarRootedMapClass :=
    fun M => Quotient.mk D39PlanarRootedMap.setoid M.toD39PlanarRootedMap
  let fm : RootedLocallyFinitePlanarMap → D39PlanarRootedMapClass :=
    fun M => Quotient.mk D39PlanarRootedMap.setoid
      ((mirrorRootedLocallyFinitePlanarMap M).toD39PlanarRootedMap)
  have hf : Measurable f := by
    exact continuous_d39PlanarRootedMapClassMap.measurable
  have hmirror : Measurable mirrorRootedLocallyFinitePlanarMap :=
    measurable_mirrorRootedLocallyFinitePlanarMap
  have hfm : Measurable fm := by
    exact hf.comp hmirror
  have hgeom : @Measurable D39MissingMapClass D39MissingMapClass
      (borel D39MissingMapClass) (borel D39MissingMapClass)
      d39MissingClassMirror := d39MissingClassMirror_borel_measurable
  have hclass := uibhbotRootedPlanarMapLaw_d39Class_mirror_invariant
  have hpost := congrArg
    (fun ν : ProbabilityMeasure D39PlanarRootedMapClass => ν.map realize) hclass
  have hpostMeasure :
      (((uibhbotRootedPlanarMapLaw.map fm).map realize) :
        ProbabilityMeasure D39MissingMapClass).toMeasure =
      (((uibhbotRootedPlanarMapLaw.map f).map realize) :
        ProbabilityMeasure D39MissingMapClass).toMeasure :=
    congrArg ProbabilityMeasure.toMeasure hpost
  have hcomposed :
      (uibhbotRootedPlanarMapLaw : ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map
          (fun M => realize (fm M)) =
        (uibhbotRootedPlanarMapLaw : ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map
          (fun M => realize (f M)) := by
    calc
      (uibhbotRootedPlanarMapLaw :
          ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map
            (fun M => realize (fm M)) =
        ((uibhbotRootedPlanarMapLaw.map fm :
          ProbabilityMeasure D39PlanarRootedMapClass).toMeasure).map realize := by
            exact (Measure.map_map hrealize hfm).symm
      _ = ((uibhbotRootedPlanarMapLaw.map f :
          ProbabilityMeasure D39PlanarRootedMapClass).toMeasure).map realize :=
        hpostMeasure
      _ = (uibhbotRootedPlanarMapLaw :
          ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map
            (fun M => realize (f M)) := by
            exact Measure.map_map hrealize hf
  apply Subtype.ext
  change (((uibhbotRootedPlanarMapLaw :
      ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map f).map
        realize).map d39MissingClassMirror =
    ((uibhbotRootedPlanarMapLaw :
      ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map f).map realize
  calc
    (((uibhbotRootedPlanarMapLaw :
        ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map f).map
          realize).map d39MissingClassMirror =
        (uibhbotRootedPlanarMapLaw :
          ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map
            (fun M => d39MissingClassMirror (realize (f M))) := by
          calc
            (((uibhbotRootedPlanarMapLaw :
                ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map f).map
                  realize).map d39MissingClassMirror =
                ((uibhbotRootedPlanarMapLaw :
                    ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map f).map
                  (fun c => d39MissingClassMirror (realize c)) :=
              Measure.map_map hgeom hrealize
            _ = (uibhbotRootedPlanarMapLaw :
                  ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map
                    (fun M => d39MissingClassMirror (realize (f M))) :=
              Measure.map_map (hgeom.comp hrealize) hf
    _ = (uibhbotRootedPlanarMapLaw :
          ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map
            (fun M => realize (fm M)) := by
          congr 1
          funext M
          exact (hcompat M).symm
    _ = (uibhbotRootedPlanarMapLaw :
          ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map
            (fun M => realize (f M)) := hcomposed
    _ = ((uibhbotRootedPlanarMapLaw :
          ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map f).map
            realize := by
          exact (Measure.map_map hrealize hf).symm






































end DirectedDistances.PaperProofs.Section5

end
