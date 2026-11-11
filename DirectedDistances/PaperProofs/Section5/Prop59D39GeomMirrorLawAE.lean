/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59D39GeomMirrorLaw

/-! Helper toward Proposition 5.9. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap MeasureTheory
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section3.RootedBallSystem

/-- Helper toward Proposition 5.9. If a realization is almost-everywhere
measurable for the pushed-forward local topology class law and commutes almost surely
with the ordered-root geometric mirror, its law is invariant under that
mirror. -/
theorem uibhbotD39MissingClassLaw_geomMirror_invariant_of_ae_compatibility
    (realize : D39PlanarRootedMapClass → D39MissingMapClass)
    (hrealize :
      letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
        bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
      letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
        borel RootedLocallyFinitePlanarMap
      letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
      letI : TopologicalSpace D39PlanarRootedMapClass :=
        d39PlanarRootedMapClass_topologicalSpace
      letI : MeasurableSpace D39PlanarRootedMapClass :=
        d39PlanarRootedMapClass_measurableSpace
      letI : BorelSpace D39PlanarRootedMapClass := ⟨rfl⟩
      letI : MeasurableSpace D39MissingMapClass := borel D39MissingMapClass
      letI : BorelSpace D39MissingMapClass := ⟨rfl⟩
      AEMeasurable realize
        ((uibhbotRootedPlanarMapLaw.map
          (fun M : RootedLocallyFinitePlanarMap =>
            Quotient.mk D39PlanarRootedMap.setoid M.toD39PlanarRootedMap) :
              ProbabilityMeasure D39PlanarRootedMapClass).toMeasure))
    (hcompatibility :
      letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
        bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
      letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
        borel RootedLocallyFinitePlanarMap
      letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
      letI : MeasurableSpace D39MissingMapClass := borel D39MissingMapClass
      letI : BorelSpace D39MissingMapClass := ⟨rfl⟩
      ∀ᵐ M ∂(uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap),
        realize (Quotient.mk D39PlanarRootedMap.setoid
          ((mirrorRootedLocallyFinitePlanarMap M).toD39PlanarRootedMap)) =
        d39MissingClassMirror
          (realize (Quotient.mk D39PlanarRootedMap.setoid M.toD39PlanarRootedMap))) :
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
  letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  letI : TopologicalSpace D39PlanarRootedMapClass :=
    d39PlanarRootedMapClass_topologicalSpace
  letI : MeasurableSpace D39PlanarRootedMapClass :=
    d39PlanarRootedMapClass_measurableSpace
  letI : BorelSpace D39PlanarRootedMapClass := ⟨rfl⟩
  letI : MeasurableSpace D39MissingMapClass := borel D39MissingMapClass
  letI : BorelSpace D39MissingMapClass := ⟨rfl⟩
  let f : RootedLocallyFinitePlanarMap → D39PlanarRootedMapClass :=
    fun M => Quotient.mk D39PlanarRootedMap.setoid M.toD39PlanarRootedMap
  let fm : RootedLocallyFinitePlanarMap → D39PlanarRootedMapClass :=
    fun M => Quotient.mk D39PlanarRootedMap.setoid
      ((mirrorRootedLocallyFinitePlanarMap M).toD39PlanarRootedMap)
  have hf : Measurable f := continuous_d39PlanarRootedMapClassMap.measurable
  have hmirror : Measurable mirrorRootedLocallyFinitePlanarMap :=
    measurable_mirrorRootedLocallyFinitePlanarMap
  have hfm : Measurable fm := hf.comp hmirror
  have hgeom : Measurable d39MissingClassMirror :=
    d39MissingClassMirror_borel_measurable
  have hrealize' : AEMeasurable realize
      ((uibhbotRootedPlanarMapLaw.map f :
        ProbabilityMeasure D39PlanarRootedMapClass).toMeasure) := hrealize
  have hcompatibility' :
      ∀ᵐ M ∂(uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap),
        realize (fm M) = d39MissingClassMirror (realize (f M)) := by
    filter_upwards [hcompatibility] with M hM
    exact hM
  have hclass := uibhbotRootedPlanarMapLaw_d39Class_mirror_invariant
  have hclassMeasure :
      (uibhbotRootedPlanarMapLaw : ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map fm =
        (uibhbotRootedPlanarMapLaw : ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map f := by
    exact congrArg ProbabilityMeasure.toMeasure hclass
  have hrealizeMirror : AEMeasurable realize
      ((uibhbotRootedPlanarMapLaw : ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map fm) := by
    rw [hclassMeasure]
    exact hrealize'
  have hpost := congrArg
    (fun ν : ProbabilityMeasure D39PlanarRootedMapClass => ν.map realize) hclass
  have hpostMeasure :
      (((uibhbotRootedPlanarMapLaw.map fm).map realize :
        ProbabilityMeasure D39MissingMapClass).toMeasure) =
      (((uibhbotRootedPlanarMapLaw.map f).map realize :
        ProbabilityMeasure D39MissingMapClass).toMeasure) :=
    congrArg ProbabilityMeasure.toMeasure hpost
  have hcompatibilityMeasure :
      (uibhbotRootedPlanarMapLaw : ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map
          (fun M => realize (Quotient.mk D39PlanarRootedMap.setoid
            ((mirrorRootedLocallyFinitePlanarMap M).toD39PlanarRootedMap))) =
        (uibhbotRootedPlanarMapLaw : ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map
          (fun M => d39MissingClassMirror (realize
            (Quotient.mk D39PlanarRootedMap.setoid M.toD39PlanarRootedMap))) := by
    apply Measure.map_congr
    filter_upwards [hcompatibility] with M hM
    exact hM
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
        ((uibhbotRootedPlanarMapLaw :
          ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map f).map
            (d39MissingClassMirror ∘ realize) := by
          exact AEMeasurable.map_map_of_aemeasurable
            (hgeom.aemeasurable : AEMeasurable d39MissingClassMirror
              (((uibhbotRootedPlanarMapLaw : ProbabilityMeasure
                RootedLocallyFinitePlanarMap).toMeasure.map f).map realize))
            hrealize'
    _ = (uibhbotRootedPlanarMapLaw :
          ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map
            (fun M => d39MissingClassMirror (realize (f M))) := by
          exact (hgeom.comp_aemeasurable hrealize').map_map_of_aemeasurable
            hf.aemeasurable
    _ = (uibhbotRootedPlanarMapLaw :
          ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map
            (fun M => realize (fm M)) := hcompatibilityMeasure.symm
    _ = ((uibhbotRootedPlanarMapLaw :
          ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map fm).map realize := by
          exact (hrealizeMirror.map_map_of_aemeasurable hfm.aemeasurable).symm
    _ = ((uibhbotRootedPlanarMapLaw :
          ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map f).map realize :=
      hpostMeasure
/-- Helper toward Proposition 5.9. The globally measurable, pointwise
compatibility hypothesis from the existing helper implies the almost-everywhere
hypotheses above. -/
theorem uibhbotD39MissingClassLaw_geomMirror_invariant_of_compatibility_via_ae
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
  letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  letI : TopologicalSpace D39PlanarRootedMapClass :=
    d39PlanarRootedMapClass_topologicalSpace
  letI : MeasurableSpace D39PlanarRootedMapClass :=
    d39PlanarRootedMapClass_measurableSpace
  letI : BorelSpace D39PlanarRootedMapClass := ⟨rfl⟩
  letI : MeasurableSpace D39MissingMapClass := borel D39MissingMapClass
  letI : BorelSpace D39MissingMapClass := ⟨rfl⟩
  have hf : Measurable (fun M : RootedLocallyFinitePlanarMap =>
      Quotient.mk D39PlanarRootedMap.setoid M.toD39PlanarRootedMap) :=
    continuous_d39PlanarRootedMapClassMap.measurable
  have hrealize : AEMeasurable realize
      ((uibhbotRootedPlanarMapLaw.map
        (fun M : RootedLocallyFinitePlanarMap =>
          Quotient.mk D39PlanarRootedMap.setoid M.toD39PlanarRootedMap) :
            ProbabilityMeasure D39PlanarRootedMapClass).toMeasure) :=
    hcompatibility.1.aemeasurable
  have hcompat :
      ∀ᵐ M ∂(uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap),
        realize (Quotient.mk D39PlanarRootedMap.setoid
          ((mirrorRootedLocallyFinitePlanarMap M).toD39PlanarRootedMap)) =
        d39MissingClassMirror (realize (Quotient.mk D39PlanarRootedMap.setoid
          M.toD39PlanarRootedMap)) :=
    Filter.Eventually.of_forall hcompatibility.2
  exact uibhbotD39MissingClassLaw_geomMirror_invariant_of_ae_compatibility
    realize hrealize hcompat

end DirectedDistances.PaperProofs.Section5

end
