/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59D39GeomMirrorLawAE

/-! Helper toward Proposition 5.9. A canonical geometric realization for this
code law must provide a measurable function of the code whose value is the
local topology missing-root class of the canonical assembly drawing, together with the
almost-sure identity commuting that realization with the ordered-root mirror.
The existing `uibhbotProviderAssemblyD39_identification` records the assembly
rotation, present-edge directions, missing-root data, face correspondence,
and ordered root, while
`uibhbotCodeLawRel_ae_provider_d39PlanarClass_eq_mirror` relates the provider
and code-selected maps after combinatorial reflection. These results do not
yet provide the required measurable geometric-class realization or its mirror
identity. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap MeasureTheory
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section3.RootedBallSystem

/-- Helper toward Proposition 5.9. If a realization is almost-everywhere
measurable for the code-pushed local topology class law and commutes almost surely with
the geometric mirror of the code-built map, then its code-space law is
invariant under the ordered-root geometric mirror. -/
theorem uibhbotD39MissingClassLaw_geomMirror_invariant_of_code_ae_compatibility
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
        ((uibhbotCodeLawRel.map
          (fun W : ℤ → Fin 3 =>
            Quotient.mk D39PlanarRootedMap.setoid
              (uibhbotRootedPlanarMapOfCode W).toD39PlanarRootedMap) :
              ProbabilityMeasure D39PlanarRootedMapClass).toMeasure))
    (hcompatibility :
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
      ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
        realize (Quotient.mk D39PlanarRootedMap.setoid
          ((mirrorRootedLocallyFinitePlanarMap
            (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap)) =
        d39MissingClassMirror
          (realize (Quotient.mk D39PlanarRootedMap.setoid
            (uibhbotRootedPlanarMapOfCode W).toD39PlanarRootedMap))) :
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
    (((uibhbotCodeLawRel.map
      (fun W : ℤ → Fin 3 =>
        Quotient.mk D39PlanarRootedMap.setoid
          (uibhbotRootedPlanarMapOfCode W).toD39PlanarRootedMap)).map
            realize).map d39MissingClassMirror) =
      ((uibhbotCodeLawRel.map
        (fun W : ℤ → Fin 3 =>
          Quotient.mk D39PlanarRootedMap.setoid
            (uibhbotRootedPlanarMapOfCode W).toD39PlanarRootedMap)).map realize) := by
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
  let μ : Measure (ℤ → Fin 3) := uibhbotCodeLawRel.toMeasure
  let mapCode : (ℤ → Fin 3) → RootedLocallyFinitePlanarMap :=
    uibhbotRootedPlanarMapOfCode
  let classOfMap : RootedLocallyFinitePlanarMap → D39PlanarRootedMapClass :=
    fun M => Quotient.mk D39PlanarRootedMap.setoid M.toD39PlanarRootedMap
  let mirroredClassOfMap : RootedLocallyFinitePlanarMap → D39PlanarRootedMapClass :=
    fun M => Quotient.mk D39PlanarRootedMap.setoid
      ((mirrorRootedLocallyFinitePlanarMap M).toD39PlanarRootedMap)
  let codeClass : (ℤ → Fin 3) → D39PlanarRootedMapClass := classOfMap ∘ mapCode
  let codeMirroredClass : (ℤ → Fin 3) → D39PlanarRootedMapClass :=
    mirroredClassOfMap ∘ mapCode
  have hmap : Measurable mapCode := measurable_uibhbotRootedPlanarMapOfCode
  have hclass : Measurable classOfMap :=
    continuous_d39PlanarRootedMapClassMap.measurable
  have hmirrorMap : Measurable mirrorRootedLocallyFinitePlanarMap :=
    measurable_mirrorRootedLocallyFinitePlanarMap
  have hmirroredClass : Measurable mirroredClassOfMap := hclass.comp hmirrorMap
  have hcodeClass : Measurable codeClass := hclass.comp hmap
  have hcodeMirroredClass : Measurable codeMirroredClass := hmirroredClass.comp hmap
  have hclassLaw := congrArg ProbabilityMeasure.toMeasure
    uibhbotRootedPlanarMapLaw_d39Class_mirror_invariant
  have hclassLaw' :
      ((uibhbotRootedPlanarMapLaw :
        ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure).map
          mirroredClassOfMap =
        ((uibhbotRootedPlanarMapLaw :
          ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure).map
            classOfMap := by
    exact hclassLaw
  have hcodeLawMap :
      μ.map mapCode =
        ((uibhbotRootedPlanarMapLaw :
          ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure) := rfl
  have hcodeClassLaw : μ.map codeMirroredClass = μ.map codeClass := by
    calc
      μ.map codeMirroredClass = (μ.map mapCode).map mirroredClassOfMap := by
        change μ.map (mirroredClassOfMap ∘ mapCode) = _
        rw [Measure.map_map hmirroredClass hmap]
      _ = (μ.map mapCode).map classOfMap := by
        rw [hcodeLawMap]
        exact hclassLaw'
      _ = μ.map codeClass := by
        change (μ.map mapCode).map classOfMap = μ.map (classOfMap ∘ mapCode)
        rw [Measure.map_map hclass hmap]
  have hrealizeCode : AEMeasurable (realize ∘ codeClass) μ :=
    hrealize.comp_aemeasurable hcodeClass.aemeasurable
  have hrealize' : AEMeasurable realize (μ.map codeClass) := hrealize
  have hrealizeMirror : AEMeasurable realize (μ.map codeMirroredClass) := by
    rw [hcodeClassLaw]
    exact hrealize'
  have hpost :
      (μ.map codeMirroredClass).map realize = (μ.map codeClass).map realize :=
    congrArg (fun ν : Measure D39PlanarRootedMapClass => ν.map realize) hcodeClassLaw
  have hcompatibility' :
      ∀ᵐ W ∂μ, realize (codeMirroredClass W) =
        d39MissingClassMirror (realize (codeClass W)) := by
    filter_upwards [hcompatibility] with W hW
    exact hW
  have hcompatibilityMeasure :
      μ.map (fun W => realize (codeMirroredClass W)) =
        μ.map (fun W => d39MissingClassMirror (realize (codeClass W))) := by
    apply Measure.map_congr
    exact hcompatibility'
  have hgeom : Measurable d39MissingClassMirror :=
    d39MissingClassMirror_borel_measurable
  apply Subtype.ext
  change ((μ.map codeClass).map realize).map d39MissingClassMirror =
    (μ.map codeClass).map realize
  calc
    ((μ.map codeClass).map realize).map d39MissingClassMirror =
        μ.map (fun W => d39MissingClassMirror (realize (codeClass W))) := by
      calc
        ((μ.map codeClass).map realize).map d39MissingClassMirror =
            (μ.map codeClass).map (d39MissingClassMirror ∘ realize) :=
          hgeom.aemeasurable.map_map_of_aemeasurable hrealize'
        _ = μ.map (d39MissingClassMirror ∘ realize ∘ codeClass) :=
          (hgeom.comp_aemeasurable hrealize').map_map_of_aemeasurable
            hcodeClass.aemeasurable
    _ = μ.map (fun W => realize (codeMirroredClass W)) :=
      hcompatibilityMeasure.symm
    _ = (μ.map codeMirroredClass).map realize :=
      (hrealizeMirror.map_map_of_aemeasurable hcodeMirroredClass.aemeasurable).symm
    _ = (μ.map codeClass).map realize := hpost

end DirectedDistances.PaperProofs.Section5

end













































































