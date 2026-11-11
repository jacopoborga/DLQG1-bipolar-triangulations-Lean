/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59Reduction
public import DirectedDistances.PaperProofs.Section5.Prop59Part2
public import DirectedDistances.PaperProofs.Section5.Prop59Part4
public import DirectedDistances.PaperProofs.Section5.Prop59MirrorRepPart2
public import DirectedDistances.PaperProofs.Section5.Prop516SourceGeometricLaw
public import DirectedDistances.PaperProofs.Section5.Prop59SourceStatement

/-! Supporting lemmas for paper labels `prop-uihbot-sym` (see CORRESPONDENCE.md). -/






public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap MeasureTheory
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open Prop516ExteriorAssembly6
open scoped ENNReal Topology

/-- Helper toward Proposition 5.9. Use the geometric Borel sigma algebra. -/
local instance prop59GeometricClassLaw_measurable :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}

/-- Helper toward Proposition 5.9. The geometric sigma algebra is Borel. -/
local instance prop59GeometricClassLaw_borel :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

private theorem root_missing_iff_of_iso {A B : D39DomainRootedMap}
    (e : D39GeomRootedMapIsoV2 A.map A.root B.map B.root) :
    A.map.toPlaneMapWithMissing.missing A.root.1 ↔
      B.map.toPlaneMapWithMissing.missing B.root.1 := by
  rw [← e.root_edge_map]
  exact (e.missing_map A.root.1).symm

/-- Helper toward Proposition 5.9. Extend reflection on missing-root
domain representatives by the identity on present-root representatives. -/
@[expose] def prop59GeometricDomainMirror (A : D39DomainRootedMap) :
    D39DomainRootedMap := by
  classical
  exact if hm : A.map.toPlaneMapWithMissing.missing A.root.1 then
    (d39MissingMirror ⟨A, hm⟩).val else A





@[expose] def prop59GeometricClassMirror :
    D39GeomRootedMapClass.{0} → D39GeomRootedMapClass.{0} :=
  Quotient.map prop59GeometricDomainMirror (by
    intro A B h
    obtain ⟨e⟩ := h
    have hm := root_missing_iff_of_iso e
    by_cases hA : A.map.toPlaneMapWithMissing.missing A.root.1
    · have hB := hm.mp hA
      simpa only [prop59GeometricDomainMirror, dite_eq_left hA, dite_eq_left hB] using
        (show d39DomainSetoid (d39MissingMirror ⟨A, hA⟩).val
          (d39MissingMirror ⟨B, hB⟩).val from ⟨e.geomMirror⟩)
    · have hB : ¬ B.map.toPlaneMapWithMissing.missing B.root.1 :=
        fun h => hA (hm.mpr h)
      simpa only [prop59GeometricDomainMirror, dite_eq_right hA, dite_eq_right hB] using
        (show d39DomainSetoid A B from ⟨e⟩))

/-- Helper toward Proposition 5.9. On the missing-root subspace the total
mirror agrees exactly with the already constructed measurable class mirror. -/
theorem prop59GeometricClassMirror_forget (c : D39MissingMapClass.{0}) :
    prop59GeometricClassMirror (d39MissingClassForget c) =
      d39MissingClassForget (d39MissingClassMirror c) := by
  refine Quotient.inductionOn c ?_
  intro A
  change Quotient.mk d39DomainSetoid (prop59GeometricDomainMirror A.val) = _
  simp only [prop59GeometricDomainMirror, dite_eq_left A.property]
  rfl

/-- Helper toward Proposition 5.9. Reflection on a missing-root
representative conjugates the drawing and reverses precisely its root mark. -/
theorem prop59GeometricClassMirror_mk (A : D39DomainRootedMap.{0})
    (hm : A.map.toPlaneMapWithMissing.missing A.root.1) :
    prop59GeometricClassMirror (Quotient.mk d39DomainSetoid A) =
      Quotient.mk d39DomainSetoid
        (⟨A.V, A.E, A.map.geomMirror, d39GeomMirrorRoot A.root,
          A.domain.geomMirror hm⟩ : D39DomainRootedMap) := by
  change Quotient.mk d39DomainSetoid (prop59GeometricDomainMirror A) = _
  simp only [prop59GeometricDomainMirror, dite_eq_left hm]
  rfl

private theorem root_missing_iff_of_ballIso {A B : D39DomainRootedMap}
    {r : ℕ} (e : D39GeomBallIsoV2 r A.map A.root B.map B.root) :
    A.map.toPlaneMapWithMissing.missing A.root.1 ↔
      B.map.toPlaneMapWithMissing.missing B.root.1 := by
  have h := e.missing_map
    ⟨A.root.1, d39GeomRootEdge_mem A.map A.root e.radius_pos⟩
  rw [e.root_edge_map] at h
  exact h.symm

/-- Helper toward Proposition 5.9. The total geometric class mirror has
the same local factor-two distance control as the missing-root mirror;
nearby classes have the same missing-root status. -/
theorem prop59GeometricClassMirror_edist_le (c d : D39GeomRootedMapClass.{0})
    (hsmall : edist c d ≤ (1 / 4 : ℝ≥0∞)) :
    edist (prop59GeometricClassMirror c) (prop59GeometricClassMirror d) ≤
      2 * edist c d := by
  revert hsmall
  refine Quotient.inductionOn₂ c d ?_
  intro A B hsmall
  have hball : Nonempty (D39GeomBallIsoV2 2 A.map A.root B.map B.root) :=
    (d39ClassDistance_le_pow_iff_nonempty (by omega) A B).mp
      (by
        convert hsmall using 1
        norm_num only [one_div]
        rw [← ENNReal.inv_pow]
        norm_num)
  obtain ⟨e⟩ := hball
  have hm := root_missing_iff_of_ballIso e
  by_cases hA : A.map.toPlaneMapWithMissing.missing A.root.1
  · have hB := hm.mp hA
    rw [prop59GeometricClassMirror_mk A hA, prop59GeometricClassMirror_mk B hB]
    exact d39GeomDistanceV2_mirror_le_two_mul A.map A.root B.map B.root hsmall
  · have hB : ¬ B.map.toPlaneMapWithMissing.missing B.root.1 :=
      fun h => hA (hm.mpr h)
    change d39ClassDistance (Quotient.mk _ (prop59GeometricDomainMirror A))
      (Quotient.mk _ (prop59GeometricDomainMirror B)) ≤ _
    simp only [prop59GeometricDomainMirror, dite_eq_right hA, dite_eq_right hB]
    exact le_mul_of_one_le_left (by positivity) (by norm_num)

/-- Helper toward Proposition 5.9. The total mirror is uniformly
continuous for the Definition 3.8 geometric class pseudometric. -/
theorem prop59GeometricClassMirror_uniformContinuous :
    UniformContinuous prop59GeometricClassMirror := by
  apply EMetric.uniformContinuous_iff_le.mpr
  intro ε hε
  refine ⟨min (1 / 4 : ℝ≥0∞) (ε / 2), lt_min (by norm_num)
    (ENNReal.div_pos (ne_of_gt hε) (by norm_num)), ?_⟩
  intro c d hcd
  calc
    edist (prop59GeometricClassMirror c) (prop59GeometricClassMirror d) ≤
        2 * edist c d := prop59GeometricClassMirror_edist_le c d
          (hcd.trans (min_le_left _ _))
    _ ≤ 2 * (ε / 2) := by gcongr; exact hcd.trans (min_le_right _ _)
    _ = ε := ENNReal.mul_div_cancel (by norm_num) (by norm_num)

/-- Helper toward Proposition 5.9. The total geometric class mirror is
Borel measurable, so it can be applied to the source geometric law. -/
theorem measurable_prop59GeometricClassMirror : Measurable prop59GeometricClassMirror :=
  prop59GeometricClassMirror_uniformContinuous.continuous.measurable

/-- Helper toward Proposition 5.9. On one conull event, the reflected
canonical class is exactly the class of the reflected canonical assembly,
and that assembly represents the mirrored code map. No law equality or
geometric comparison is a premise. -/
theorem prop59GeometricClassMirror_canonical_representation_ae :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ (B : D39DomainRootedMapV2.{0})
        (hm : B.map.toPlaneMapWithMissing.missing B.root.1),
        canonicalGeometricClass W = PLCylinderBall.geometricClass B ∧
        prop59GeometricClassMirror (canonicalGeometricClass W) =
          Quotient.mk d39DomainSetoid
            (⟨B.V, B.E, B.map.geomMirror, d39GeomMirrorRoot B.root,
              B.domain.geomMirror hm⟩ : D39DomainRootedMap) ∧
        D39DrawingRepresents3
          ((mirrorRootedLocallyFinitePlanarMap
            (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap)
          ⟨B.V, B.E, B.map.geomMirror, d39GeomMirrorRoot B.root,
            B.domain.geomMirror hm⟩ := by
  filter_upwards [prop59_mirrorRep_canonicalRepresentation_ae,
    Prop516ExteriorAssembly6.canonicalGeometricClass_spec] with W hw hc
  obtain ⟨H, h0, hL, hR, hfin, hRpos, hA, hmirrorDomain, hrep⟩ := hw
  let D : UIBHBOTD39CanonicalDomainWitness W :=
    ⟨H, h0, hL, hR, hfin, hRpos, hA⟩
  let B := uibhbotD39CanonicalRepresentation13Domain W D
  have hm : B.map.toPlaneMapWithMissing.missing B.root.1 :=
    (hA.geomMirror_iff_missing).mp hmirrorDomain
  have he : canonicalGeometricClass W = PLCylinderBall.geometricClass B := by
    obtain ⟨hs, he⟩ := hc
    simpa only [uibhbotD39CanonicalClass_eq_some_domain W D, Option.get_some] using he
  refine ⟨B, hm, he, ?_, ?_⟩
  · rw [he]
    exact prop59GeometricClassMirror_mk (PLCylinderBall.domainMap B) hm
  · exact hrep

/-- Helper toward Proposition 5.9. OPEN 1, OPEN 2 and OPEN 3 give zero
geometric distance between every pair of PL representations of the mirrored
code on one conull event, simultaneously at all radii. The conclusion uses
the installed pseudometric and does not assert whole-map class equality. -/
theorem prop59_mirroredCode_PLRepresentations_edist_zero_ae :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (B C : D39DomainRootedMapV2.{0})
        (_x : PLCylinderBall.Representation
          ((mirrorRootedLocallyFinitePlanarMap
            (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap) B)
        (_y : PLCylinderBall.Representation
          ((mirrorRootedLocallyFinitePlanarMap
            (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap) C),
        edist (PLCylinderBall.geometricClass B) (PLCylinderBall.geometricClass C) = 0 := by
  filter_upwards [prop59_mirrorRep_canonicalRepresentation_ae] with W hw
  obtain ⟨H, h0, hL, hR, hfin, hRpos, hA, hmirrorDomain, ⟨canonical⟩⟩ := hw
  intro B C x y
  change d39GeomDistanceV2 B.map B.root C.map C.root = 0
  apply d39GeomDistanceV2_eq_zero_iff.mpr
  intro r hr
  exact prop59_canonicalPair_geomBallIso W H h0 hL hR hfin hRpos
    hA hmirrorDomain canonical x y r hr (D39BallIso.refl _)

/-- Helper toward Proposition 5.9. The reflected source law is the
pushforward of code by the reflected canonical geometric class. This
uses the proved source-law characterization and mirror measurability;
it is a normalization, not a symmetry premise or invariance conclusion. -/
theorem uibhbotSourceGeometricClassLaw_map_mirror_eq_codePushforward :
    uibhbotSourceGeometricClassLaw.map prop59GeometricClassMirror =
      uibhbotCodeLawRel.map
        (fun W => prop59GeometricClassMirror (canonicalGeometricClass W)) := by
  rw [uibhbotSourceGeometricClassLaw_eq_canonicalCodePushforward]
  apply ProbabilityMeasure.toMeasure_injective
  exact Measure.map_map measurable_prop59GeometricClassMirror
    measurable_canonicalGeometricClass



































end DirectedDistances.PaperProofs.Section5
end
