/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59SourceStatement
public import DirectedDistances.PaperProofs.Section5.Prop59RootAbsentAE
public import DirectedDistances.PaperProofs.Section5.Prop59MirrorCompat8
public import DirectedDistances.PaperProofs.Section5.Prop59MirrorCompat9
public import DirectedDistances.PaperProofs.Section5.Prop59MirrorCompat11
public import DirectedDistances.PaperProofs.Section5.Prop59D39GeomMirrorLawAE2
public import DirectedDistances.PaperProofs.Section5.Prop59CanonicalMirrorCompat6
public import DirectedDistances.PaperProofs.Section5.Prop59CanonicalMirroredRoot
public import DirectedDistances.PaperProofs.Section5.Prop516ExteriorMarkedComparison2

/-! Helpers toward Proposition 5.9 (`prop-uihbot-sym`,

The installed statement `Prop59SourceStatement.lean:118-124` concerns the
project carrier. Its own documentation at lines 112-117 and 133-143 explicitly
paper-facing declaration for Proposition 5.9 is installed in that file or in
`DirectedDistances/Paper/Section5`. This module preserves that distinction.

The newer `exteriorMarkedComparison_reparam_geomBallIso` supplies the retained
ambient-face comparison missing from the older Compat9 report. Consequently
OPEN 3, on the stated PL representation carrier, follows from OPEN 2 without
an additional geometric-isomorphism or face-correspondence premise. The
canonical assembly exterior comparison below also removes a redundant
target-root-missing premise and discharges root absence almost surely.

These reductions do not construct a geometric class realization of the
and integration belong to the sole coordinator. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap MeasureTheory
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section3.RootedBallSystem

/-- Helper toward Proposition 5.9. The exact project-carrier conclusion of
`Prop59SourceStatement.lean:118-124`, expressed directly as two code
pushforwards. Composition and mirror measurability are proved inputs from
the installed construction; no law equality is assumed. This is not a
geometric source-law identification. -/
theorem prop59_reduction_code_pushforward_mirror_invariant :
    letI _prop59Reduction_codeTopology : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI _prop59Reduction_codeMeasurable : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    (uibhbotCodeLawRel.map (fun W : ℤ → Fin 3 =>
      mirrorRootedLocallyFinitePlanarMap (uibhbotRootedPlanarMapOfCode W))) =
      uibhbotCodeLawRel.map uibhbotRootedPlanarMapOfCode := by
  let prop59Reduction_codeProofTopology : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  let prop59Reduction_codeProofMeasurable : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  let prop59Reduction_codeProofBorel : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  apply ProbabilityMeasure.toMeasure_injective
  change (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
      (mirrorRootedLocallyFinitePlanarMap ∘ uibhbotRootedPlanarMapOfCode) =
    (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map uibhbotRootedPlanarMapOfCode
  rw [← Measure.map_map measurable_mirrorRootedLocallyFinitePlanarMap
    measurable_uibhbotRootedPlanarMapOfCode]
  exact congrArg ProbabilityMeasure.toMeasure prop_uihbot_sym

/-- Helper toward Proposition 5.9. OPEN 2 gives the full OPEN 3 geometric
ball comparison for the exact PL representation binders in Compat3. The
retained ambient faces are supplied by the newer exterior-marked comparison,
and literal path equality supplies its endpoint-preserving reparameterizations.
No geometric ball isomorphism is assumed. -/
theorem prop59_representedGeomBallIso_of_open2
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B)
    (y : PLCylinderBall.Representation N C)
    (r : ℕ) (hr : 0 < r)
    (I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr))
    (hOpen2 : plBallFaceOrbitMap I
        (d39FacedBallPLWithExternal M x.drawing r hr).externalOrbit =
      (d39FacedBallPLWithExternal N y.drawing r hr).externalOrbit) :
    Nonempty (D39GeomBallIsoV2 r B.map B.root C.map C.root) := by
  have hmarked : Quotient.mk exteriorMarkedBallSetoid
        (d39FacedBallPLWithExternal M x.drawing r hr) =
      Quotient.mk exteriorMarkedBallSetoid
        (d39FacedBallPLWithExternal N y.drawing r hr) := by
    apply Quotient.sound
    exact ⟨{ toD39BallIso := I
             external_iff := (plBallFaceOrbitMap_eq_iff I _ _).mp hOpen2 }⟩
  apply exteriorMarkedComparison_reparam_geomBallIso
    x.data y.data x.drawing y.drawing x.pos_eq y.pos_eq
    (fun d => ⟨Homeomorph.refl unitInterval, rfl, rfl,
      fun t => (x.arc_eq d t).symm⟩)
    (fun d => ⟨Homeomorph.refl unitInterval, rfl, rfl,
      fun t => (y.arc_eq d t).symm⟩) r hr hmarked

/-- Helper toward Proposition 5.9. The root-side incidence in each
restricted exterior suffices for OPEN 2 and hence OPEN 3. Neither a missing
tag nor an isomorphism of geometric balls is a premise: the root and edge
inverse fields identify the common dart used to transport the exterior. -/
theorem prop59_representedGeomBallIso_of_rootSide_mem
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B)
    (y : PLCylinderBall.Representation N C)
    (r : ℕ) (hr : 0 < r)
    (I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr))
    (hsideM : (d39FacedBall M r hr).map.edgeInv
        (d39FacedBall M r hr).rootDart ∈
      (d39FacedBallPLWithExternal M x.drawing r hr).externalOrbit.val)
    (hsideN : (d39FacedBall N r hr).map.edgeInv
        (d39FacedBall N r hr).rootDart ∈
      (d39FacedBallPLWithExternal N y.drawing r hr).externalOrbit.val) :
    Nonempty (D39GeomBallIsoV2 r B.map B.root C.map C.root) := by
  apply prop59_representedGeomBallIso_of_open2 x y r hr I
  apply (plBallFaceOrbitMap_eq_iff_exists_common_dart I _ _).mpr
  refine ⟨(d39FacedBall M r hr).map.edgeInv
    (d39FacedBall M r hr).rootDart, hsideM, ?_⟩
  rw [I.edgeInv_comm, I.root_comm]
  exact hsideN

/-- Helper toward Proposition 5.9. In the canonical assembly comparison,
only the second drawing's restricted root-side membership remains as an
exterior input. Its root-missing tag is transported by the faced-ball
isomorphism rather than assumed separately. -/
theorem prop59_canonicalAssembly_externalOrbit_eq_of_second_rootSide_mem
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (hhit : ∀ n, BoundaryHitWitnesses (shiftedStream W n))
    (C₀ : UIBHBOTCertifiedRootCapture W 0)
    (hrootAbsent : ¬ wholePlaneEdgePresent W (uibhbotRootEdge W))
    {N : D39RootedMap}
    (Q : PLDrawing N.core.D (RootedLocallyFiniteVertex N.core.D N.core.rot)
      N.core.edgeInv N.core.rot (d39VertexClass N))
    (r : ℕ) (hr : 0 < r)
    (I : D39BallIso (d39FacedBall
      (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap r hr)
      (d39FacedBall N r hr))
    (hsideN : (d39FacedBall N r hr).map.edgeInv
        (d39FacedBall N r hr).rootDart ∈
      (d39FacedBallPLWithExternal N Q r hr).externalOrbit.val) :
    plBallFaceOrbitMap I (d39FacedBallPLWithExternal
        (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
        (prop59_canonicalAssembly_reindexedDrawing W D hhit C₀) r hr).externalOrbit =
      (d39FacedBallPLWithExternal N Q r hr).externalOrbit := by
  have hroot := (prop59_canonicalAssembly_missingRootSide_mem_restrictedExternalOrbit
    W D hhit C₀ hrootAbsent r hr).1
  have hrootN : N.core.missing N.rootMark.dart := by
    change (d39FacedBall N r hr).missing (d39FacedBall N r hr).rootDart
    rw [← I.root_comm]
    exact (I.missing_iff _).mpr hroot
  exact prop59_canonicalAssembly_externalOrbit_eq_of_rootSide_mem
    W D hhit C₀ hrootAbsent Q r hr I hrootN hsideN

/-- Helper toward Proposition 5.9. Root absence is discharged on one conull
event, simultaneously for every canonical witness, second drawing, radius,
and faced-ball isomorphism. The sole remaining premise of this exterior
comparison is the second drawing's displayed geometric root-side incidence. -/
theorem prop59_canonicalAssembly_externalOrbit_reduction_ae :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (D : UIBHBOTD39CanonicalDomainWitness W)
        (hhit : ∀ n, BoundaryHitWitnesses (shiftedStream W n))
        (C₀ : UIBHBOTCertifiedRootCapture W 0)
        (N : D39RootedMap)
        (Q : PLDrawing N.core.D (RootedLocallyFiniteVertex N.core.D N.core.rot)
          N.core.edgeInv N.core.rot (d39VertexClass N))
        (r : ℕ) (hr : 0 < r)
        (I : D39BallIso (d39FacedBall
          (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
          r hr) (d39FacedBall N r hr)),
        (d39FacedBall N r hr).map.edgeInv (d39FacedBall N r hr).rootDart ∈
            (d39FacedBallPLWithExternal N Q r hr).externalOrbit.val →
          plBallFaceOrbitMap I (d39FacedBallPLWithExternal
              (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
              (prop59_canonicalAssembly_reindexedDrawing W D hhit C₀) r hr).externalOrbit =
            (d39FacedBallPLWithExternal N Q r hr).externalOrbit := by
  filter_upwards [prop59_uibhbotRootEdge_absent_ae] with W hrootAbsent
  intro D hhit C₀ N Q r hr I hsideN
  exact prop59_canonicalAssembly_externalOrbit_eq_of_second_rootSide_mem
    W D hhit C₀ hrootAbsent Q r hr I hsideN













































end DirectedDistances.PaperProofs.Section5

end
