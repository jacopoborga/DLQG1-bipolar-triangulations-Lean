module
public import Palomar.Principal.Busemann.Solution
public import DirectedDistances.Paper.Section5.UIHBOTSym

@[expose] public section
noncomputable section
namespace DLQG1.Palomar.GeometryInterface
open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section5
open scoped ENNReal Topology

abbrev related (A B : D39DomainRootedMap.{0}) : Prop :=
  Nonempty (D39GeomRootedMapIsoV2 A.map A.root B.map B.root)
theorem related_equivalence : Equivalence related := by
  change Equivalence d39DomainSetoid.r
  exact d39DomainSetoid.iseqv
abbrev domainSetoid : Setoid D39DomainRootedMap.{0} where
  r := related
  iseqv := related_equivalence
abbrev MapClass := Quotient domainSetoid
theorem domainSetoid_eq_source : domainSetoid = d39DomainSetoid := rfl
theorem carrier_eq_source : MapClass = D39GeomRootedMapClass.{0} := rfl

theorem distance_respects :
    ∀ A B A' B' : D39DomainRootedMap.{0},
      related A A' → related B B' →
      d39GeomDistanceV2 A.map A.root B.map B.root =
        d39GeomDistanceV2 A'.map A'.root B'.map B'.root := by
  rintro A B A' B' ⟨eA⟩ ⟨eB⟩
  exact eA.d39GeomDistanceV2_congr_left.trans eB.d39GeomDistanceV2_congr_right
abbrev distance (c d : MapClass) : ℝ≥0∞ :=
  Quotient.liftOn₂ c d
    (fun A B => d39GeomDistanceV2 A.map A.root B.map B.root) distance_respects
theorem distance_eq_source : distance = d39ClassDistance := rfl
theorem distance_self (c : MapClass) : distance c c = 0 :=
  d39ClassDistance_self c
theorem distance_comm (c d : MapClass) : distance c d = distance d c :=
  d39ClassDistance_comm c d
theorem distance_triangle (c d e : MapClass) :
    distance c e ≤ distance c d + distance d e := d39ClassDistance_triangle c d e

abbrev metric : PseudoEMetricSpace MapClass where
  edist := distance
  edist_self := distance_self
  edist_comm := distance_comm
  edist_triangle := distance_triangle
theorem metric_eq_source :
    metric = (inferInstance : PseudoEMetricSpace D39GeomRootedMapClass.{0}) := rfl
abbrev topology : TopologicalSpace MapClass :=
  metric.toUniformSpace.toTopologicalSpace
theorem topology_eq_source :
    topology = (inferInstance : TopologicalSpace D39GeomRootedMapClass.{0}) := rfl

theorem mirrorMap_external {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) :
    ∀ e, M.toPlaneMapWithMissing.missing e →
      ∃ F : (PlaneGraphDrawing.geomMirror M.toPlaneGraphDrawing).Face,
        (PlaneGraphDrawing.geomMirror M.toPlaneGraphDrawing).IsExternal F ∧
        Set.range ((PlaneGraphDrawing.geomMirror M.toPlaneGraphDrawing).arc e) ⊆
          closure F.1 :=
  M.geomMirror.missing_on_external
def mirrorMap {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) : DirectedPlaneMapWithMissing V E where
  toPlaneMapWithMissing := {
    toPlaneGraphDrawing := PlaneGraphDrawing.geomMirror M.toPlaneGraphDrawing
    missing := M.toPlaneMapWithMissing.missing
    missing_on_external := mirrorMap_external M }
  forward := M.forward
theorem mirrorMap_eq_source {V E : Type*} (M : DirectedPlaneMapWithMissing V E) :
    mirrorMap M = M.geomMirror := rfl
theorem mirrorDomainValid (A : D39DomainRootedMap.{0})
    (hm : A.map.toPlaneMapWithMissing.missing A.root.1) :
    D39GeomDomain (mirrorMap A.map) (d39GeomMirrorRoot A.root) :=
  A.domain.geomMirror hm
def domainMirror (A : D39DomainRootedMap.{0}) : D39DomainRootedMap.{0} := by
  classical
  exact if hm : A.map.toPlaneMapWithMissing.missing A.root.1 then
    { V := A.V, E := A.E, map := mirrorMap A.map,
      root := d39GeomMirrorRoot A.root, domain := mirrorDomainValid A hm } else A
theorem domainMirror_eq_source : domainMirror = prop59GeometricDomainMirror := rfl
theorem mirror_respects : ∀ A B : D39DomainRootedMap.{0},
    related A B → related (domainMirror A) (domainMirror B) := by
  intro A B h
  apply Quotient.exact (s := d39DomainSetoid)
  exact congrArg prop59GeometricClassMirror (Quotient.sound h)
def mirror : MapClass → MapClass := Quotient.map domainMirror mirror_respects
theorem mirror_eq_source : mirror = prop59GeometricClassMirror := rfl

def classOf (B : DirectedDistances.PaperProofs.SourceResults.D39DomainRootedMapV2.{0}) :
    MapClass :=
  Quotient.mk domainSetoid ⟨B.V, B.E, B.map, B.root, B.domain⟩
theorem classOf_eq_source :
    classOf = DirectedDistances.PaperProofs.Section5.PLCylinderBall.geometricClass := rfl

end DLQG1.Palomar.GeometryInterface

attribute [local instance] DLQG1.Palomar.GeometryInterface.metric DLQG1.Palomar.GeometryInterface.topology

@[expose] public section
noncomputable section
namespace DLQG1.Palomar.HalfPlaneCode
open DirectedDistances.PlanarMap DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.SourceResults
def rootDart (W : ℤ → Fin 3) : DLQG1.Palomar.Model.KMSW.WholePlaneDart W :=
  DLQG1.Palomar.Model.KMSW.wholePlaneDartι W 1 (kmswLLCreatedEdge (shiftedStream W 1) 1, false)
def outerDart (W : ℤ → Fin 3) : DLQG1.Palomar.Model.KMSW.WholePlaneDart W :=
  DLQG1.Palomar.Model.KMSW.wholePlaneDartFlip W (rootDart W)
/-- A full dart encoding of the concrete code graph, including rotation,
missing edges, directions, the marked outer face and ordered missing root. -/
def IsCodeMap (W : ℤ → Fin 3) (H : DLQG1.Palomar.Model.KMSW.WholePlaneRotationHypothesis W)
    (M : D39RootedMap) : Prop :=
  ∃ e : M.core.D ≃ DLQG1.Palomar.Model.KMSW.WholePlaneDart W,
    (∀ d, e (M.core.rot d) = DLQG1.Palomar.Model.KMSW.wholePlaneRotation W H (e d)) ∧
    (∀ d, e (M.core.edgeInv d) = DLQG1.Palomar.Model.KMSW.wholePlaneDartFlip W (e d)) ∧
    (∀ d, M.core.missing d ↔ ¬ DLQG1.Palomar.Model.KMSW.wholePlaneEdgePresent W (e d).1) ∧
    (∀ d, M.core.tail d ↔ DLQG1.Palomar.Model.KMSW.wholePlaneDartTail W (e d)) ∧
    e M.core.outer = outerDart W ∧
    e M.rootMark.dart = rootDart W ∧
    M.core.missing M.rootMark.dart

theorem codeMaps_iso {W : ℤ → Fin 3} {H : DLQG1.Palomar.Model.KMSW.WholePlaneRotationHypothesis W}
    {M N : D39RootedMap} (hM : IsCodeMap W H M) (hN : IsCodeMap W H N) :
    Nonempty (D39RootedMapIso M N) := by
  obtain ⟨e, er, ei, em, et, _eo, eRoot, _emRoot⟩ := hM
  obtain ⟨f, fr, fi, fm, ft, _fo, fRoot, _fmRoot⟩ := hN
  let g := e.trans f.symm
  have hg (d : M.core.D) : f (g d) = e d := f.apply_symm_apply (e d)
  refine ⟨{
    toEquiv := g
    rot_comm := ?_
    edgeInv_comm := ?_
    missing_iff := ?_
    tail_iff := ?_
    root_dart_comm := ?_ }⟩
  · intro d
    apply f.injective
    rw [hg, er, fr, hg]
  · intro d
    apply f.injective
    rw [hg, ei, fi, hg]
  · intro d
    rw [fm, hg]
    exact (em d).symm
  · intro d _hd
    rw [ft, hg]
    exact (et d).symm
  · apply f.injective
    rw [hg, fRoot, eRoot]

theorem canonical_codeMap (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C : UIBHBOTCertifiedRootCapture W 0) :
    IsCodeMap W ((DLQG1.Palomar.Model.KMSW.rotationHyp_iff_source W).mpr H)
      (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C).toD39RootedMap := by
  let h := (DLQG1.Palomar.Model.KMSW.rotationHyp_iff_source W).mpr H
  let f := DLQG1.Palomar.Model.KMSW.sourceDartEquiv W
  have hr : f (rootDart W) = uibhbotWholePlaneRootDart W :=
    DLQG1.Palomar.Model.KMSW.sourceDartEquiv_ι W 1 (kmswLLCreatedEdge (shiftedStream W 1) 1, false)
  refine ⟨f.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    change WholePlaneDart W at d
    apply f.injective
    change f (f.symm (wholePlaneRotation W H d)) =
      f (DLQG1.Palomar.Model.KMSW.wholePlaneRotation W h (f.symm d))
    dsimp only [f]
    rw [Equiv.apply_symm_apply, DLQG1.Palomar.Model.KMSW.sourceDartEquiv_rotation, Equiv.apply_symm_apply]
  · intro d
    change WholePlaneDart W at d
    apply f.injective
    change f (f.symm (wholePlaneDartFlip W d)) =
      f (DLQG1.Palomar.Model.KMSW.wholePlaneDartFlip W (f.symm d))
    dsimp only [f]
    rw [Equiv.apply_symm_apply, DLQG1.Palomar.Model.KMSW.sourceDartEquiv_flip, Equiv.apply_symm_apply]
  · intro d
    change WholePlaneDart W at d
    obtain ⟨x, rfl⟩ := f.surjective d
    change (¬ wholePlaneEdgePresent W (f x).1) ↔
      ¬ DLQG1.Palomar.Model.KMSW.wholePlaneEdgePresent W (f.symm (f x)).1
    rw [Equiv.symm_apply_apply, DLQG1.Palomar.Model.KMSW.sourceDartEquiv_fst]
    exact (not_congr (DLQG1.Palomar.Model.KMSW.sourceEdgeEquiv_present W x.1)).symm
  · intro d
    change WholePlaneDart W at d
    obtain ⟨x, rfl⟩ := f.surjective d
    change wholePlaneDartTail W (f x) ↔
      DLQG1.Palomar.Model.KMSW.wholePlaneDartTail W (f.symm (f x))
    rw [Equiv.symm_apply_apply]
    change (¬ (f x).2 ∧ wholePlaneEdgePresent W (f x).1) ↔
      (¬ x.2 ∧ DLQG1.Palomar.Model.KMSW.wholePlaneEdgePresent W x.1)
    rw [DLQG1.Palomar.Model.KMSW.sourceDartEquiv_snd, DLQG1.Palomar.Model.KMSW.sourceDartEquiv_fst]
    exact and_congr Iff.rfl (DLQG1.Palomar.Model.KMSW.sourceEdgeEquiv_present W x.1).symm
  · apply f.injective
    change f (f.symm (uibhbotWholePlaneOuterDart W)) = f (outerDart W)
    rw [Equiv.apply_symm_apply]
    change wholePlaneDartFlip W (uibhbotWholePlaneRootDart W) =
      f (DLQG1.Palomar.Model.KMSW.wholePlaneDartFlip W (rootDart W))
    rw [DLQG1.Palomar.Model.KMSW.sourceDartEquiv_flip, hr]
  · apply f.injective
    change f (f.symm (uibhbotWholePlaneFrameEdgeDart W)) = f (rootDart W)
    rw [Equiv.apply_symm_apply, hr]
    rfl
  · exact (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C).frameEdge_missing
end DLQG1.Palomar.HalfPlaneCode

namespace DLQG1.Palomar.GeometryLawMinimal
open DirectedDistances.PlanarMap DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section5.Prop516ExteriorAssembly6
open MeasureTheory Set Filter
open DLQG1.Palomar.HalfPlaneCode
open scoped ENNReal Topology

local instance lawMeasurable : MeasurableSpace DLQG1.Palomar.GeometryInterface.MapClass :=
  borel DLQG1.Palomar.GeometryInterface.MapClass
local instance lawBorel : BorelSpace DLQG1.Palomar.GeometryInterface.MapClass := ⟨rfl⟩

/-- A concrete realization of the actual code graph, with its rotation,
directions, missing tags, ordered root, faces and an endpoint-preserving
piecewise-linear reparameterization witness. The marked root-side orbit is
infinite, as proved for the actual half-plane source. -/
def RealizesCode (W : ℤ → Fin 3) (c : DLQG1.Palomar.GeometryInterface.MapClass) : Prop :=
  ∃ (H : DLQG1.Palomar.Model.KMSW.WholePlaneRotationHypothesis W)
    (M : D39RootedMap), IsCodeMap W H M ∧
    ∃ (B : D39DomainRootedMapV2.{0}) (x : D39DrawingRepresentationData3 M B)
      (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
        M.core.edgeInv M.core.rot (d39VertexClass M)),
      B.map.toPlaneMapWithMissing.missing B.root.1 ∧
      (∀ v, P.pos v = B.map.toPlaneMapWithMissing.pos (x.vertexEquiv v)) ∧
      (∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, φ 0 = 0 ∧ φ 1 = 1 ∧
        ∀ t, d39DrawingDartArc B x.toD39DrawingRepresentationData d t =
          (P.arc d).toPath (φ t)) ∧
      {d | Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv)
        (M.core.edgeInv M.rootMark.dart) d}.Infinite ∧
      c = DLQG1.Palomar.GeometryInterface.classOf B
/-- The actual canonical source has this concrete realization almost surely;
no new PL hypothesis is imposed on the source geometry. -/
theorem canonical_realizesCode_ae :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      RealizesCode W (canonicalGeometricClass W) := by
  filter_upwards [prop59_mirrorRep_canonicalRepresentation_ae,
    canonicalGeometricClass_spec, uibhbotRootedPlanarMapConullEvent_spec.2.1]
    with W hw hc hW
  obtain ⟨H, h0, hL, hR, hfin, hRpos, hA, hmirror, canonical⟩ := hw
  let D : UIBHBOTD39CanonicalDomainWitness W := ⟨H, h0, hL, hR, hfin, hRpos, hA⟩
  let B := uibhbotD39CanonicalRepresentation13Domain W D
  have hm : B.map.toPlaneMapWithMissing.missing B.root.1 :=
    hA.geomMirror_iff_missing.mp hmirror
  have he : canonicalGeometricClass W = DLQG1.Palomar.GeometryInterface.classOf B := by
    rw [DLQG1.Palomar.GeometryInterface.classOf_eq_source]
    obtain ⟨hs, he⟩ := hc
    simpa only [uibhbotD39CanonicalClass_eq_some_domain W D, Option.get_some] using he
  obtain ⟨hhit, C₀, iso, x, hp, ha⟩ :=
    exteriorMarkedComparison_canonical_reparam_data W hW D
  let M := uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀
  let P := exteriorMarkedComparison_canonicalDrawing W D hhit C₀
  have hM : {d | Equiv.Perm.SameCycle (M.rot.symm * M.edgeInv)
      (M.edgeInv M.frameEdgeDart) d}.Infinite :=
    prop59_canonical_outerOrbit_infinite W H h0 hL hR hfin hRpos
  exact ⟨(DLQG1.Palomar.Model.KMSW.rotationHyp_iff_source W).mpr H,
    M.toD39RootedMap, canonical_codeMap W H hhit C₀, B, x, P, hm, hp, ha, hM, he⟩

/-- Any two actual realizations of the same source code have zero geometric
distance. This asserts Borel indistinguishability, not global class equality. -/
theorem realizesCode_edist_zero {W : ℤ → Fin 3}
    {c d : DLQG1.Palomar.GeometryInterface.MapClass}
    (hc : RealizesCode W c) (hd : RealizesCode W d) : edist c d = 0 := by
  obtain ⟨H, M, hMap, B, x, P, _, hp, ha, hM, rfl⟩ := hc
  obtain ⟨H', N, hMap', C, y, Q, _, hq, hb, hN, rfl⟩ := hd
  have hH : H' = H := Subsingleton.elim _ _
  cases hH
  obtain ⟨I⟩ := codeMaps_iso hMap hMap'
  exact represented_edist_zero_of_infinite_rootSideOrbit x y P Q hp hq ha hb I hM hN
/-- Full pushforward law uniqueness for measurable actual code realizations. -/
theorem realization_pushforward_unique
    (f g : (ℤ → Fin 3) → DLQG1.Palomar.GeometryInterface.MapClass)
    (hf : Measurable f) (hg : Measurable g)
    (hfc : ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), RealizesCode W (f W))
    (hgc : ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), RealizesCode W (g W)) :
    uibhbotCodeLawRel.map f = uibhbotCodeLawRel.map g := by
  apply ProbabilityMeasure.toMeasure_injective
  apply map_eq_of_ae_edist_zero hf.aemeasurable hg.aemeasurable
  filter_upwards [hfc, hgc] with W hWf hWg
  exact realizesCode_edist_zero hWf hWg

/-- A source law is a Borel pushforward of the actual conditioned code law
under a measurable concrete realization. No desired symmetry or limit is part
of this definition. -/
def IsSourceLaw (μ : ProbabilityMeasure DLQG1.Palomar.GeometryInterface.MapClass) : Prop :=
  ∃ f : (ℤ → Fin 3) → DLQG1.Palomar.GeometryInterface.MapClass,
    Measurable f ∧
    (∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), RealizesCode W (f W)) ∧
    μ = uibhbotCodeLawRel.map f

/-- The actual Definition5.8 source law satisfies the full realization predicate. -/
theorem sourceLaw_realizes : IsSourceLaw uibhbotSourceGeometricClassLaw := by
  exact ⟨canonicalGeometricClass, measurable_canonicalGeometricClass,
    canonical_realizesCode_ae, uibhbotSourceGeometricClassLaw_eq_canonicalCodePushforward⟩

/-- The concrete realization characterization determines exactly one Borel
probability law, without asserting unique whole-map geometric classes. -/
theorem existsUnique_sourceLaw :
    ∃! μ : ProbabilityMeasure DLQG1.Palomar.GeometryInterface.MapClass, IsSourceLaw μ := by
  refine ⟨uibhbotSourceGeometricClassLaw, sourceLaw_realizes, ?_⟩
  intro μ hμ
  obtain ⟨f, hf, hfc, rfl⟩ := hμ
  rw [uibhbotSourceGeometricClassLaw_eq_canonicalCodePushforward]
  exact realization_pushforward_unique f canonicalGeometricClass hf
    measurable_canonicalGeometricClass hfc canonical_realizesCode_ae

/-- The uniquely characterized Borel law of the concrete conditioned-code geometry. -/
def sourceLaw : ProbabilityMeasure DLQG1.Palomar.GeometryInterface.MapClass :=
  Classical.choose existsUnique_sourceLaw.exists
theorem sourceLaw_spec : IsSourceLaw sourceLaw :=
  Classical.choose_spec existsUnique_sourceLaw.exists
theorem sourceLaw_eq_source : sourceLaw = uibhbotSourceGeometricClassLaw := by
  obtain ⟨μ, hμ, huniq⟩ := existsUnique_sourceLaw
  exact (huniq sourceLaw sourceLaw_spec).trans (huniq _ sourceLaw_realizes).symm

end DLQG1.Palomar.GeometryLawMinimal

