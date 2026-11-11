/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516CanonicalClassRealization
public import DirectedDistances.Probability.BSLocalCylinderMeasurable
import all DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalClass

/-! Helper toward Proposition 5.16. The common geometric subspace consists exactly
of the finite exterior samples and the canonical source representatives on
the established conull code event. The observations retain the exterior mark.
The source-law interpretation F3 remains a coordinator decision. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section5.Prop516ExteriorAssembly4

open DirectedDistances.PlanarMap DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.Probability
open Prop516RootExteriorEncoding
open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- Helper toward Proposition 5.16: the actual finite and canonical source
representatives, with their already proved geometric construction witnesses. -/
inductive Source where
  /-- Helper toward Proposition 5.16: a finite disk sample with its exterior drawing. -/
  | finite (ell n : ℕ) (hell : 0 < ell)
      (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} × Fin ell)
      (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
      (U : P.Face) (hU : P.IsUnbounded U)
      (hborder : ∀ d, P.dartBorders d U ↔
        (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell p) n).IsOuter d)
  /-- Helper toward Proposition 5.16: a canonical representative on the source code event. -/
  | canonical (W : ℤ → Fin 3) (hW : W ∈ uibhbotRootedPlanarMapConullEvent)
      (D : UIBHBOTD39CanonicalDomainWitness W)

/-- Helper toward Proposition 5.16: the geometric domain of each actual source. -/
@[expose] def domain : Source → D39DomainRootedMapV2
  | .finite ell n hell p P U hU hborder =>
      diskSampleExteriorDomain ell n hell p P U hU hborder
  | .canonical W _ D => uibhbotD39CanonicalRepresentation13Domain W D

/-- Helper toward Proposition 5.16: the source combinatorial map. -/
@[expose] def codeMap : Source → D39RootedMap
  | .finite ell n hell p _ _ _ _ => diskRootedD39MapOfSample n ell hell p
  | .canonical W _ _ =>
      (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap

/-- Helper toward Proposition 5.16: the source's geometric quotient class. -/
@[expose] def classMap (s : Source) : D39GeomRootedMapClass :=
  PLCylinderBall.geometricClass (domain s)

/-- Helper toward Proposition 5.16: the source's marked positive-radius ball. -/
@[expose] def codeBall (r : ℕ) (s : Source) : ExteriorMarkedBallClass :=
  rootLift (d39BallClass (codeMap s) (r + 1) (Nat.succ_pos r))

private theorem representation (s : Source) :
    ∃ (M : D39RootedMap) (x : D39DrawingRepresentationData3 M (domain s))
      (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
        M.core.edgeInv M.core.rot (d39VertexClass M)),
      (∀ v, P.pos v = (domain s).map.toPlaneMapWithMissing.pos (x.vertexEquiv v)) ∧
      (∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, φ 0 = 0 ∧ φ 1 = 1 ∧
        ∀ t, d39DrawingDartArc (domain s) x.toD39DrawingRepresentationData d t =
          (P.arc d).toPath (φ t)) ∧
      (∀ r (hr : 0 < r), d39BallClass M r hr = d39BallClass (codeMap s) r hr) ∧
      (∀ r (hr : 0 < r), Quotient.mk exteriorMarkedBallSetoid
        (d39FacedBallPLWithExternal M P r hr) = rootLift (d39BallClass M r hr)) := by
  cases s with
  | finite ell n hell p P U hU hborder =>
    exact ⟨_, diskSampleExteriorData3 ell n hell p P U hU hborder,
      diskSampleRootedStagePLDrawing ell n hell p P, fun _ => rfl,
      diskSampleExteriorBase_dartArc_reparam ell n hell p P U hU hborder,
      fun _ _ => rfl,
      diskSampleExteriorMarkedBallClass_eq_rootLift ell n hell p P U hU hborder⟩
  | canonical W hW D =>
    obtain ⟨hhit, C, iso, x, hp, ha⟩ :=
      exteriorMarkedComparison_canonical_reparam_data W hW D
    exact ⟨_, x, exteriorMarkedComparison_canonicalDrawing W D hhit C, hp, ha,
      fun r hr => Quotient.sound ⟨iso.ballIso r hr⟩,
      exteriorMarkedComparison_canonicalDrawing_rootLift W D hhit C⟩

private theorem signed_face_unique (s : Source)
    (a : (domain s).E) (b : Bool)
    (F G : (domain s).map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
    (hF : if b then (domain s).map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf F a
      else (domain s).map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf F a)
    (hG : if b then (domain s).map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf G a
      else (domain s).map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf G a) : F = G := by
  cases s with
  | finite ell n hell p P U hU hborder =>
    exact diskSampleExteriorDomain_signed_face_unique ell n hell p P U hU hborder a b F G hF hG
  | canonical W hW D =>
    exact uibhbotCanonicalDomain_signed_face_unique W D a b F G hF hG

private theorem retained_assignment (s t : Source)
    {M N : D39RootedMap} {r : ℕ}
    (x : D39DrawingRepresentationData3 M (domain s))
    (y : D39DrawingRepresentationData3 N (domain t))
    (e : D39GeomBallIsoV2 r (domain s).map (domain s).root (domain t).map (domain t).root)
    (d : {d : M.core.D // d ∈ d39BallDarts M r})
    (hret : x.faceOfDart d.1 ∈ d39GeomRetainedFaces (domain s).map (domain s).root r) :
    (e.faceEquiv ⟨x.faceOfDart d.1, hret⟩).1 =
      y.faceOfDart (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d).1 := by
  have hs := d39DrawingRepresentationData3_geomBallIso_faceEquiv_imageSide x y e d hret
  apply signed_face_unique t _ _ _ _ hs.1
  have ht := hs.2.2
  rw [hs.2.1] at ht
  exact ht

private theorem original_iff (s t : Source)
    {M N : D39RootedMap} {r : ℕ}
    (x : D39DrawingRepresentationData3 M (domain s))
    (y : D39DrawingRepresentationData3 N (domain t))
    (e : D39GeomBallIsoV2 r (domain s).map (domain s).root (domain t).map (domain t).root)
    (d : {d : M.core.D // d ∈ d39BallDarts M r}) :
    d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d ∈
      (d39FacedBall N r e.radius_pos).original ↔
      d ∈ (d39FacedBall M r e.radius_pos).original := by
  let E := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e
  constructor
  · intro hd
    have hret := (d39DrawingRepresentationData3_original_iff_face_retained
      y r e.radius_pos (E d)).mp hd
    have heq := retained_assignment t s y x e.symm (E d) hret
    have hback : d39DrawingRepresentationData3_geomBallIso_ballDartEquiv
        y x e.symm (E d) = d := by
      rw [geomBallIso_ballDartEquiv_symm_apply]
      exact E.symm_apply_apply d
    rw [hback] at heq
    apply (d39DrawingRepresentationData3_original_iff_face_retained x r e.radius_pos d).mpr
    rw [← heq]
    exact (e.symm.faceEquiv ⟨y.faceOfDart (E d).1, hret⟩).property
  · intro hd
    have hret := (d39DrawingRepresentationData3_original_iff_face_retained
      x r e.radius_pos d).mp hd
    have heq := retained_assignment s t x y e d hret
    apply (d39DrawingRepresentationData3_original_iff_face_retained y r e.radius_pos (E d)).mpr
    rw [← heq]
    exact (e.faceEquiv ⟨x.faceOfDart d.1, hret⟩).property

/-- Helper toward Proposition 5.16: the full dyadic metric equivalence holds
for every pair of actual source representatives, including both within-family cases. -/
theorem source_hball (r : ℕ) (s t : Source) :
    edist (classMap s) (classMap t) ≤ (1 / 2 : ℝ≥0∞) ^ (r + 1) ↔
      codeBall r s = codeBall r t := by
  obtain ⟨M, x, P, hp, ha, hc, hm⟩ := representation s
  obtain ⟨N, y, Q, hq, hb, hd, hn⟩ := representation t
  constructor
  · intro h
    obtain ⟨e⟩ := (d39ClassDistance_le_pow_iff_nonempty (Nat.succ_pos r)
      (PLCylinderBall.domainMap (domain s)) (PLCylinderBall.domainMap (domain t))).mp h
    have hf := d39BallIso_of_geomBallIsoV2_of_original_iff (r + 1) (Nat.succ_pos r)
      x y e (original_iff s t x y e)
    have he : d39BallClass M (r + 1) (Nat.succ_pos r) =
        d39BallClass N (r + 1) (Nat.succ_pos r) := Quotient.sound hf
    exact congrArg rootLift ((hc _ _).symm.trans (he.trans (hd _ _)))
  · intro h
    have he : Quotient.mk exteriorMarkedBallSetoid
        (d39FacedBallPLWithExternal M P (r + 1) (Nat.succ_pos r)) =
      Quotient.mk exteriorMarkedBallSetoid
        (d39FacedBallPLWithExternal N Q (r + 1) (Nat.succ_pos r)) := by
      rw [hm, hn, hc, hd]
      exact h
    exact (d39ClassDistance_le_pow_iff_nonempty (Nat.succ_pos r) _ _).mpr
      (exteriorMarkedComparison_reparam_geomBallIso x y P Q hp hq ha hb
        (r + 1) (Nat.succ_pos r) he)

/-- Helper toward Proposition 5.16: the common geometric subspace is the
image of the two actual source families. -/
@[expose] def subspace : Set D39GeomRootedMapClass := range classMap

/-- Helper toward Proposition 5.16: each source gives a point of the common subspace. -/
@[expose] def toSubspace (s : Source) : subspace := ⟨classMap s, mem_range_self s⟩

/-- Helper toward Proposition 5.16: the marked observation on the common
subspace, characterized independently of the selected source representative below. -/
@[expose] def observation (r : ℕ) (x : subspace) : ExteriorMarkedBallClass :=
  codeBall r (Classical.choose x.property)

/-- Helper toward Proposition 5.16: every source representative has its
actual marked code ball as observation; the choice in observation is immaterial. -/
theorem observation_toSubspace (r : ℕ) (s : Source) :
    observation r (toSubspace s) = codeBall r s := by
  apply (source_hball r _ s).mp
  have he := Classical.choose_spec (toSubspace s).property
  change classMap (Classical.choose (toSubspace s).property) = classMap s at he
  rw [he, edist_self]
  exact bot_le

/-- Helper toward Proposition 5.16: the common subspace observations have
the exact dyadic-ball characterization required by the convergence assembly. -/
theorem hball (r : ℕ) (x y : subspace) :
    edist (x : D39GeomRootedMapClass) y ≤ (1 / 2 : ℝ≥0∞) ^ (r + 1) ↔
      observation r x = observation r y := by
  obtain ⟨s, hs⟩ := x.property
  obtain ⟨t, ht⟩ := y.property
  have hx : x = toSubspace s := Subtype.ext hs.symm
  have hy : y = toSubspace t := Subtype.ext ht.symm
  rw [hx, hy, observation_toSubspace, observation_toSubspace]
  exact source_hball r s t

/-- Helper toward Proposition 5.16: the local observation topology is exactly
the geometric subspace topology. -/
theorem topology_eq : localClassTopology observation =
    (inferInstance : TopologicalSpace subspace) :=
  localClassTopology_eq_induced observation hball
    (localClass_compatible_of_dyadic_ball observation hball)

/-- Helper toward Proposition 5.16: there is a measurable canonical map
into the common subspace, realizing the exact option class and all marked
cylinder identities simultaneously almost surely. -/
theorem exists_canonicalClass :
    letI : TopologicalSpace subspace := localClassTopology observation
    letI : MeasurableSpace subspace := borel subspace
    ∃ g : (ℤ → Fin 3) → subspace, Measurable g ∧
      ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
        (∃ hW : (uibhbotD39CanonicalClass W).isSome,
          (g W).val = (uibhbotD39CanonicalClass W).get hW) ∧
        ∀ r, observation r (g W) = rootLift (d39BallClass
          (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
          (r + 1) (Nat.succ_pos r)) := by
  classical
  let : TopologicalSpace subspace := localClassTopology observation
  let : MeasurableSpace subspace := borel subspace
  have ha := uibhbotRootedPlanarMapConullEvent_spec.2.1.and
    uibhbotCodeLawRel_ae_d39CanonicalDomainEvent
  obtain ⟨S, hSae, hS, hs⟩ := ha.exists_measurable_mem
  obtain ⟨W₀, hW₀⟩ :=
    (show ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), W ∈ S from hSae).exists
  let D (W : ℤ → Fin 3) (hW : W ∈ S) := Classical.choice (hs W hW).2
  let g₀ := toSubspace (.canonical W₀ (hs W₀ hW₀).1 (D W₀ hW₀))
  let g (W : ℤ → Fin 3) : subspace :=
    if hW : W ∈ S then toSubspace (.canonical W (hs W hW).1 (D W hW)) else g₀
  have hg (r : ℕ) :
      @Measurable _ ExteriorMarkedBallClass _ ⊤ (fun W => observation r (g W)) := by
    have he : (fun W => observation r (g W)) =
        S.piecewise (fun W => rootLift (d39BallClass
          (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
            (r + 1) (Nat.succ_pos r))) (fun _ => observation r g₀) := by
      funext W
      by_cases hW : W ∈ S
      · simp only [g, dite_eq_left hW, observation_toSubspace, codeBall, codeMap,
          piecewise, ite_eq_left hW]
      · simp only [g, dite_eq_right hW, piecewise, ite_eq_right hW]
    rw [he]
    exact (measurable_uibhbot_exteriorMarkedCode r).piecewise hS measurable_const
  refine ⟨g, (measurable_to_localClass_iff observation
    (localClass_compatible_of_dyadic_ball observation hball) g).mpr
      (fun r c => hg r (by trivial : @MeasurableSet ExteriorMarkedBallClass ⊤ {c})), ?_⟩
  filter_upwards [hSae] with W hW
  constructor
  · have he := uibhbotD39CanonicalClass_eq_some_domain W (D W hW)
    have hi : (uibhbotD39CanonicalClass W).isSome := by rw [he]; rfl
    refine ⟨hi, ?_⟩
    simp only [g, dite_eq_left hW, toSubspace, classMap, domain, he, Option.get_some]
  · intro r
    simp only [g, dite_eq_left hW, observation_toSubspace, codeBall, codeMap]

/-- Helper toward Proposition 5.16: finite samples have a measurable map
into the common subspace with their exact marked cylinders at every radius. -/
theorem exists_finiteSampleClass (ell n : ℕ) (hell : 0 < ell) :
    letI : MeasurableSpace
      {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    letI : TopologicalSpace subspace := localClassTopology observation
    letI : MeasurableSpace subspace := borel subspace
    ∃ f : ({q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) → subspace, Measurable f ∧
      (∀ p, ∃ (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
        (U : P.Face) (hU : P.IsUnbounded U)
        (hborder : ∀ d, P.dartBorders d U ↔
          (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell p) n).IsOuter d),
        f p = toSubspace (.finite ell n hell p P U hU hborder)) ∧
      ∀ p r, observation r (f p) = rootLift
        (d39BallClass (diskRootedD39MapOfSample n ell hell p) (r + 1) (Nat.succ_pos r)) := by
  classical
  let E := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) E
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  let : TopologicalSpace subspace := localClassTopology observation
  let : MeasurableSpace subspace := borel subspace
  choose P U hU hborder _ using diskSample_exists_exteriorData3 ell n hell
  let f := fun p => toSubspace (.finite ell n hell p (P p) (U p) (hU p) (hborder p))
  exact ⟨f, measurable_of_countable f,
    fun p => ⟨P p, U p, hU p, hborder p, rfl⟩,
    fun p r => observation_toSubspace r _⟩

/-- Helper toward Proposition 5.16: finite geometric realizations descend
measurably to the intermediate planar-map carrier for all cylinder tests.
Every actual sample has its exact observations, and hence so does its law. -/
theorem exists_finiteClass (ell n : ℕ) (hell : 0 < ell) :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap := borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    letI : TopologicalSpace subspace := localClassTopology observation
    letI : MeasurableSpace subspace := borel subspace
    ∃ f : RootedLocallyFinitePlanarMap → subspace, Measurable f ∧
      (∀ (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} × Fin ell)
        (r : ℕ), observation r (f (diskRootedPlanarMapOfSample n ell hell p)) =
          rootLift (d39BallClass (diskRootedD39MapOfSample n ell hell p)
            (r + 1) (Nat.succ_pos r))) ∧
      ∀ (hle : ell ≤ n) (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q),
        ∀ᵐ M ∂((diskRootedPlanarMapLaw n ell hell hle hmod) : Measure RootedLocallyFinitePlanarMap),
          ∀ r, observation r (f M) = rootLift (d39RootedBallSystem.ballClass r
            M.toRootedLocallyFiniteMap.toD39RootedMap) := by
  classical
  let : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  let : MeasurableSpace RootedLocallyFinitePlanarMap := borel RootedLocallyFinitePlanarMap
  let : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  let : TopologicalSpace subspace := localClassTopology observation
  let : MeasurableSpace subspace := borel subspace
  let : TopologicalSpace D39RootedMap := bsLocalDistanceTopologyGeneric d39RootedBallSystem
  let : MeasurableSpace D39RootedMap := borel D39RootedMap
  let : BorelSpace D39RootedMap := ⟨rfl⟩
  let : MeasurableSpace ExteriorMarkedBallClass := ⊤
  let E := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) E
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  let j := diskRootedPlanarMapOfSample n ell hell
  let β (r : ℕ) (M : RootedLocallyFinitePlanarMap) :=
    rootLift (d39RootedBallSystem.ballClass r M.toRootedLocallyFiniteMap.toD39RootedMap)
  have hβ (r : ℕ) : Measurable (β r) :=
    measurable_rootLift.comp
      ((measurable_into_iff_ballClass_generic d39RootedBallSystem _).mp
        measurable_toD39RootedMap r)
  obtain ⟨f₀, _, _, hf₀⟩ := exists_finiteSampleClass ell n hell
  obtain ⟨g, _, _⟩ := exists_canonicalClass
  let c₀ := g (fun _ => 0)
  let S : Set RootedLocallyFinitePlanarMap :=
    {M | ∃ p : Q × Fin ell, ∀ r, β r M = β r (j p)}
  have hS : MeasurableSet S := by
    simp only [S, ofPred_exists, ofPred_forall]
    exact MeasurableSet.iUnion fun p => MeasurableSet.iInter fun r =>
      hβ r (MeasurableSet.singleton (β r (j p)))
  let f (M : RootedLocallyFinitePlanarMap) : subspace :=
    if hM : M ∈ S then f₀ (Classical.choose hM) else c₀
  have hon (M : RootedLocallyFinitePlanarMap) (hM : M ∈ S) (r : ℕ) :
      observation r (f M) = β r M := by
    simp only [f, dite_eq_left hM]
    exact (hf₀ _ r).trans ((Classical.choose_spec hM r).symm)
  have hcoord (r : ℕ) : Measurable (fun M => observation r (f M)) := by
    have he : (fun M => observation r (f M)) =
        S.piecewise (β r) (fun _ => observation r c₀) := by
      funext M
      by_cases hM : M ∈ S
      · simpa only [piecewise, ite_eq_left hM] using hon M hM r
      · simp only [f, dite_eq_right hM, piecewise, ite_eq_right hM]
    rw [he]
    exact (hβ r).piecewise hS measurable_const
  have hf : Measurable f := (measurable_to_localClass_iff observation
    (localClass_compatible_of_dyadic_ball observation hball) f).mpr
      (fun r c => hcoord r (MeasurableSet.singleton c))
  have hj (p : Q × Fin ell) : j p ∈ S := ⟨p, fun _ => rfl⟩
  refine ⟨f, hf, fun p r => hon (j p) (hj p) r, ?_⟩
  intro hle hmod
  have hsae : ∀ᵐ M ∂((diskRootedPlanarMapLaw n ell hell hle hmod) :
      Measure RootedLocallyFinitePlanarMap), M ∈ S := by
    rw [diskRootedPlanarMapLaw_toMeasure]
    exact (ae_map_iff (measurable_diskRootedPlanarMapOfSample n ell hell).aemeasurable hS).mpr
      (Eventually.of_forall hj)
  filter_upwards [hsae] with M hM
  exact hon M hM

/-- Helper toward Proposition 5.16: all geometric subspace and cylinder
inputs can be instantiated, giving weak convergence to the explicit canonical
code pushforward. Identifying this limit with the paper's law is F3 and is
not asserted here. -/
theorem exists_geometric_pushforward_convergence
    (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ)) :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap := borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
    letI : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
    letI : TopologicalSpace subspace := localClassTopology observation
    letI : MeasurableSpace subspace := borel subspace
    letI : BorelSpace subspace := ⟨rfl⟩
    ∃ (f : ℕ → RootedLocallyFinitePlanarMap → subspace) (g : (ℤ → Fin 3) → subspace),
      (∀ k, Measurable (f k)) ∧ Measurable g ∧
      (∀ k, ∀ᵐ M ∂((diskRootedPlanarMapLaw (k + 1) (ell k)
          (hadm k).1 (hadm k).2.1 (hadm k).2.2) : Measure RootedLocallyFinitePlanarMap),
        ∀ r, observation r (f k M) = rootLift (d39RootedBallSystem.ballClass r
          M.toRootedLocallyFiniteMap.toD39RootedMap)) ∧
      (∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
        (∃ hW : (uibhbotD39CanonicalClass W).isSome,
          (g W).val = (uibhbotD39CanonicalClass W).get hW) ∧
        ∀ r, observation r (g W) = rootLift (d39RootedBallSystem.ballClass r
          (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap)) ∧
      Tendsto (fun k =>
        ((diskRootedPlanarMapLaw (k + 1) (ell k)
          (hadm k).1 (hadm k).2.1 (hadm k).2.2).map (f k)).map Subtype.val)
        atTop (𝓝 ((uibhbotCodeLawRel.map g).map Subtype.val)) := by
  classical
  let : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  let : MeasurableSpace RootedLocallyFinitePlanarMap := borel RootedLocallyFinitePlanarMap
  let : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  let : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
  let : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
  let : TopologicalSpace subspace := localClassTopology observation
  let : MeasurableSpace subspace := borel subspace
  let : BorelSpace subspace := ⟨rfl⟩
  choose f hf _ hfc using fun k => exists_finiteClass (ell k) (k + 1) (hadm k).1
  obtain ⟨g, hg, hgc⟩ := exists_canonicalClass
  refine ⟨f, g, hf, hg, fun k => hfc k (hadm k).2.1 (hadm k).2.2, hgc, ?_⟩
  apply exteriorMarked_geometricClassLaw_tendsto_of_inputs
    A hA ell hadm hlo hhi subspace observation hball f g
    ((uibhbotCodeLawRel.map g).map Subtype.val) hf hg
  · intro k r
    filter_upwards [hfc k (hadm k).2.1 (hadm k).2.2] with M hM
    exact hM r
  · intro r
    filter_upwards [hgc] with W hW
    exact hW.2 r
  · rfl

/- REMAINDER: F3 (coordinator/source-law decision, not a theorem assumed here).
All subspace, topology, measurability and cylinder inputs of Assembly2:137
are instantiated above. The explicit code-pushforward limit is proved.
To identify it with a source-named law requires the following equation,
under the displayed full binders and Borel instances:

letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
letI : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
(F : (ℤ → Fin 3) → D39GeomRootedMapClass)
(hFmeas : Measurable F)
(hFcanon : ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
  ∃ hW : (uibhbotD39CanonicalClass W).isSome,
    F W = (uibhbotD39CanonicalClass W).get hW)
(definition58GeometricClassLaw : ProbabilityMeasure D39GeomRootedMapClass)

  definition58GeometricClassLaw = uibhbotCodeLawRel.map F

The law binder must first receive its source interpretation from the
coordinator. The equation is not true for an arbitrary probability measure,
and is neither a theorem nor a premise in this file. The uniqueness theorem
uibhbotCanonical_realization_map_unique makes the right side independent of
the measurable total representative. No source-law definition is introduced.
The stronger universal finite-window locality and global Option-measurability
separate kernel validation remain with the coordinator; no paper count changes. -/

end DirectedDistances.PaperProofs.Section5.Prop516ExteriorAssembly4
end

