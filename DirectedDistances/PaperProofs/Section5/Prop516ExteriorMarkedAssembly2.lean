/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516ExteriorMarkedComparison2
public import DirectedDistances.PaperProofs.Section5.Prop516ExteriorMarkedAssembly

/-! Measurability and convergence transport through reversed-root marking.
The final assembly is a conditional criterion with all source-realization,
subspace-observation and geometric-law inputs displayed explicitly. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open DirectedDistances.Probability
open Prop516RootExteriorEncoding
open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology ENNReal

/-- Helper toward Proposition 5.16: reversed-root lifting is measurable for
the discrete sigma algebras on the countable ball-class carriers. -/
theorem measurable_rootLift :
    @Measurable D39BallClass ExteriorMarkedBallClass ⊤ ⊤ rootLift :=
  fun _ _ => trivial

/-- Helper toward Proposition 5.16: forgetting an exterior marker is
measurable for the discrete ball-class sigma algebras. -/
theorem measurable_exteriorMarked_forget :
    @Measurable ExteriorMarkedBallClass D39BallClass ⊤ ⊤
      ExteriorMarkedBallClass.forget := fun _ _ => trivial

/-- Helper toward Proposition 5.16: projection and lifting preserve and
reflect measurability of every ball observation on any measurable source. -/
theorem measurable_rootLift_comp_iff {X : Type*} [MeasurableSpace X]
    (b : X → D39BallClass) :
    @Measurable X ExteriorMarkedBallClass _ ⊤ (fun x => rootLift (b x)) ↔
      @Measurable X D39BallClass _ ⊤ b := by
  constructor
  · intro h
    have hf := measurable_exteriorMarked_forget.comp h
    simpa only [Function.comp_def, rootLift_forget] using hf
  · exact fun h => measurable_rootLift.comp h

/-- Helper toward Proposition 5.16: canonical marked code observations are
measurable at every positive radius, with no selection of a geometric witness. -/
theorem measurable_uibhbot_exteriorMarkedCode (r : ℕ) :
    letI : MeasurableSpace ExteriorMarkedBallClass := ⊤
    Measurable (fun W : ℤ → Fin 3 => rootLift (d39BallClass
      (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
      (r + 1) (Nat.succ_pos r))) := by
  exact (measurable_rootLift_comp_iff _).mpr (measurable_uibhbotD39BallClass r)

/-- Helper toward Proposition 5.16: every geometric class map on the finite
sample carrier is measurable for its actual discrete sampling sigma algebra.
This applies to any choice of the proved exterior realizations. -/
theorem measurable_diskSample_geometricClassMap
    (ell n : ℕ) (hell : 0 < ell)
    (f : ({q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) → D39GeomRootedMapClass) :
    letI : MeasurableSpace
      {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
    Measurable f := by
  let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  let : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
  exact measurable_of_countable f

/-- Helper toward Proposition 5.16: the exterior construction supplies a
measurable geometric realization of every finite sample, with its complete
source witnesses; no stronger stage geometry certificate is required. -/
theorem exists_measurable_diskSample_exteriorClass
    (ell n : ℕ) (hell : 0 < ell) :
    letI : MeasurableSpace
      {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    letI : MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
    ∃ f : ({q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
        Fin ell) → D39GeomRootedMapClass.{0},
      Measurable f ∧ ∀ p,
        ∃ (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
          (U : P.Face) (hU : P.IsUnbounded U)
          (hborder : ∀ d, P.dartBorders d U ↔
            (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell p) n).IsOuter d),
          f p = PLCylinderBall.geometricClass
            (diskSampleExteriorDomain ell n hell p P U hU hborder) := by
  let : MeasurableSpace
      {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  let : MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
  choose P U hU hborder hdata using diskSample_exists_exteriorData3 ell n hell
  let f := fun p => PLCylinderBall.geometricClass
    (diskSampleExteriorDomain ell n hell p (P p) (U p) (hU p) (hborder p))
  exact ⟨f, measurable_diskSample_geometricClassMap ell n hell f,
    fun p => ⟨P p, U p, hU p, hborder p, rfl⟩⟩

/-- Helper toward Proposition 5.16: the actual exterior-marked sample ball
map is measurable for every selection of its certified stage drawings. -/
theorem measurable_diskSample_exteriorMarkedClass
    (ell n : ℕ) (hell : 0 < ell)
    (P : ∀ p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell, StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (r : ℕ) (hr : 0 < r) :
    letI : MeasurableSpace
      {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    letI : MeasurableSpace ExteriorMarkedBallClass := ⊤
    @Measurable _ ExteriorMarkedBallClass _ ⊤ (fun p => (Quotient.mk exteriorMarkedBallSetoid
      (d39FacedBallPLWithExternal (diskRootedD39MapOfSample n ell hell p)
        (diskSampleRootedStagePLDrawing ell n hell p (P p)) r hr) :
        ExteriorMarkedBallClass)) := by
  let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  let : MeasurableSpace ExteriorMarkedBallClass := ⊤
  exact measurable_of_countable _

/-- Helper toward Proposition 5.16: marked cylinder convergence yields
geometric weak convergence on any source-realized subspace whose marked
observations describe the induced local topology topology. Every realization,
measurability, cylinder and Definition 5.8 law input remains explicit. -/
theorem exteriorMarked_geometricClassLaw_tendsto_of_inputs
    (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ))
    (S : Set D39GeomRootedMapClass)
    (b : ℕ → S → ExteriorMarkedBallClass)
    (hball : ∀ r (x y : S),
      edist (x : D39GeomRootedMapClass) y ≤ (1 / 2 : ℝ≥0∞) ^ (r + 1) ↔
        b r x = b r y) :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    letI : TopologicalSpace D39RootedMap :=
      bsLocalDistanceTopologyGeneric d39RootedBallSystem
    letI : MeasurableSpace D39RootedMap := borel D39RootedMap
    letI : BorelSpace D39RootedMap := ⟨rfl⟩
    letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
    letI : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
    letI : TopologicalSpace S := localClassTopology b
    letI : MeasurableSpace S := borel S
    letI : BorelSpace S := ⟨rfl⟩
    ∀ (finiteClass : ℕ → RootedLocallyFinitePlanarMap → S)
      (canonicalClass : (ℤ → Fin 3) → S)
      (geometricUIBHBOTLaw : ProbabilityMeasure D39GeomRootedMapClass)
      (_hfiniteMeas : ∀ k, Measurable (finiteClass k))
      (_hcanonicalMeas : Measurable canonicalClass)
      (_hfiniteCyl : ∀ k r,
        ∀ᵐ M ∂((diskRootedPlanarMapLaw (k + 1) (ell k)
          (hadm k).1 (hadm k).2.1 (hadm k).2.2) :
            Measure RootedLocallyFinitePlanarMap),
          b r (finiteClass k M) = rootLift (d39RootedBallSystem.ballClass r
            M.toRootedLocallyFiniteMap.toD39RootedMap))
      (_hcanonicalCyl : ∀ r,
        ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
          b r (canonicalClass W) = rootLift (d39RootedBallSystem.ballClass r
            (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap))
      (_hlaw : geometricUIBHBOTLaw =
        (uibhbotCodeLawRel.map canonicalClass).map Subtype.val),
      Tendsto (fun k =>
        ((diskRootedPlanarMapLaw (k + 1) (ell k)
          (hadm k).1 (hadm k).2.1 (hadm k).2.2).map
            (finiteClass k)).map Subtype.val)
        atTop (𝓝 geometricUIBHBOTLaw) := by
  let : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  let : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  let : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  let : TopologicalSpace D39RootedMap :=
    bsLocalDistanceTopologyGeneric d39RootedBallSystem
  let : MeasurableSpace D39RootedMap := borel D39RootedMap
  let : BorelSpace D39RootedMap := ⟨rfl⟩
  let : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
  let : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
  let : TopologicalSpace S := localClassTopology b
  let : MeasurableSpace S := borel S
  let : BorelSpace S := ⟨rfl⟩
  intro finiteClass canonicalClass geometricUIBHBOTLaw hfiniteMeas
    hcanonicalMeas hfiniteCyl hcanonicalCyl hlaw
  have hcompat := localClass_compatible_of_dyadic_ball b hball
  let f : RootedLocallyFinitePlanarMap → D39RootedMap :=
    fun M => M.toRootedLocallyFiniteMap.toD39RootedMap
  have hf : Measurable f := measurable_toD39RootedMap
  have hcode : Measurable uibhbotRootedPlanarMapOfCode :=
    measurable_uibhbotRootedPlanarMapOfCode
  let : TopologicalSpace d39RootedBallSystem.Object :=
    bsLocalDistanceTopologyGeneric d39RootedBallSystem
  let : MeasurableSpace d39RootedBallSystem.Object := borel d39RootedBallSystem.Object
  let : BorelSpace d39RootedBallSystem.Object := ⟨rfl⟩
  have hcombMeas (r : ℕ) (c : ExteriorMarkedBallClass) :
      MeasurableSet ((fun M => rootLift (d39RootedBallSystem.ballClass r M)) ⁻¹' {c} : Set D39RootedMap) := by
    have hc : IsClopen[localClassTopology (fun r (M : D39RootedMap) =>
        rootLift (d39RootedBallSystem.ballClass r M))]
        ((fun M => rootLift (d39RootedBallSystem.ballClass r M)) ⁻¹' {c}) :=
      isClopen_localCylinder (fun r (M : D39RootedMap) =>
        rootLift (d39RootedBallSystem.ballClass r M)) r c
    rw [rootLift_d39_topology] at hc
    exact hc.isOpen.measurableSet
  have hgeomMeas (r : ℕ) (c : ExteriorMarkedBallClass) :
      MeasurableSet (b r ⁻¹' {c}) :=
    (isClopen_localCylinder b r c).isOpen.measurableSet
  have hcodeLaw : uibhbotCodeLawRel.map (f ∘ uibhbotRootedPlanarMapOfCode) =
      uibhbotRootedPlanarMapLaw.map f := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map,
      uibhbotRootedPlanarMapLaw_toMeasure_eq_code_map]
    exact (Measure.map_map hf hcode).symm
  have hfiniteMass (k r : ℕ) (c : ExteriorMarkedBallClass) :
      ((diskRootedPlanarMapLaw (k + 1) (ell k)
        (hadm k).1 (hadm k).2.1 (hadm k).2.2).map (finiteClass k))
          (b r ⁻¹' {c}) =
      ((diskRootedPlanarMapLaw (k + 1) (ell k)
        (hadm k).1 (hadm k).2.1 (hadm k).2.2).map f)
          ((fun M => rootLift (d39RootedBallSystem.ballClass r M)) ⁻¹' {c}) :=
    map_cylinder_mass_eq_of_ae _ (finiteClass k) f (b r)
      (fun M => rootLift (d39RootedBallSystem.ballClass r M)) (hfiniteMeas k) hf
      (hfiniteCyl k r) c (hgeomMeas r c) (hcombMeas r c)
  have hcanonicalMass (r : ℕ) (c : ExteriorMarkedBallClass) :
      (uibhbotCodeLawRel.map canonicalClass) (b r ⁻¹' {c}) =
      (uibhbotRootedPlanarMapLaw.map f)
        ((fun M => rootLift (d39RootedBallSystem.ballClass r M)) ⁻¹' {c}) := by
    rw [← hcodeLaw]
    exact map_cylinder_mass_eq_of_ae _ canonicalClass
      (f ∘ uibhbotRootedPlanarMapOfCode) (b r)
      (fun M => rootLift (d39RootedBallSystem.ballClass r M)) hcanonicalMeas (hf.comp hcode)
      (hcanonicalCyl r) c (hgeomMeas r c) (hcombMeas r c)
  have hmass : ∀ r c, Tendsto (fun k =>
      ((diskRootedPlanarMapLaw (k + 1) (ell k)
        (hadm k).1 (hadm k).2.1 (hadm k).2.2).map (finiteClass k))
          (b r ⁻¹' {c})) atTop
        (𝓝 ((uibhbotCodeLawRel.map canonicalClass) (b r ⁻¹' {c}))) := by
    intro r c
    simp only [hfiniteMass, hcanonicalMass]
    exact diskRootedPlanarMapLaw_rootLift_cylinder_tendsto_uibhbot
      A hA ell hadm hlo hhi r c
  rw [hlaw]
  exact (tendsto_of_localCylinder_subspace b hball hcompat hmass).2


























end DirectedDistances.PaperProofs.Section5
end
