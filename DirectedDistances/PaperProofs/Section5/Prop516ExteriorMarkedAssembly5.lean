/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516ExteriorMarkedAssembly4

/-! Helper toward Proposition 5.16. Actual finite sample geometric laws, using
the proved exterior domain, and their independence from geometric choices
at the level of Borel measures. No source limiting law is defined here. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section5.Prop516ExteriorAssembly5

open DirectedDistances.PlanarMap DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open DirectedDistances.Probability
open Prop516RootExteriorEncoding Prop516ExteriorAssembly4
open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- Helper toward Proposition 5.16: agreement of every marked observation
makes two source classes topologically inseparable in the geometric space. -/
theorem inseparable_of_observation_eq (x y : subspace)
    (h : ∀ r, observation r x = observation r y) :
    Inseparable (x : D39GeomRootedMapClass) (y : D39GeomRootedMapClass) := by
  apply EMetric.inseparable_iff.mpr
  apply le_antisymm _ bot_le
  apply ge_of_tendsto'
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (1 / 2 : ℝ≥0∞) < 1))
  intro r
  exact ((hball r x y).mpr (h r)).trans
    (pow_le_pow_right_of_le_one' (by norm_num) (Nat.le_succ r))

/-- Helper toward Proposition 5.16: simultaneous marked-cylinder agreement
identifies Borel pushforwards, without requiring equality of geometric classes. -/
theorem map_val_eq_of_observation_eq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → subspace) :
    letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
    ∀ (_hf : Measurable (fun ω => (f ω).val))
      (_hg : Measurable (fun ω => (g ω).val))
      (_h : ∀ᵐ ω ∂μ, ∀ r, observation r (f ω) = observation r (g ω)),
      μ.map (fun ω => (f ω).val) = μ.map (fun ω => (g ω).val) := by
  let : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
  let : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
  intro hf hg h
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hf hs, Measure.map_apply hg hs]
  apply measure_congr
  filter_upwards [h] with ω hω
  exact propext ((inseparable_of_observation_eq (f ω) (g ω) hω).mem_measurableSet_iff hs)

/-- Helper toward Proposition 5.16: the finite source sample carrier, with
the channeled map and the uniform missing-edge mark kept as separate factors. -/
abbrev Sample (ell n : ℕ) :=
  {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} × Fin ell

/-- Helper toward Proposition 5.16: a choice of the already constructed
finite exterior realization in the common geometric subspace. -/
@[expose] def finiteSampleClass (ell n : ℕ) (hell : 0 < ell) :
    Sample ell n → subspace :=
  Classical.choose (exists_finiteSampleClass ell n hell)

/-- Helper toward Proposition 5.16: the chosen finite realization is an
actual exterior domain of the given sample, with all its construction witnesses. -/
theorem finiteSampleClass_spec (ell n : ℕ) (hell : 0 < ell) (p : Sample ell n) :
    ∃ (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
      (U : P.Face) (hU : P.IsUnbounded U)
      (hborder : ∀ d, P.dartBorders d U ↔
        (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell p) n).IsOuter d),
      finiteSampleClass ell n hell p =
        toSubspace (.finite ell n hell p P U hU hborder) :=
  (Classical.choose_spec (exists_finiteSampleClass ell n hell)).2.1 p

/-- Helper toward Proposition 5.16: all marked cylinders of the chosen
finite realization equal the actual rooted disk code cylinders. -/
theorem finiteSampleClass_observation (ell n : ℕ) (hell : 0 < ell)
    (p : Sample ell n) (r : ℕ) :
    observation r (finiteSampleClass ell n hell p) = rootLift
      (d39BallClass (diskRootedD39MapOfSample n ell hell p) (r + 1) (Nat.succ_pos r)) :=
  (Classical.choose_spec (exists_finiteSampleClass ell n hell)).2.2 p r

/-- Helper toward Proposition 5.16: the finite class map takes values in
the geometric quotient itself. -/
@[expose] def finiteGeometricClass (ell n : ℕ) (hell : 0 < ell)
    (p : Sample ell n) : D39GeomRootedMapClass :=
  (finiteSampleClass ell n hell p).val

/-- Helper toward Proposition 5.16: the actual finite class map is Borel
measurable for the finite sampling sigma algebra. -/
theorem measurable_finiteGeometricClass (ell n : ℕ) (hell : 0 < ell) :
    letI : MeasurableSpace
      {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
    Measurable (finiteGeometricClass ell n hell) :=
  measurable_diskSample_geometricClassMap ell n hell _

/-- Helper toward Proposition 5.16: a finite law on geometric classes from
the independent uniform map and missing-edge samples. This is a finite source
realization, with no identification of the limiting law. -/
@[expose] def finiteGeometricLaw (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
    ProbabilityMeasure D39GeomRootedMapClass := by
  let E := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) E
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  let : Nonempty (KMSWLeftWalkClass (ell + 1) n) :=
    kmswLeftWalkClass_nonempty_of_domain ell n hell hle hmod
  let : Nonempty Q := E.symm.nonempty
  let : Nonempty (Fin ell) := ⟨⟨0, hell⟩⟩
  let := diskBS_uniformCountingMeasure_probability Q
  let := diskBS_uniformCountingMeasure_probability (Fin ell)
  let : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
  exact ⟨((uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))).map
    (finiteGeometricClass ell n hell), inferInstance⟩

/-- Helper toward Proposition 5.16: the finite geometric law is exactly
the pushforward of the product sampling measure by the exterior class map. -/
theorem finiteGeometricLaw_toMeasure (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    let E := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
    let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
    letI : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) E
    letI : MeasurableSpace Q := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
    (finiteGeometricLaw n ell hell hle hmod).toMeasure =
      ((uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))).map
        (finiteGeometricClass ell n hell) := rfl

/-- Helper toward Proposition 5.16: inclusion of the common source subspace
is measurable for its local observation topology and the geometric Borel space. -/
theorem measurable_subspace_val :
    letI : TopologicalSpace subspace := localClassTopology observation
    letI : MeasurableSpace subspace := borel subspace
    letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
    Measurable (Subtype.val : subspace → D39GeomRootedMapClass) := by
  let : TopologicalSpace subspace := localClassTopology observation
  let : MeasurableSpace subspace := borel subspace
  let : BorelSpace subspace := ⟨rfl⟩
  let : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
  let : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
  have hc : Continuous (Subtype.val : subspace → D39GeomRootedMapClass) := by
    change @Continuous _ _ (localClassTopology observation) _ Subtype.val
    rw [topology_eq]
    exact continuous_subtype_val
  exact hc.measurable

/-- Helper toward Proposition 5.16: the intermediate planar-map assembly
has exactly the geometric law of the actual uniform finite samples whenever
its already constructed marked observations agree almost surely. -/
theorem finiteGeometricLaw_eq_map (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap := borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    letI : TopologicalSpace subspace := localClassTopology observation
    letI : MeasurableSpace subspace := borel subspace
    letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
    ∀ (f : RootedLocallyFinitePlanarMap → subspace) (_hf : Measurable f)
      (_hc : ∀ᵐ M ∂((diskRootedPlanarMapLaw n ell hell hle hmod) :
        Measure RootedLocallyFinitePlanarMap),
        ∀ r, observation r (f M) = rootLift (d39RootedBallSystem.ballClass r
          M.toRootedLocallyFiniteMap.toD39RootedMap)),
      finiteGeometricLaw n ell hell hle hmod =
        ((diskRootedPlanarMapLaw n ell hell hle hmod).map f).map Subtype.val := by
  let : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  let : MeasurableSpace RootedLocallyFinitePlanarMap := borel RootedLocallyFinitePlanarMap
  let : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  let : TopologicalSpace subspace := localClassTopology observation
  let : MeasurableSpace subspace := borel subspace
  let : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
  intro f hf hc
  let E := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) E
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  let μ := (uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))
  let j := diskRootedPlanarMapOfSample n ell hell
  have hj : Measurable j := measurable_diskRootedPlanarMapOfSample n ell hell
  have hsample : ∀ᵐ p ∂μ, ∀ r,
      observation r (f (j p)) = rootLift (d39RootedBallSystem.ballClass r
        (j p).toRootedLocallyFiniteMap.toD39RootedMap) := by
    rw [diskRootedPlanarMapLaw_toMeasure] at hc
    exact ae_of_ae_map hj.aemeasurable hc
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [finiteGeometricLaw_toMeasure, diskRootedPlanarMapLaw_toMeasure,
    Measure.map_map hf hj, Measure.map_map measurable_subspace_val (hf.comp hj)]
  apply map_val_eq_of_observation_eq μ (finiteSampleClass ell n hell)
    (fun p => f (j p)) (measurable_finiteGeometricClass ell n hell)
    (measurable_subspace_val.comp (hf.comp hj))
  filter_upwards [hsample] with p hp
  intro r
  exact (finiteSampleClass_observation ell n hell p r).trans (hp r).symm

/-- Helper toward Proposition 5.16: every family of actual exterior
drawings gives exactly the same finite geometric Borel law. -/
theorem finiteGeometricLaw_eq_exterior_pushforward
    (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q)
    (P : ∀ p : Sample ell n, StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (U : ∀ p, (P p).Face) (hU : ∀ p, (P p).IsUnbounded (U p))
    (hborder : ∀ p d, (P p).dartBorders d (U p) ↔
      (kmswStageDirectedMap (diskSampleCanonicalStageCode ell n hell p) n).IsOuter d) :
    let E := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
    let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
    letI : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) E
    letI : MeasurableSpace Q := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
    (finiteGeometricLaw n ell hell hle hmod).toMeasure =
      ((uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))).map
        (fun p => PLCylinderBall.geometricClass
          (diskSampleExteriorDomain ell n hell p (P p) (U p) (hU p) (hborder p))) := by
  let E := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) E
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  let : MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
  rw [finiteGeometricLaw_toMeasure]
  apply map_val_eq_of_observation_eq _ (finiteSampleClass ell n hell)
    (fun p => toSubspace (.finite ell n hell p (P p) (U p) (hU p) (hborder p)))
    (measurable_finiteGeometricClass ell n hell)
    (measurable_diskSample_geometricClassMap ell n hell _)
  exact Eventually.of_forall fun p r =>
    (finiteSampleClass_observation ell n hell p r).trans
      (observation_toSubspace r
        (.finite ell n hell p (P p) (U p) (hU p) (hborder p))).symm

end DirectedDistances.PaperProofs.Section5.Prop516ExteriorAssembly5
end
