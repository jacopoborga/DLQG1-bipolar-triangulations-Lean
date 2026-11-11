/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516D39Transport
public import DirectedDistances.Probability.BSLocalCriterionSubspace
public import DirectedDistances.Probability.BSLocalCylinderMeasurable
public import DirectedDistances.PaperProofs.Section5.Prop516GeometricStatement
public import DirectedDistances.PaperProofs.Section5.Prop516PLCylinderBall
public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallIso5
public import DirectedDistances.PaperProofs.Section5.Prop516Def58LawIdentification

/-! The assembly below is conditional on displayed geometric representation,
measurability, ball comparison, and law identification inputs. It does not
establish Proposition 5.16 or identify the candidate PL carrier with the source.
The topology used on combinatorial maps is exactly the one in
`Prop516D39Transport`, with index `r` meaning source radius `r + 1`. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open DirectedDistances.Probability
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

/-- Helper toward Proposition 5.16: almost-sure agreement of observations
identifies their cylinder masses under measurable push-forwards. -/
theorem map_cylinder_mass_eq_of_ae
    {Ω X Y C : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace Y] (μ : ProbabilityMeasure Ω)
    (f : Ω → X) (g : Ω → Y) (b : X → C) (c : Y → C)
    (hf : Measurable f) (hg : Measurable g)
    (heq : ∀ᵐ ω ∂(μ : Measure Ω), b (f ω) = c (g ω))
    (a : C) (hb : MeasurableSet (b ⁻¹' {a}))
    (hc : MeasurableSet (c ⁻¹' {a})) :
    μ.map f (b ⁻¹' {a}) = μ.map g (c ⁻¹' {a}) := by
  rw [ProbabilityMeasure.map_apply _ hf.aemeasurable hb,
    ProbabilityMeasure.map_apply _ hg.aemeasurable hc]
  apply congrArg ENNReal.toNNReal
  apply measure_congr
  filter_upwards [heq] with ω hω
  exact propext (show b (f ω) = a ↔ c (g ω) = a from hω ▸ Iff.rfl)

/-- Helper toward Proposition 5.16: composition of measurable maps commutes
with probability push-forward, including the geometric subspace inclusion. -/
theorem probabilityMeasure_map_map_eq
    {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace Y] (μ : ProbabilityMeasure Ω)
    (f : Ω → X) (g : X → Y) (hf : Measurable f) (hg : Measurable g) :
    (μ.map f).map g = μ.map (g ∘ f) := by
  apply ProbabilityMeasure.toMeasure_injective
  exact Measure.map_map hg hf

/-- Helper toward Proposition 5.16: weak convergence preserves the mass of
each clopen event, with masses valued in the nonnegative reals. -/
theorem tendsto_clopen_mass_of_tendsto
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {ι : Type*} {L : Filter ι}
    {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs L (𝓝 μ)) {s : Set X} (hs : IsClopen s) :
    Tendsto (fun i => μs i s) L (𝓝 (μ s)) := by
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ
    (BoundedContinuousFunction.indicator s hs)
  change Tendsto (fun i => ∫ x, s.indicator 1 x ∂(μs i : Measure X)) L
    (𝓝 (∫ x, s.indicator 1 x ∂(μ : Measure X))) at h
  simp only [integral_indicator_one hs.isOpen.measurableSet, Measure.real,
    ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_toReal] at h
  exact NNReal.tendsto_coe.mp h

/-- Helper toward Proposition 5.16: combinatorial convergence in the exact
local topology topology implies convergence of every faced-ball cylinder mass. -/
theorem diskRootedPlanarMapLaw_d39_cylinder_tendsto_uibhbot
    (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ)) :
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    letI : TopologicalSpace D39RootedMap :=
      bsLocalDistanceTopologyGeneric d39RootedBallSystem
    letI : MeasurableSpace D39RootedMap := borel D39RootedMap
    letI : BorelSpace D39RootedMap := ⟨rfl⟩
    ∀ r c, Tendsto (fun k =>
      ((diskRootedPlanarMapLaw (k + 1) (ell k)
        (hadm k).1 (hadm k).2.1 (hadm k).2.2).map
          (fun M : RootedLocallyFinitePlanarMap =>
            M.toRootedLocallyFiniteMap.toD39RootedMap))
        (d39RootedBallSystem.ballClass r ⁻¹' {c}))
      atTop (𝓝 ((uibhbotRootedPlanarMapLaw.map
        (fun M : RootedLocallyFinitePlanarMap =>
          M.toRootedLocallyFiniteMap.toD39RootedMap))
        (d39RootedBallSystem.ballClass r ⁻¹' {c}))) := by
  let : TopologicalSpace RootedLocallyFinitePlanarMap :=
    bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
  let : MeasurableSpace RootedLocallyFinitePlanarMap :=
    borel RootedLocallyFinitePlanarMap
  let : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  let : TopologicalSpace D39RootedMap :=
    bsLocalDistanceTopologyGeneric d39RootedBallSystem
  let : MeasurableSpace D39RootedMap := borel D39RootedMap
  let : BorelSpace D39RootedMap := ⟨rfl⟩
  intro r c
  have hc : IsClopen[bsLocalDistanceTopologyGeneric d39RootedBallSystem]
      (d39RootedBallSystem.ballClass r ⁻¹' {c}) := by
    rw [bsLocalDistanceTopology_eq_localClassTopologyGeneric]
    exact isClopen_localCylinder d39RootedBallSystem.ballClass r c
  exact tendsto_clopen_mass_of_tendsto
    (diskRootedPlanarMapLaw_d39_tendsto_uibhbot A hA ell hadm hlo hhi) hc

/-- Helper toward Proposition 5.16: the dyadic closed-ball characterization
itself implies compatibility of consecutive radius observations. -/
theorem localClass_compatible_of_dyadic_ball
    {X : Type*} [PseudoEMetricSpace X] {S : Set X} {C : ℕ → Type*}
    (b : ∀ r, S → C r)
    (hball : ∀ r (x y : S),
      edist (x : X) y ≤ (1 / 2 : ℝ≥0∞) ^ (r + 1) ↔ b r x = b r y) :
    ∀ r x y, b (r + 1) x = b (r + 1) y → b r x = b r y := by
  intro r x y h
  apply (hball r x y).mp
  calc
    edist (x : X) y ≤ (1 / 2 : ℝ≥0∞) ^ ((r + 1) + 1) :=
      (hball (r + 1) x y).mpr h
    _ = (1 / 2 : ℝ≥0∞) ^ (r + 1) * (1 / 2) := pow_succ _ _
    _ ≤ (1 / 2 : ℝ≥0∞) ^ (r + 1) :=
      mul_le_of_le_one_right' (by norm_num)

/-- Helper toward Proposition 5.16: transfer the proved combinatorial limit
to geometric class laws through almost-sure cylinder identifications.

The maps take values in the candidate represented PL subspace, so membership
is carried by their codomain. Their measurability, both samplewise cylinder
identifications, the metric characterization of `b`, and
the identification of the geometric UIBHBOT law are all displayed inputs.
No geometric convergence is assumed. -/
theorem prop516_geometricClassLaw_tendsto_of_inputs
    (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ))
    (b : ℕ → PLCylinderBall.X_PL → D39BallClass)
    (hball : ∀ r (x y : PLCylinderBall.X_PL),
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
    letI : TopologicalSpace PLCylinderBall.X_PL := localClassTopology b
    letI : MeasurableSpace PLCylinderBall.X_PL := borel PLCylinderBall.X_PL
    letI : BorelSpace PLCylinderBall.X_PL := ⟨rfl⟩
    ∀ (finiteClass : ℕ → RootedLocallyFinitePlanarMap → PLCylinderBall.X_PL)
      (canonicalClass : (ℤ → Fin 3) → PLCylinderBall.X_PL)
      (geometricUIBHBOTLaw : ProbabilityMeasure D39GeomRootedMapClass)
      (_hfiniteMeas : ∀ k, Measurable (finiteClass k))
      (_hcanonicalMeas : Measurable canonicalClass)
      (_hfiniteCyl : ∀ k r,
        ∀ᵐ M ∂((diskRootedPlanarMapLaw (k + 1) (ell k)
          (hadm k).1 (hadm k).2.1 (hadm k).2.2) :
            Measure RootedLocallyFinitePlanarMap),
          b r (finiteClass k M) = d39RootedBallSystem.ballClass r
            M.toRootedLocallyFiniteMap.toD39RootedMap)
      (_hcanonicalCyl : ∀ r,
        ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
          b r (canonicalClass W) = d39RootedBallSystem.ballClass r
            (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap)
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
  let : TopologicalSpace PLCylinderBall.X_PL := localClassTopology b
  let : MeasurableSpace PLCylinderBall.X_PL := borel PLCylinderBall.X_PL
  let : BorelSpace PLCylinderBall.X_PL := ⟨rfl⟩
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
  have hcombMeas (r : ℕ) (c : D39BallClass) :
      MeasurableSet (d39RootedBallSystem.ballClass r ⁻¹' {c} : Set D39RootedMap) := by
    have hc : IsClopen[bsLocalDistanceTopologyGeneric d39RootedBallSystem]
        (d39RootedBallSystem.ballClass r ⁻¹' {c}) := by
      rw [bsLocalDistanceTopology_eq_localClassTopologyGeneric]
      exact isClopen_localCylinder d39RootedBallSystem.ballClass r c
    exact hc.isOpen.measurableSet
  have hgeomMeas (r : ℕ) (c : D39BallClass) :
      MeasurableSet (b r ⁻¹' {c}) :=
    (isClopen_localCylinder b r c).isOpen.measurableSet
  have hcodeLaw : uibhbotCodeLawRel.map (f ∘ uibhbotRootedPlanarMapOfCode) =
      uibhbotRootedPlanarMapLaw.map f := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map,
      uibhbotRootedPlanarMapLaw_toMeasure_eq_code_map]
    exact (Measure.map_map hf hcode).symm
  have hfiniteMass (k r : ℕ) (c : D39BallClass) :
      ((diskRootedPlanarMapLaw (k + 1) (ell k)
        (hadm k).1 (hadm k).2.1 (hadm k).2.2).map (finiteClass k))
          (b r ⁻¹' {c}) =
      ((diskRootedPlanarMapLaw (k + 1) (ell k)
        (hadm k).1 (hadm k).2.1 (hadm k).2.2).map f)
          (d39RootedBallSystem.ballClass r ⁻¹' {c}) :=
    map_cylinder_mass_eq_of_ae _ (finiteClass k) f (b r)
      (d39RootedBallSystem.ballClass r) (hfiniteMeas k) hf
      (hfiniteCyl k r) c (hgeomMeas r c) (hcombMeas r c)
  have hcanonicalMass (r : ℕ) (c : D39BallClass) :
      (uibhbotCodeLawRel.map canonicalClass) (b r ⁻¹' {c}) =
      (uibhbotRootedPlanarMapLaw.map f)
        (d39RootedBallSystem.ballClass r ⁻¹' {c}) := by
    rw [← hcodeLaw]
    exact map_cylinder_mass_eq_of_ae _ canonicalClass
      (f ∘ uibhbotRootedPlanarMapOfCode) (b r)
      (d39RootedBallSystem.ballClass r) hcanonicalMeas (hf.comp hcode)
      (hcanonicalCyl r) c (hgeomMeas r c) (hcombMeas r c)
  have hmass : ∀ r c, Tendsto (fun k =>
      ((diskRootedPlanarMapLaw (k + 1) (ell k)
        (hadm k).1 (hadm k).2.1 (hadm k).2.2).map (finiteClass k))
          (b r ⁻¹' {c})) atTop
        (𝓝 ((uibhbotCodeLawRel.map canonicalClass) (b r ⁻¹' {c}))) := by
    intro r c
    simp only [hfiniteMass, hcanonicalMass]
    exact diskRootedPlanarMapLaw_d39_cylinder_tendsto_uibhbot
      A hA ell hadm hlo hhi r c
  rw [hlaw]
  exact (tendsto_of_localCylinder_subspace b hball hcompat hmass).2
































































end DirectedDistances.PaperProofs.Section5

end
