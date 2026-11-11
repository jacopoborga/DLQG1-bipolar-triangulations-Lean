/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTQualifierTransport
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! # Finite-ball factorization toward Proposition 3.9

local-determination criterion, not Proposition 3.9 or any counted consumer.
The functions on finite geometric ball classes are arbitrary: their pullbacks
are locally constant. An almost-sure limit of these functions therefore has a
Borel factor on geometric rooted-map classes. No measurable inverse of the
KMSW coding, separability of the map-class space, or code-fiber descent is assumed.

The index `r` of `d39GeomBallClassMap` denotes the radius `r + 1` ball.
The deterministic definition of DC and all qualifications of the imported -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.RandomWalk DirectedDistances.PlanarMap MeasureTheory Filter Set
open scoped Topology ENNReal

local instance : MeasurableSpace D39GeomRootedMapClass.{0} :=
  borel D39GeomRootedMapClass.{0}
local instance : BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

/-- Helper toward Proposition 3.9: every function of one geometric ball
class is continuous, since that ball class is constant on a dyadic neighborhood.
No topology or countability of the ball-class quotient is required. -/
theorem continuous_d39GeomBallClass_observable
    {α : Type*} [TopologicalSpace α] (r : ℕ)
    (phi : Quotient (d39GeomBallClassSetoid.{0} r) → α) :
    Continuous (fun x => phi (d39GeomBallClassMap r x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hball : Metric.eball x ((1 / 2 : ℝ≥0∞) ^ r) ∈ 𝓝 x :=
    Metric.eball_mem_nhds x (ENNReal.pow_pos (by norm_num) r)
  have heq : (fun y => phi (d39GeomBallClassMap r y)) =ᶠ[𝓝 x]
      (fun _ => phi (d39GeomBallClassMap r x)) := by
    filter_upwards [hball] with y hy
    rw [d39GeomClass_openBall_eq_ballClass] at hy
    exact congrArg phi hy.symm
  exact tendsto_const_nhds.congr' heq.symm

/-- Helper toward Proposition 3.9: functions of finite geometric ball
classes are Borel measurable, even without a countable set of ball classes. -/
theorem measurable_d39GeomBallClass_observable
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    (r : ℕ) (phi : Quotient (d39GeomBallClassSetoid.{0} r) → α) :
    Measurable (fun x => phi (d39GeomBallClassMap r x)) :=
  (continuous_d39GeomBallClass_observable r phi).measurable

/-- Helper toward Proposition 3.9: an almost-sure limit of functions of
the finite geometric balls of the measurable KMSW class map has a Borel factor.
The local limit premise concerns explicit finite-ball approximants, rather than
assuming the desired factorization. The complete separable metric output may
itself be a countable product, so the equality retains one simultaneous event. -/
theorem exists_measurable_uibot_factor_of_ballClass_tendsto
    {α : Type*} [TopologicalSpace α] [PolishSpace α]
    [MeasurableSpace α] [BorelSpace α] [Nonempty α]
    (DC : UIBOTDeterministicComparison)
    (Psi : (ℤ → Fin 3) → α)
    (phi : (r : ℕ) → Quotient (d39GeomBallClassSetoid.{0} r) → α)
    (hlim : ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      Tendsto (fun r => phi r (d39GeomBallClassMap r
        (uibotMeasurableWholePlaneClassMap DC W))) atTop (𝓝 (Psi W))) :
    ∃ Phi : D39GeomRootedMapClass.{0} → α, Measurable Phi ∧
      Psi =ᵐ[wholePlaneIIDCodeMeasure] Phi ∘ uibotMeasurableWholePlaneClassMap DC := by
  let Phi : D39GeomRootedMapClass.{0} → α :=
    fun x => limUnder atTop (fun r => phi r (d39GeomBallClassMap r x))
  have hPhi : Measurable Phi :=
    (StronglyMeasurable.limUnder (fun r =>
      (measurable_d39GeomBallClass_observable r (phi r)).stronglyMeasurable)).measurable
  refine ⟨Phi, hPhi, ?_⟩
  filter_upwards [hlim] with W hW
  exact hW.limUnder_eq.symm

/-- Helper toward Proposition 3.9: countably many finite-ball limits
factor jointly on one almost-sure event. This retains the full indexed
observable needed for joint laws, rather than merely its marginal laws. -/
theorem exists_measurable_uibot_joint_factor_of_ballClass_tendsto
    {ι α : Type*} [Countable ι] [TopologicalSpace α] [PolishSpace α]
    [MeasurableSpace α] [BorelSpace α] [Nonempty α]
    (DC : UIBOTDeterministicComparison)
    (Psi : (ℤ → Fin 3) → ι → α)
    (phi : ι → (r : ℕ) → Quotient (d39GeomBallClassSetoid.{0} r) → α)
    (hlim : ∀ i, ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      Tendsto (fun r => phi i r (d39GeomBallClassMap r
        (uibotMeasurableWholePlaneClassMap DC W))) atTop (𝓝 (Psi W i))) :
    ∃ Phi : D39GeomRootedMapClass.{0} → ι → α, Measurable Phi ∧
      Psi =ᵐ[wholePlaneIIDCodeMeasure] Phi ∘ uibotMeasurableWholePlaneClassMap DC := by
  apply exists_measurable_uibot_factor_of_ballClass_tendsto
    DC Psi (fun r b i => phi i r b)
  filter_upwards [ae_all_iff.mpr hlim] with W hW
  exact tendsto_pi_nhds.mpr hW

/-- Helper toward Proposition 3.9: a finite-ball observable, modified only
on a code null set, has an explicit Borel factor on geometric rooted maps. -/
theorem exists_measurable_uibot_factor_of_ballClass
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    (DC : UIBOTDeterministicComparison) (r : ℕ)
    (Psi : (ℤ → Fin 3) → α)
    (phi : Quotient (d39GeomBallClassSetoid.{0} r) → α)
    (hlocal : ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      Psi W = phi (d39GeomBallClassMap r (uibotMeasurableWholePlaneClassMap DC W))) :
    ∃ Phi : D39GeomRootedMapClass.{0} → α, Measurable Phi ∧
      Psi =ᵐ[wholePlaneIIDCodeMeasure] Phi ∘ uibotMeasurableWholePlaneClassMap DC :=
  ⟨fun x => phi (d39GeomBallClassMap r x),
    measurable_d39GeomBallClass_observable r phi, hlocal⟩

/-- Helper toward Proposition 3.9: the Borel factor supplied by finite-ball
limits has the original code observable's law under the UIBOT local limit,
conditional on DC and the imported finite-law attribution qualifications. -/
theorem exists_uibot_factor_and_law_of_ballClass_tendsto
    {α : Type*} [TopologicalSpace α] [PolishSpace α]
    [MeasurableSpace α] [BorelSpace α] [Nonempty α]
    (DC : UIBOTDeterministicComparison)
    (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (hsize : ∀ k, 1 ≤ ns k)
    (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k)))
    (Psi : (ℤ → Fin 3) → α)
    (phi : (r : ℕ) → Quotient (d39GeomBallClassSetoid.{0} r) → α)
    (hlim : ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      Tendsto (fun r => phi r (d39GeomBallClassMap r
        (uibotMeasurableWholePlaneClassMap DC W))) atTop (𝓝 (Psi W))) :
    ∃ Phi : D39GeomRootedMapClass.{0} → α, Measurable Phi ∧
      Psi =ᵐ[wholePlaneIIDCodeMeasure] Phi ∘ uibotMeasurableWholePlaneClassMap DC ∧
      (uibotGeometricLocalLimitProbabilityLaw DC ℓ ρ hℓ hρ ns hns hsize hne :
        Measure D39GeomRootedMapClass.{0}).map Phi = wholePlaneIIDCodeMeasure.map Psi := by
  obtain ⟨Phi, hPhi, heq⟩ :=
    exists_measurable_uibot_factor_of_ballClass_tendsto DC Psi phi hlim
  refine ⟨Phi, hPhi, heq, ?_⟩
  rw [uibotGeometricLocalLimitProbabilityLaw_map DC ℓ ρ hℓ hρ ns hns hsize hne Phi hPhi]
  exact Measure.map_congr heq.symm
















































end DirectedDistances.PaperProofs.Section3

end
