/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTLocalLimitLaw













public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section5
open MeasureTheory Filter Set
open scoped Topology

local instance : MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance : BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩








@[expose] def uibotGeometricLocalLimitProbabilityLaw
    (DC : UIBOTDeterministicComparison)
    (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (ns : ℕ → ℕ) (_hns : Tendsto ns atTop atTop)
    (hsize : ∀ k, 1 ≤ ns k)
    (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k))) :
    ProbabilityMeasure D39GeomRootedMapClass.{0} :=
  letI : Nonempty (ProbabilityMeasure D39GeomRootedMapClass.{0}) :=
    ⟨uibotWholePlaneGeometricProbabilityLaw DC⟩
  limUnder atTop (fun k => uibotFiniteGeometricProbabilityLaw ℓ ρ (ns k)
    hℓ hρ (hsize k) (hne k))

variable (DC : UIBOTDeterministicComparison)
  (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
  (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
  (hsize : ∀ k, 1 ≤ ns k)
  (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k)))

/-- Helper toward Proposition 3.9: the source-defined local-limit law
equals the measurable whole-plane iid geometric pushforward, under DC. -/
theorem uibotGeometricLocalLimitProbabilityLaw_toMeasure_eq :
    (uibotGeometricLocalLimitProbabilityLaw DC ℓ ρ hℓ hρ ns hns hsize hne :
      Measure D39GeomRootedMapClass.{0}) =
      wholePlaneIIDCodeMeasure.map (uibotMeasurableWholePlaneClassMap DC) := by
  exact uibotGeometricLocalLimit_eq_iidPushforward_of_comparison
    DC ℓ ρ hℓ hρ ns hns hsize hne

/-- Helper toward Proposition 3.9: the finite geometric probability laws
converge to the local-limit probability law used for transport. -/
theorem tendsto_uibotGeometricLocalLimitProbabilityLaw :
    Tendsto (fun k => uibotFiniteGeometricProbabilityLaw ℓ ρ (ns k)
      hℓ hρ (hsize k) (hne k)) atTop
      (𝓝 (uibotGeometricLocalLimitProbabilityLaw DC ℓ ρ hℓ hρ ns hns hsize hne)) := by
  have heq : uibotGeometricLocalLimitProbabilityLaw DC ℓ ρ hℓ hρ ns hns hsize hne =
      uibotWholePlaneGeometricProbabilityLaw DC :=
    (uibotFiniteGeometricProbabilityLaw_tendsto_of_comparison
      DC ℓ ρ hℓ hρ ns hns hsize hne).limUnder_eq
  rw [heq]
  exact uibotFiniteGeometricProbabilityLaw_tendsto_of_comparison
    DC ℓ ρ hℓ hρ ns hns hsize hne

/-- Helper toward Proposition 3.9: every observable measurable for the
local-topology Borel sigma algebra has the same law under the UIBOT local
limit as its composition with the measurable class map under the iid code
law. This asserts equality in law, without a pathwise identification. -/
theorem uibotGeometricLocalLimitProbabilityLaw_map
    {α : Type*} [MeasurableSpace α]
    (Phi : D39GeomRootedMapClass.{0} → α) (hPhi : Measurable Phi) :
    (uibotGeometricLocalLimitProbabilityLaw DC ℓ ρ hℓ hρ ns hns hsize hne :
      Measure D39GeomRootedMapClass.{0}).map Phi =
      wholePlaneIIDCodeMeasure.map (Phi ∘ uibotMeasurableWholePlaneClassMap DC) := by
  rw [uibotGeometricLocalLimitProbabilityLaw_toMeasure_eq]
  exact Measure.map_map hPhi (measurable_uibotMeasurableWholePlaneClassMap DC)

/-- Helper toward Proposition 3.9: a Borel event of rooted geometric maps
has the same probability under the local-limit law and its iid preimage. -/
theorem uibotGeometricLocalLimitProbabilityLaw_apply
    (s : Set D39GeomRootedMapClass.{0}) (hs : MeasurableSet s) :
    (uibotGeometricLocalLimitProbabilityLaw DC ℓ ρ hℓ hρ ns hns hsize hne :
      Measure D39GeomRootedMapClass.{0}) s =
      wholePlaneIIDCodeMeasure (uibotMeasurableWholePlaneClassMap DC ⁻¹' s) := by
  rw [uibotGeometricLocalLimitProbabilityLaw_toMeasure_eq]
  exact Measure.map_apply (measurable_uibotMeasurableWholePlaneClassMap DC) hs

/-- Helper toward Proposition 3.9: events of any Borel-measurable map
observable transport to the corresponding composed iid-code events. -/
theorem uibotGeometricLocalLimitProbabilityLaw_observable_event
    {α : Type*} [MeasurableSpace α]
    (Phi : D39GeomRootedMapClass.{0} → α) (hPhi : Measurable Phi)
    (s : Set α) (hs : MeasurableSet s) :
    (uibotGeometricLocalLimitProbabilityLaw DC ℓ ρ hℓ hρ ns hns hsize hne :
      Measure D39GeomRootedMapClass.{0}) (Phi ⁻¹' s) =
      wholePlaneIIDCodeMeasure ((Phi ∘ uibotMeasurableWholePlaneClassMap DC) ⁻¹' s) := by
  exact uibotGeometricLocalLimitProbabilityLaw_apply
    DC ℓ ρ hℓ hρ ns hns hsize hne (Phi ⁻¹' s) (hPhi hs)

/-- Helper toward Proposition 3.9: a Borel-measurable property of the
rooted geometric map holds almost surely for the local limit if and only
if its pullback holds almost surely for the iid code. -/
theorem uibotGeometricLocalLimitProbabilityLaw_ae_iff
    (P : D39GeomRootedMapClass.{0} → Prop) (hP : MeasurableSet {x | P x}) :
    (∀ᵐ x ∂(uibotGeometricLocalLimitProbabilityLaw DC ℓ ρ hℓ hρ ns hns hsize hne :
      Measure D39GeomRootedMapClass.{0}), P x) ↔
      ∀ᵐ W ∂wholePlaneIIDCodeMeasure, P (uibotMeasurableWholePlaneClassMap DC W) := by
  rw [uibotGeometricLocalLimitProbabilityLaw_toMeasure_eq]
  exact ae_map_iff (measurable_uibotMeasurableWholePlaneClassMap DC).aemeasurable hP

/-- Helper toward Proposition 3.9: almost-sure measurable properties of
a measurable observable transport through its composition with the iid
class map, retaining a single almost-sure event for the entire property. -/
theorem uibotGeometricLocalLimitProbabilityLaw_observable_ae_iff
    {α : Type*} [MeasurableSpace α]
    (Phi : D39GeomRootedMapClass.{0} → α) (hPhi : Measurable Phi)
    (P : α → Prop) (hP : MeasurableSet {y | P y}) :
    (∀ᵐ x ∂(uibotGeometricLocalLimitProbabilityLaw DC ℓ ρ hℓ hρ ns hns hsize hne :
      Measure D39GeomRootedMapClass.{0}), P (Phi x)) ↔
      ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        P (Phi (uibotMeasurableWholePlaneClassMap DC W)) := by
  exact uibotGeometricLocalLimitProbabilityLaw_ae_iff
    DC ℓ ρ hℓ hρ ns hns hsize hne (fun x => P (Phi x)) (hPhi hP)


































































































































end DirectedDistances.PaperProofs.Section3

end
