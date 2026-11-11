/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTCodeRecoveryPart6
public import DirectedDistances.PaperProofs.Section3.UIBOTQualifierTransport








public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open MeasureTheory Filter

local instance uibotCodeRecoveryPart7MeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance uibotCodeRecoveryPart7BorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

/-- Helper toward Proposition 3.9: fix one of the proved Borel inverses,
used jointly for all subsequent observables and predicates. -/
@[expose] def uibotRecoveredCode : D39GeomRootedMapClass.{0} → (ℤ → Fin 3) :=
  uibotRecovery_exists_borel_inverse.choose

/-- Helper toward Proposition 3.9: the fixed inverse is Borel measurable. -/
theorem measurable_uibotRecoveredCode : Measurable uibotRecoveredCode :=
  uibotRecovery_exists_borel_inverse.choose_spec.1

/-- Helper toward Proposition 3.9: the entire code is recovered on one
event of probability one, before any observable or predicate is chosen. -/
theorem uibotRecoveredCode_ae :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      uibotRecoveredCode (uibotMeasurableWholePlaneClassMap
        uibotDeterministicComparison_proved W) = W :=
  uibotRecovery_exists_borel_inverse.choose_spec.2

/-- Helper toward Proposition 3.9: all code predicates are preserved on
the same event, including their dependent shared witnesses and quantifiers.
This is a literal predicate equivalence, without a measurability claim. -/
theorem uibotRecoveredCode_ae_all_predicates :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ Q : (ℤ → Fin 3) → Prop,
      Q W ↔ Q (uibotRecoveredCode (uibotMeasurableWholePlaneClassMap
        uibotDeterministicComparison_proved W)) := by
  filter_upwards [uibotRecoveredCode_ae] with W hW
  intro Q
  rw [hW]

/-- Helper toward Proposition 3.9: a Borel version of an a.e. measurable
code observable, evaluated using the fixed recovered code. -/
@[expose] def uibotRecoveredObservable {α : Type*} [MeasurableSpace α]
    (X : (ℤ → Fin 3) → α) (hX : AEMeasurable X wholePlaneIIDCodeMeasure) :
    D39GeomRootedMapClass.{0} → α :=
  hX.mk X ∘ uibotRecoveredCode

/-- Helper toward Proposition 3.9: the recovered observable is Borel
even when the original selector is only a.e. measurable. -/
theorem measurable_uibotRecoveredObservable {α : Type*} [MeasurableSpace α]
    (X : (ℤ → Fin 3) → α) (hX : AEMeasurable X wholePlaneIIDCodeMeasure) :
    Measurable (uibotRecoveredObservable X hX) :=
  hX.measurable_mk.comp measurable_uibotRecoveredCode

/-- Helper toward Proposition 3.9: the recovered Borel observable agrees
with the entire original observable almost surely after the class map. -/
theorem uibotRecoveredObservable_ae {α : Type*} [MeasurableSpace α]
    (X : (ℤ → Fin 3) → α) (hX : AEMeasurable X wholePlaneIIDCodeMeasure) :
    X =ᵐ[wholePlaneIIDCodeMeasure] uibotRecoveredObservable X hX ∘
      uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved := by
  filter_upwards [uibotRecoveredCode_ae, hX.ae_eq_mk] with W hW hXW
  change X W = hX.mk X (uibotRecoveredCode _)
  rw [hW]
  exact hXW

/-- Helper toward Proposition 3.9: countably many a.e. measurable
observations have one Borel joint factor and one simultaneous equality event. -/
theorem uibotRecovery_ae_family_factor {ι α : Type*} [Countable ι]
    [MeasurableSpace α] (X : ι → (ℤ → Fin 3) → α)
    (hX : ∀ i, AEMeasurable (X i) wholePlaneIIDCodeMeasure) :
    ∃ Phi : D39GeomRootedMapClass.{0} → ι → α, Measurable Phi ∧
      ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ i,
        X i W = Phi (uibotMeasurableWholePlaneClassMap
          uibotDeterministicComparison_proved W) i := by
  let Y := fun W i => X i W
  have hY : AEMeasurable Y wholePlaneIIDCodeMeasure := aemeasurable_pi_iff.mpr hX
  refine ⟨uibotRecoveredObservable Y hY, measurable_uibotRecoveredObservable Y hY, ?_⟩
  filter_upwards [uibotRecoveredObservable_ae Y hY] with W hW
  exact congrFun hW

/-- Helper toward Proposition 3.9: a null-measurable code predicate has
a Borel geometric factor with the complete predicate preserved a.e. -/
theorem uibotRecovery_nullMeasurable_predicate_factorization
    (Q : (ℤ → Fin 3) → Prop)
    (hQ : NullMeasurableSet {W | Q W} wholePlaneIIDCodeMeasure) :
    ∃ P : D39GeomRootedMapClass.{0} → Prop, MeasurableSet {x | P x} ∧
      ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        Q W ↔ P (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W) := by
  let S := toMeasurable wholePlaneIIDCodeMeasure {W | Q W}
  refine ⟨fun x => uibotRecoveredCode x ∈ S,
    (measurableSet_toMeasurable _ _).preimage measurable_uibotRecoveredCode, ?_⟩
  filter_upwards [uibotRecoveredCode_ae, hQ.toMeasurable_ae_eq] with W hW hQW
  rw [hW]
  exact hQW.symm.to_iff

section LocalLimit

variable (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
  (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
  (hsize : ∀ k, 1 ≤ ns k)
  (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k)))

/-- Helper toward Proposition 3.9: the recovered code under the existing
geometric local-limit law has exactly the original iid law. -/
theorem uibotRecoveredCode_localLimit_law :
    (uibotGeometricLocalLimitProbabilityLaw uibotDeterministicComparison_proved
      ℓ ρ hℓ hρ ns hns hsize hne : Measure D39GeomRootedMapClass.{0}).map
        uibotRecoveredCode = wholePlaneIIDCodeMeasure := by
  rw [uibotGeometricLocalLimitProbabilityLaw_map _ _ _ _ _ _ _ _ _
    uibotRecoveredCode measurable_uibotRecoveredCode]
  exact (Measure.map_congr uibotRecoveredCode_ae).trans Measure.map_id

/-- Helper toward Proposition 3.9: Borel recovery preserves the full
joint law of any a.e. measurable observable, not only scalar marginals. -/
theorem uibotRecoveredObservable_localLimit_law {α : Type*} [MeasurableSpace α]
    (X : (ℤ → Fin 3) → α) (hX : AEMeasurable X wholePlaneIIDCodeMeasure) :
    (uibotGeometricLocalLimitProbabilityLaw uibotDeterministicComparison_proved
      ℓ ρ hℓ hρ ns hns hsize hne : Measure D39GeomRootedMapClass.{0}).map
        (uibotRecoveredObservable X hX) = wholePlaneIIDCodeMeasure.map X := by
  rw [uibotGeometricLocalLimitProbabilityLaw_map _ _ _ _ _ _ _ _ _
    _ (measurable_uibotRecoveredObservable X hX)]
  exact Measure.map_congr (uibotRecoveredObservable_ae X hX).symm

/-- Helper toward Proposition 3.9: arbitrary complete code predicates
transport as a.e. statements through recovery. No measurability premise is
needed for this equivalence of a.e. assertions; it does not assert Borelness. -/
theorem uibotRecoveredCode_localLimit_ae_iff (Q : (ℤ → Fin 3) → Prop) :
    (∀ᵐ x ∂(uibotGeometricLocalLimitProbabilityLaw uibotDeterministicComparison_proved
      ℓ ρ hℓ hρ ns hns hsize hne : Measure D39GeomRootedMapClass.{0}),
      Q (uibotRecoveredCode x)) ↔ ∀ᵐ W ∂wholePlaneIIDCodeMeasure, Q W := by
  constructor
  · intro h
    rw [uibotGeometricLocalLimitProbabilityLaw_toMeasure_eq] at h
    have hp := ae_of_ae_map
      (measurable_uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved).aemeasurable h
    filter_upwards [hp, uibotRecoveredCode_ae] with W hW heq
    exact heq ▸ hW
  · intro h
    rw [← uibotRecoveredCode_localLimit_law ℓ ρ hℓ hρ ns hns hsize hne] at h
    exact ae_of_ae_map measurable_uibotRecoveredCode.aemeasurable h

end LocalLimit
end DirectedDistances.PaperProofs.Section3
end
